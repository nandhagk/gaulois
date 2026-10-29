open Core

module Audit = struct
  type t =
    | Hygiene
    | Layout
    | Claims
  [@@deriving enumerate, sexp_of, string ~capitalize:"kebab-case"]
end

module Diagnostic = struct
  type t =
    { file : Filename.t
    ; line : int
    ; claim : string option
    ; problem : string
    }
  [@@deriving sexp_of]

  let error ~file ~line ?claim problem =
    Or_error.error_s [%sexp ({ file; line; claim; problem } : t)]
  ;;
end

module Lex = struct
  module Token = struct
    type t =
      { text : string
      ; line : int
      }
    [@@deriving sexp_of]
  end

  module Sentence = struct
    type t =
      { tokens : Token.t list
      ; line : int
      }
    [@@deriving sexp_of]
  end

  let is_identifier c =
    Char.is_alphanum c || Char.equal c '_' || Char.equal c '\'' || Char.to_int c >= 128
  ;;

  let text ({ text; _ } : Token.t) = text

  (* Accumulators keep lexing linear; comments and strings never contribute identifier tokens. *)
  let scan ~file source =
    let length = String.length source in
    let at i c = i < length && Char.equal source.[i] c in
    let pair i a b = at i a && at (i + 1) b in
    let rec identifier_end i =
      if i < length && is_identifier source.[i] then identifier_end (i + 1) else i
    in
    let rec comment i line depth =
      if i >= length
      then Diagnostic.error ~file ~line "unterminated Rocq comment"
      else if pair i '(' '*'
      then comment (i + 2) line (depth + 1)
      else if pair i '*' ')'
      then if depth = 1 then Ok (i + 2, line) else comment (i + 2) line (depth - 1)
      else if at i '"'
      then (
        let%bind.Or_error next, next_line = quoted (i + 1) line in
        comment next next_line depth)
      else comment (i + 1) (line + if at i '\n' then 1 else 0) depth
    and quoted i line =
      if i >= length
      then Diagnostic.error ~file ~line "unterminated Rocq string"
      else if pair i '"' '"'
      then quoted (i + 2) line
      else if at i '"'
      then Ok (i + 1, line)
      else quoted (i + 1) (line + if at i '\n' then 1 else 0)
    in
    let rec loop i line tokens sentences =
      if i >= length
      then
        if List.is_empty tokens
        then Ok (List.rev sentences)
        else Diagnostic.error ~file ~line "incomplete Rocq sentence (missing final period)"
      else if pair i '(' '*'
      then (
        let%bind.Or_error i, line = comment (i + 2) line 1 in
        loop i line tokens sentences)
      else if at i '"'
      then (
        let%bind.Or_error next, next_line = quoted (i + 1) line in
        loop next next_line (({ text = "<string>"; line } : Token.t) :: tokens) sentences)
      else if Char.is_whitespace source.[i]
      then loop (i + 1) (line + if at i '\n' then 1 else 0) tokens sentences
      else if
        at i '.' && (i + 1 = length || Char.is_whitespace source.[i + 1] || pair (i + 1) '(' '*')
      then (
        let tokens = List.rev tokens in
        let sentence_line =
          match tokens with
          | [] -> line
          | first :: _ -> first.line
        in
        loop (i + 1) line [] (({ tokens; line = sentence_line } : Sentence.t) :: sentences))
      else (
        let next = if is_identifier source.[i] then identifier_end (i + 1) else i + 1 in
        let token = ({ text = String.sub source ~pos:i ~len:(next - i); line } : Token.t) in
        loop next line (token :: tokens) sentences)
    in
    loop 0 1 [] []
  ;;

  let rec head = function
    | "#" :: "[" :: rest -> attributes rest
    | ("Local" | "Global" | "Polymorphic" | "Monomorphic" | "Program" | "Time" | "Fail" | "Succeed")
      :: rest -> head rest
    | "Timeout" :: _seconds :: rest -> head rest
    | "Redirect" :: "<string>" :: rest -> head rest
    | tokens -> tokens

  and attributes = function
    | [] -> []
    | "]" :: rest -> head rest
    | _ :: rest -> attributes rest
  ;;

  let words ({ tokens; _ } : Sentence.t) = List.map tokens ~f:text
end

module Source = struct
  module Root = struct
    type t =
      | Theories
      | Examples
      | Tests
    [@@deriving enumerate, equal, string ~capitalize:"kebab-case", sexp_of]
  end

  type t =
    { file : Filename.t
    ; root : Root.t
    ; package : string
    ; source : string
    ; sentences : Lex.Sentence.t list
    }
  [@@deriving sexp_of]

  let extension = ".v"
  let float_package = "Float"
  let rewrite_package = "Rewrite"
  let examples_package = "Examples"

  let packages =
    String.Set.of_list
      [ "Collections"
      ; "Order"
      ; "Graph"
      ; "Fixpoint"
      ; "Rules"
      ; rewrite_package
      ; "Bits"
      ; "Domains"
      ; "Views"
      ; "Analyses"
      ; float_package
      ]
  ;;

  let example_directories = String.Set.of_list [ "While"; "Ssa" ]

  let package ~root relative =
    match root, String.split relative ~on:'/' with
    | Root.Examples, directory :: _ :: _ when Set.mem example_directories directory ->
      examples_package
    | (Root.Theories | Root.Tests), package :: _ :: _ -> package
    | Root.Examples, _ | (Root.Theories | Root.Tests), _ -> ""
  ;;

  let load ~root ~file ~package =
    let%bind.Or_error source = Or_error.try_with (fun () -> In_channel.read_all file) in
    let%map.Or_error sentences = Lex.scan ~file source in
    ({ file; root; package; source; sentences } : t)
  ;;

  let rec files directory =
    let%bind.Or_error entries = Or_error.try_with (fun () -> Sys_unix.ls_dir directory) in
    List.map entries ~f:(fun entry ->
      let file = Filename.concat directory entry in
      let%bind.Or_error ({ st_kind; _ } : Core_unix.stats) =
        Or_error.try_with (fun () -> Core_unix.lstat file)
      in
      match st_kind with
      | S_DIR -> files file
      | S_REG -> Ok (if String.is_suffix file ~suffix:extension then [ file ] else [])
      | S_LNK -> Diagnostic.error ~file ~line:1 "symlinks are not authored source paths"
      | S_CHR | S_BLK | S_FIFO | S_SOCK ->
        Diagnostic.error ~file ~line:1 "unexpected source file kind")
    |> Or_error.combine_errors
    |> Or_error.map ~f:List.concat
  ;;

  let discover repository =
    List.map Root.all ~f:(fun root ->
      let directory = Filename.concat repository (Root.to_string root) in
      let%bind.Or_error paths = files directory in
      List.map (List.sort paths ~compare:String.compare) ~f:(fun file ->
        let relative = String.chop_prefix_exn file ~prefix:[%string "%{directory}/"] in
        let package = package ~root relative in
        load ~root ~file ~package)
      |> Or_error.combine_errors)
    |> Or_error.combine_errors
    |> Or_error.map ~f:List.concat
  ;;

  let is_float ({ root; package; _ } : t) =
    Root.equal root Theories && String.equal package float_package
  ;;

  let is_production ({ root; _ } : t) =
    match root with
    | Theories | Examples -> true
    | Tests -> false
  ;;
end

module Scope = struct
  type t =
    | Section of string
    | Module of string
    | Signature of string

  module Assignment = struct
    type t =
      | Body
      | Constraint
  end

  let assignment depth words =
    (* A module-type refinement contains := without closing the module's declaration. *)
    let rec loop depth (state : Assignment.t) = function
      | "(" :: rest -> loop (depth + 1) state rest
      | ")" :: rest -> loop (depth - 1) state rest
      | "with" :: rest when depth = 0 -> loop depth Constraint rest
      | ":" :: "=" :: rest when depth = 0 ->
        (match state with
         | Constraint -> loop depth Body rest
         | Body -> true)
      | _ :: rest -> loop depth state rest
      | [] -> false
    in
    loop depth Body words
  ;;

  let advance ~file ~line scopes = function
    | "Section" :: name :: _ -> Ok (Section name :: scopes)
    | "Module" :: "Type" :: name :: rest ->
      Ok (if assignment 0 rest then scopes else Signature name :: scopes)
    | "Module" :: ("Import" | "Export") :: name :: rest | "Module" :: name :: rest ->
      Ok (if assignment 0 rest then scopes else Module name :: scopes)
    | "End" :: name :: _ ->
      (match scopes with
       | (Section opened | Module opened | Signature opened) :: rest when String.equal opened name
         -> Ok rest
       | (Section _ | Module _ | Signature _) :: _ | [] ->
         Diagnostic.error ~file ~line "unbalanced Module/Section scope during source audit")
    | _ -> Ok scopes
  ;;

  let inside_section scopes =
    List.exists scopes ~f:(function
      | Section _ -> true
      | Module _ | Signature _ -> false)
  ;;

  let inside_signature scopes =
    List.exists scopes ~f:(function
      | Signature _ -> true
      | Section _ | Module _ -> false)
  ;;
end

module Import_policy = struct
  type t =
    { known : String.Set.t
    ; forbidden : String.Set.t
    }

  let empty = ({ known = String.Set.empty; forbidden = String.Set.empty } : t)
  let stdlib = "Stdlib"
  let stdlib_prefix = [%string "%{stdlib}."]

  let paths tokens =
    let identifier word =
      (not (String.is_empty word)) && String.for_all word ~f:Lex.is_identifier
    in
    let rec loop current paths = function
      | "(" :: rest ->
        let%bind.Or_error rest = mask 1 rest in
        loop current paths rest
      | "." :: name :: rest when identifier name && not (List.is_empty current) ->
        loop (name :: current) paths rest
      | name :: rest when identifier name ->
        let paths =
          if List.is_empty current
          then paths
          else String.concat ~sep:"." (List.rev current) :: paths
        in
        loop [ name ] paths rest
      | [] ->
        Ok
          (List.rev
             (if List.is_empty current
              then paths
              else String.concat ~sep:"." (List.rev current) :: paths))
      | tokens -> Or_error.error_s [%message "unrecognized Require path" (tokens : string list)]
    and mask depth = function
      | "(" :: rest -> mask (depth + 1) rest
      | ")" :: rest -> if depth = 1 then Ok rest else mask (depth - 1) rest
      | _ :: rest -> mask depth rest
      | [] -> Or_error.error_string "unclosed Require import mask"
    in
    loop [] [] tokens
  ;;

  let modules = function
    | ("Import" | "Export") :: rest -> paths rest
    | words -> paths words
  ;;

  let imports = function
    | "From" :: rest ->
      let prefix, require =
        List.split_while rest ~f:(fun word -> not (String.equal word "Require"))
      in
      let%bind.Or_error prefix = paths prefix in
      (match prefix, require with
       | [ prefix ], "Require" :: rest ->
         let%map.Or_error names = modules rest in
         List.map names ~f:(fun name -> [%string "%{prefix}.%{name}"])
       | _ -> Or_error.error_string "unrecognized From/Require command")
    | "Require" :: rest -> modules rest
    | _ -> Ok []
  ;;

  module Node = struct
    type t =
      { name : string
      ; imports : string list
      ; postulates : String.Set.t
      }
  end

  module Scan = struct
    type t =
      { scopes : Scope.t list
      ; imports : string list
      ; postulates : String.Set.t
      }
  end

  let postulate scopes words =
    (* Abstract signature fields describe module arguments, rather than global axioms. *)
    (not (Scope.inside_signature scopes))
    &&
    match words with
    | ( "Axiom"
      | "Axioms"
      | "Parameter"
      | "Parameters"
      | "Conjecture"
      | "Conjectures"
      | "Admitted"
      | "Admit" )
      :: _
    | "Declare" :: ("Module" | "Instance") :: _ -> true
    | ("Variable" | "Variables" | "Hypothesis" | "Hypotheses" | "Context") :: _ ->
      not (Scope.inside_section scopes)
    | _ -> false
  ;;

  let node ~directory file =
    let relative =
      String.chop_prefix_exn file ~prefix:[%string "%{directory}/"] |> Filename.chop_extension
    in
    let name = String.concat ~sep:"." (stdlib :: String.split relative ~on:'/') in
    let%bind.Or_error source = Or_error.try_with (fun () -> In_channel.read_all file) in
    let%bind.Or_error sentences = Lex.scan ~file source in
    let%bind.Or_error ({ scopes; imports; postulates } : Scan.t) =
      List.fold_result
        sentences
        ~init:({ scopes = []; imports = []; postulates = String.Set.empty } : Scan.t)
        ~f:
          (fun
            ({ scopes; imports = previous; postulates } : Scan.t)
            ({ line; _ } as sentence : Lex.Sentence.t) ->
          let words = Lex.head (Lex.words sentence) in
          let%bind.Or_error imported = imports words in
          let postulates = if postulate scopes words then Set.add postulates name else postulates in
          let%map.Or_error scopes = Scope.advance ~file ~line scopes words in
          ({ scopes; imports = List.rev_append imported previous; postulates } : Scan.t))
    in
    if List.is_empty scopes
    then Ok ({ name; imports; postulates } : Node.t)
    else Diagnostic.error ~file ~line:1 "unclosed scope while indexing pinned Stdlib"
  ;;

  let suffixes name =
    let rec loop = function
      | [] -> []
      | _ :: rest as parts -> String.concat ~sep:"." parts :: loop rest
    in
    loop (String.split name ~on:'.')
  ;;

  let index nodes =
    let known = List.map nodes ~f:(fun ({ name; _ } : Node.t) -> name) |> String.Set.of_list in
    let aliases =
      Set.to_list known
      |> List.concat_map ~f:(fun name ->
        let relative = String.chop_prefix_exn name ~prefix:stdlib_prefix in
        let paths =
          suffixes relative
          |> List.concat_map ~f:(fun suffix -> [ suffix; [%string "%{stdlib_prefix}%{suffix}"] ])
        in
        List.map paths ~f:(fun suffix -> suffix, name))
      |> String.Map.of_alist_multi
    in
    let reverse =
      List.fold nodes ~init:String.Map.empty ~f:(fun reverse ({ name; imports; _ } : Node.t) ->
        List.concat_map imports ~f:(fun imported ->
          Map.find aliases imported |> Option.value ~default:[])
        |> List.fold ~init:reverse ~f:(fun reverse dependency ->
          Map.update reverse dependency ~f:(fun previous ->
            Set.add (Option.value previous ~default:String.Set.empty) name)))
    in
    let roots =
      List.fold nodes ~init:String.Set.empty ~f:(fun roots ({ postulates; _ } : Node.t) ->
        Set.union roots postulates)
    in
    let rec propagate pending seen =
      match pending with
      | [] -> seen
      | name :: rest when Set.mem seen name -> propagate rest seen
      | name :: rest ->
        let clients =
          Map.find reverse name |> Option.value ~default:String.Set.empty |> Set.to_list
        in
        propagate (List.rev_append clients rest) (Set.add seen name)
    in
    let forbidden = propagate (Set.to_list roots) String.Set.empty in
    let known =
      Map.key_set aliases |> Set.filter ~f:(fun name -> String.is_prefix name ~prefix:stdlib_prefix)
    in
    let forbidden =
      Map.fold aliases ~init:String.Set.empty ~f:(fun ~key ~data names ->
        if List.exists data ~f:(Set.mem forbidden) then Set.add names key else names)
    in
    ({ known; forbidden } : t)
  ;;

  let load () =
    let directory =
      Sys.getenv "ROCQPATH"
      |> Option.value ~default:""
      |> String.split ~on:':'
      |> List.find_map ~f:(fun root ->
        let directory = Filename.concat root stdlib in
        match Sys_unix.is_directory directory with
        | `Yes -> Some directory
        | `No | `Unknown -> None)
    in
    match directory with
    | None -> Or_error.error_string "pinned Stdlib source directory is unavailable through ROCQPATH"
    | Some directory ->
      let%bind.Or_error files = Source.files directory in
      let%map.Or_error nodes = List.map files ~f:(node ~directory) |> Or_error.combine_errors in
      index nodes
  ;;

  let for_sources sources =
    let needs_index sentence =
      match Lex.head (Lex.words sentence) with
      | "From" :: origin :: _ -> String.equal origin stdlib
      | "Require" :: rest -> List.mem rest stdlib ~equal:String.equal
      | _ -> false
    in
    if
      List.exists sources ~f:(fun ({ sentences; _ } : Source.t) ->
        List.exists sentences ~f:needs_index)
    then load ()
    else Ok empty
  ;;
end

module Hygiene = struct
  let forbidden =
    String.Set.of_list
      [ "Admitted"
      ; "admit"
      ; "give_up"
      ; "Axiom"
      ; "Axioms"
      ; "Parameter"
      ; "Parameters"
      ; "Conjecture"
      ; "Conjectures"
      ]
  ;;

  let queries =
    String.Set.of_list
      [ "Print"
      ; "Check"
      ; "Compute"
      ; "Eval"
      ; "About"
      ; "Locate"
      ; "Search"
      ; "SearchPattern"
      ; "SearchRewrite"
      ]
  ;;

  let local_instance words =
    let rec prefix local = function
      | "Local" :: rest -> prefix true rest
      | "Global" :: rest -> prefix false rest
      | "#" :: "[" :: rest -> attribute local rest
      | ("Polymorphic" | "Monomorphic" | "Program" | "Time") :: rest -> prefix local rest
      | _ -> local
    and attribute local = function
      | "]" :: rest -> prefix local rest
      | "local" :: rest -> attribute true rest
      | ("global" | "export") :: rest -> attribute false rest
      | _ :: rest -> attribute local rest
      | [] -> false
    in
    prefix false words
  ;;

  let import_problem ({ known; forbidden } : Import_policy.t) source name =
    if String.is_prefix name ~prefix:Import_policy.stdlib_prefix
    then
      if not (Set.mem known name)
      then Some [%string "unknown pinned Stdlib module: %{name}"]
      else if Set.mem forbidden name && not (Source.is_float source)
      then Some [%string "axiom-bearing Stdlib import outside Float: %{name}"]
      else None
    else if String.is_prefix name ~prefix:"Gaulois."
    then
      if
        String.is_prefix name ~prefix:"Gaulois.Float."
        && Source.is_production source
        && not (Source.is_float source)
      then Some "only Gaulois.Float may depend on Float"
      else None
    else if String.is_prefix name ~prefix:"Flocq." && Source.is_float source
    then None
    else Some "dependency outside Stdlib/Gaulois (Flocq is Float-only)"
  ;;

  let record_problem words =
    let problem = "record carrier Type field; parameterize the dictionary instead" in
    let rec carrier = function
      | "(" :: rest -> carrier rest
      | "Type" :: _ -> Some problem
      | _ -> None
    in
    let field tokens =
      match List.rev tokens with
      | _name :: ":" :: rest -> carrier rest
      | _ -> None
    in
    let rec fields depth tokens = function
      | (";" | "}") :: rest when depth = 0 ->
        Option.first_some (field tokens) (fields depth [] rest)
      | (("(" | "{" | "[") as token) :: rest -> fields (depth + 1) (token :: tokens) rest
      | ((")" | "}" | "]") as token) :: rest -> fields (depth - 1) (token :: tokens) rest
      | token :: rest -> fields depth (token :: tokens) rest
      | [] -> field tokens
    in
    let rec record_body = function
      | "{" :: rest -> fields 0 [] rest
      | _ :: rest -> record_body rest
      | [] -> None
    in
    let rec body = function
      | ":" :: "=" :: rest -> record_body rest
      | _ :: rest -> body rest
      | [] -> None
    in
    match words with
    | ("Record" | "Structure" | "Class") :: rest -> body rest
    | _ -> None
  ;;

  let kernel_problem = function
    | "Set" :: "Nested" :: "Proofs" :: "Allowed" :: _ ->
      Some "nested proofs prevent unambiguous theorem completion tracking"
    | ("Reset" | "Back" | "BackTo") :: _ ->
      Some "proof editing command can remove discovered declarations"
    | "Unset" :: ("Guard" | "Positivity" | "Universe") :: "Checking" :: _ ->
      Some "disabled kernel checking"
    | "Unset" :: "Rocqtop" :: "Exit" :: "On" :: "Error" :: _ ->
      Some "disabled strict Rocq query failures"
    | "Load" :: _ | "Declare" :: "ML" :: _ ->
      Some "external source or native plugin bypasses the authored source audit"
    | _ -> None
  ;;

  let kernel_safety (source : Source.t) =
    List.map source.sentences ~f:(fun ({ line; _ } as sentence : Lex.Sentence.t) ->
      match kernel_problem (Lex.head (Lex.words sentence)) with
      | None -> Ok ()
      | Some problem -> Diagnostic.error ~file:source.file ~line problem)
    |> Or_error.combine_errors_unit
  ;;

  let sentence ~policy (source : Source.t) ({ tokens; line } as sentence : Lex.Sentence.t) =
    let words = Lex.words sentence in
    let head = Lex.head words in
    let%bind.Or_error imports =
      Import_policy.imports head
      |> Or_error.tag_s ~tag:[%message "source imports" (source.file : Filename.t) (line : int)]
    in
    let problem =
      match List.find tokens ~f:(fun ({ text; _ } : Lex.Token.t) -> Set.mem forbidden text) with
      | Some ({ text; _ } : Lex.Token.t) ->
        Some [%string "forbidden proof escape or declaration: %{text}"]
      | None ->
        (match head with
         | ("Instance" :: _ | "Existing" :: "Instance" :: _ | "Existing" :: "Instances" :: _)
           when not (local_instance words) -> Some "global instance; dictionaries must be explicit"
         | "Declare" :: "Instance" :: _ -> Some "instance declaration introduces an axiom"
         | "Admit" :: _ -> Some "admitted Program obligation"
         | first :: _
           when Source.is_production source
                && (String.is_prefix first ~prefix:"Extract"
                    || Set.mem queries first
                    || (String.equal first "Recursive"
                        && List.mem head "Extraction" ~equal:String.equal)
                    || (String.equal first "Separate"
                        && List.mem head "Extraction" ~equal:String.equal)) ->
           Some "theory extraction or query command belongs in a client or scratch file"
         | _ ->
           Option.first_some
             (kernel_problem head)
             (Option.first_some
                (List.find_map imports ~f:(import_problem policy source))
                (record_problem head)))
    in
    match problem with
    | None -> Ok ()
    | Some problem -> Diagnostic.error ~file:source.file ~line problem
  ;;

  let source ~policy (source : Source.t) =
    let%bind.Or_error scopes =
      List.fold_result
        source.sentences
        ~init:[]
        ~f:(fun scopes ({ line; _ } as current : Lex.Sentence.t) ->
          let head = Lex.head (Lex.words current) in
          let%bind.Or_error () =
            match head with
            | ("Variable" | "Variables" | "Hypothesis" | "Hypotheses" | "Context") :: _
              when not (Scope.inside_section scopes) ->
              Diagnostic.error
                ~file:source.file
                ~line
                "global assumption; bind it in a Section or a theorem instead"
            | _ -> Ok ()
          in
          let%bind.Or_error () = sentence ~policy source current in
          Scope.advance ~file:source.file ~line scopes head)
    in
    if List.is_empty scopes
    then Ok ()
    else
      Diagnostic.error ~file:source.file ~line:1 "unclosed Module/Section scope during source audit"
  ;;

  let run sources =
    let%bind.Or_error policy = Import_policy.for_sources sources in
    List.map sources ~f:(source ~policy) |> Or_error.combine_errors_unit
  ;;
end

module Layout = struct
  let source ({ file; root; package; _ } : Source.t) =
    let allowed =
      match root with
      | Theories -> Source.packages
      | Tests -> Set.add Source.packages Source.examples_package
      | Examples -> String.Set.singleton Source.examples_package
    in
    if not (Set.mem allowed package)
    then Diagnostic.error ~file ~line:1 "source must be placed under its declared package directory"
    else if not (String.is_prefix (Filename.basename file) ~prefix:package)
    then Diagnostic.error ~file ~line:1 [%string "Rocq basename must start with package %{package}"]
    else Ok ()
  ;;

  let run sources =
    let by_basename =
      List.map sources ~f:(fun ({ file; _ } : Source.t) -> Filename.basename file, file)
      |> String.Map.of_alist_multi
    in
    let duplicates =
      Map.fold by_basename ~init:[] ~f:(fun ~key:basename ~data:files errors ->
        match files with
        | [] | [ _ ] -> errors
        | _ ->
          Or_error.error_s
            [%message "duplicate Rocq basename" (basename : string) (files : Filename.t list)]
          :: errors)
    in
    Or_error.combine_errors_unit (List.map sources ~f:source @ duplicates)
  ;;
end

module Claim = struct
  type t =
    { name : string
    ; line : int
    }
  [@@deriving sexp_of]

  module Scan = struct
    type nonrec t =
      { scopes : Scope.t list
      ; claims : t list
      ; pending : t option
      }
  end

  let declaration ~file ~line ~scopes ~words name =
    if Scope.inside_signature scopes
    then
      Diagnostic.error
        ~file
        ~line
        ~claim:name
        "module signature theorem has no auditable implementation"
    else if
      List.mem
        (List.take_while words ~f:(fun word -> not (String.equal word "Theorem")))
        "Fail"
        ~equal:String.equal
    then
      Diagnostic.error
        ~file
        ~line
        ~claim:name
        "failed theorem command has no declaration to inspect"
    else (
      let modules =
        List.filter_map (List.rev scopes) ~f:(function
          | Scope.Module name -> Some name
          | Scope.Section _ | Scope.Signature _ -> None)
      in
      Ok ({ name = String.concat ~sep:"." (modules @ [ name ]); line } : t))
  ;;

  let step ~file ({ scopes; claims; pending } : Scan.t) ({ line; _ } as sentence : Lex.Sentence.t) =
    let original = Lex.words sentence in
    let words = Lex.head original in
    let%bind.Or_error scopes = Scope.advance ~file ~line scopes words in
    match words, pending with
    | "Abort" :: _, Some ({ name; _ } : t) ->
      Diagnostic.error ~file ~line ~claim:name "aborted theorem has no proof to inspect"
    | "Theorem" :: _ :: _, Some ({ name; _ } : t) ->
      Diagnostic.error ~file ~line ~claim:name "previous theorem proof is incomplete"
    | "Theorem" :: name :: _, None ->
      let%map.Or_error claim = declaration ~file ~line ~scopes ~words:original name in
      (* Theorem always opens a proof; := inside its statement may belong to a let expression. *)
      ({ scopes; claims = claim :: claims; pending = Some claim } : Scan.t)
    | ("Qed" | "Defined" | "Save") :: _, _ ->
      let attempted =
        List.mem
          (List.take_while original ~f:(fun word ->
             not (List.mem [ "Qed"; "Defined"; "Save" ] word ~equal:String.equal)))
          "Fail"
          ~equal:String.equal
      in
      Ok ({ scopes; claims; pending = (if attempted then pending else None) } : Scan.t)
    | _, _ -> Ok ({ scopes; claims; pending } : Scan.t)
  ;;

  let discover ({ file; sentences; _ } : Source.t) =
    let%bind.Or_error ({ scopes; claims; pending } : Scan.t) =
      List.fold_result
        sentences
        ~init:({ scopes = []; claims = []; pending = None } : Scan.t)
        ~f:(step ~file)
    in
    match pending with
    | Some ({ name; line } : t) ->
      Diagnostic.error ~file ~line ~claim:name "theorem proof is incomplete"
    | None ->
      if List.is_empty scopes
      then Ok (List.rev claims)
      else Diagnostic.error ~file ~line:1 "unclosed Module/Section scope during theorem discovery"
  ;;
end

module Query = struct
  module Mode = struct
    type t =
      | Repl
      | Compile
    [@@deriving string ~capitalize:"kebab-case"]

    let arguments = function
      | Repl -> [ "-batch" ]
      | Compile -> []
    ;;
  end

  let scratch = "/tmp/gaulois-TOOL-1"
  let marker = "__GAULOIS_AUDIT_"
  let namespace = "GauloisAuditSource"

  (* The fresh module and exact Locate identity prevent imported-name fallback. *)
  let qualified name = String.concat ~sep:"." [ namespace; name ]
  let closed = "Closed under the global context"
  let axioms = "Axioms:"

  let allowed_axioms =
    String.Set.of_list
      [ "Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec"
      ; "Stdlib.Reals.ClassicalDedekindReals.sig_not_dec"
      ; "Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep"
      ]
  ;;

  let preamble = "Set Rocqtop Exit On Error.\nUnset Nested Proofs Allowed.\n"
  let printing = "Set Printing All.\n"
  let null_device = "/dev/null"

  let rec remove_workspace directory =
    let children =
      let%bind.Or_error entries = Or_error.try_with (fun () -> Sys_unix.ls_dir directory) in
      List.map entries ~f:(fun entry ->
        let file = Filename.concat directory entry in
        let%bind.Or_error ({ st_kind; _ } : Core_unix.stats) =
          Or_error.try_with (fun () -> Core_unix.lstat file)
        in
        match st_kind with
        | S_DIR -> remove_workspace file
        | S_REG | S_LNK | S_CHR | S_BLK | S_FIFO | S_SOCK ->
          Or_error.try_with (fun () -> Core_unix.unlink file))
      |> Or_error.combine_errors_unit
    in
    let removal = Or_error.try_with (fun () -> Core_unix.rmdir directory) in
    Or_error.combine_errors_unit [ children; removal ]
  ;;

  let with_workspace ~f =
    let%bind.Or_error directory =
      Or_error.try_with (fun () ->
        Core_unix.mkdir_p scratch;
        Filename_unix.temp_dir ~in_dir:scratch "query-" "")
    in
    let operation = Or_error.try_with_join (fun () -> f directory) in
    let cleanup = remove_workspace directory in
    let%map.Or_error result, () = Or_error.both operation cleanup in
    result
  ;;

  let run_process ~mode ~directory ~args ~output =
    let%bind.Or_error status =
      Or_error.try_with
      @@ fun () ->
      Core_unix.with_file null_device ~mode:[ O_RDONLY ] ~f:(fun input ->
        Core_unix.with_file
          output
          ~perm:0o600
          ~mode:[ O_WRONLY; O_CREAT; O_TRUNC ]
          ~f:(fun output ->
            let ({ pid; _ } : (_, _, _) Core_unix.Pid_with_generated_fds.t) =
              Core_unix.create_process_with_fds
                ~working_dir:directory
                ~prog:"systemd-run"
                ~args:
                  ([ "--user"
                   ; "--scope"
                   ; "--quiet"
                   ; "--slice=gaulois.slice"
                   ; "-p"
                   ; "MemoryMax=2G"
                   ; "-p"
                   ; "MemorySwapMax=0"
                   ; "--"
                   ; "env"
                   ; "-u"
                   ; "COQPATH"
                   ; "rocq"
                   ; Mode.to_string mode
                   ; "-q"
                   ]
                   @ Mode.arguments mode
                   @ args)
                ~stdin:(Use_this input)
                ~stdout:(Use_this output)
                ~stderr:(Use_this output)
                ()
            in
            Core_unix.waitpid pid))
    in
    let%bind.Or_error transcript = Or_error.try_with (fun () -> In_channel.read_all output) in
    match status with
    | Ok () -> Ok transcript
    | Error _ ->
      Or_error.error_s
        [%message
          "Rocq assumptions query failed"
            (status : Core_unix.Exit_or_signal.t)
            (transcript : string)]
  ;;

  let load_paths repository =
    let candidate = Filename.concat repository "_build/default" in
    let build =
      match Sys_unix.is_directory candidate with
      | `Yes -> candidate
      | `No | `Unknown -> repository
    in
    let theories =
      Set.to_list Source.packages
      |> List.filter_map ~f:(fun package ->
        let directory = Filename.concat build [%string "theories/%{package}"] in
        if
          Sys_unix.is_directory directory
          |> function
          | `Yes -> true
          | `No | `Unknown -> false
        then Some [ "-Q"; directory; [%string "Gaulois.%{package}"] ]
        else None)
    in
    List.concat
      (theories
       @ [ [ "-Q"; Filename.concat build "examples"; "Gaulois.Examples" ]
         ; [ "-Q"; Filename.concat build "tests"; "Gaulois.Tests" ]
         ])
  ;;

  let delimiter index = [%string "%{marker}%{index#Int}__"]

  let mark index =
    let label = delimiter index in
    [%string "Goal True. Proof. idtac \"%{label}\". Abort.\n"]
  ;;

  let execute ~repository source commands =
    if String.is_substring source ~substring:marker
    then Or_error.error_string "reserved audit delimiter in source"
    else
      with_workspace ~f:(fun directory ->
        let input = Filename.concat directory "Query.v" in
        let script =
          String.concat
            [ preamble
            ; [%string "Module %{namespace}.\n"]
            ; source
            ; [%string "\nEnd %{namespace}.\n"]
            ; printing
            ; List.mapi commands ~f:(fun index command ->
                String.concat [ mark index; command; "\n" ])
              |> String.concat
            ; mark (List.length commands)
            ]
        in
        let%bind.Or_error () =
          Or_error.try_with (fun () -> Out_channel.write_all input ~data:script)
        in
        let output = Filename.concat directory "Query.log" in
        run_process ~mode:Repl ~directory ~args:(load_paths repository @ [ "-l"; input ]) ~output)
  ;;

  let blocks ~count transcript =
    let lines = String.split_lines transcript in
    let rec loop index lines blocks =
      if index = count
      then
        if List.exists lines ~f:(fun line -> not (String.is_empty (String.strip line)))
        then Or_error.error_string "unexpected trailing assumptions query output"
        else Ok (List.rev blocks)
      else (
        let label = delimiter (index + 1) in
        let block, rest = List.split_while lines ~f:(fun line -> not (String.equal line label)) in
        match rest with
        | [] -> Or_error.error_s [%message "incomplete assumptions query" (index : int)]
        | _ :: rest -> loop (index + 1) rest (block :: blocks))
    in
    let _, remaining =
      List.split_while lines ~f:(fun line -> not (String.equal line (delimiter 0)))
    in
    match remaining with
    | [] -> Or_error.error_string "missing assumptions query delimiter"
    | _ :: rest -> loop 0 rest []
  ;;

  let assumption_names lines =
    match List.filter lines ~f:(fun line -> not (String.is_empty (String.strip line))) with
    | [ line ] when String.equal line closed -> Ok []
    | header :: rest when String.equal header axioms ->
      let names =
        List.filter_map rest ~f:(fun line ->
          if Char.is_whitespace line.[0]
          then None
          else
            Some
              (String.lsplit2 line ~on:':' |> Option.value_map ~default:line ~f:fst |> String.strip))
      in
      if
        List.is_empty names
        || List.exists names ~f:(fun name ->
          String.is_empty name
          || not (String.for_all name ~f:(fun c -> Lex.is_identifier c || Char.equal c '.')))
      then Or_error.error_s [%message "unrecognized axiom report" (lines : string list)]
      else Ok names
    | _ ->
      Or_error.error_s [%message "missing or unrecognized assumptions report" (lines : string list)]
  ;;

  let claim_report ~name = function
    | identity :: report when String.equal identity [%string "Constant Top.%{qualified name}"] ->
      assumption_names report
    | lines ->
      Or_error.error_s
        [%message
          "claim does not resolve to the source declaration" (name : string) (lines : string list)]
  ;;

  let resolve lines =
    match lines with
    | [ line ] ->
      (match String.chop_prefix line ~prefix:"Constant " with
       | Some name when Set.mem allowed_axioms name -> Ok ()
       | Some name -> Or_error.error_s [%message "unexpected Float axiom" (name : string)]
       | None -> Or_error.error_s [%message "unrecognized axiom identity" (line : string)])
    | _ -> Or_error.error_s [%message "ambiguous axiom identity" (lines : string list)]
  ;;
end

module Claims = struct
  module Report = struct
    type t =
      { claim : Claim.t
      ; assumptions : string list
      }
  end

  let check_names (source : Source.t) (claim : Claim.t) names =
    if List.is_empty names || Source.is_float source
    then Ok ()
    else
      Diagnostic.error
        ~file:source.file
        ~line:claim.line
        ~claim:claim.name
        [%string "theorem depends on axioms: %{String.concat ~sep:\", \" names}"]
  ;;

  let inspect (source : Source.t) ~claims ~transcript =
    let%bind.Or_error blocks =
      Query.blocks ~count:(List.length claims) transcript
      |> Or_error.tag_s
           ~tag:
             [%message
               "incomplete source inspection" (source.file : Filename.t) (claims : Claim.t list)]
    in
    List.map2_exn claims blocks ~f:(fun claim block ->
      let%bind.Or_error assumptions =
        Query.claim_report ~name:claim.name block
        |> Or_error.tag_s
             ~tag:
               [%message "incomplete claim inspection" (source.file : Filename.t) (claim : Claim.t)]
      in
      let%map.Or_error () = check_names source claim assumptions in
      ({ claim; assumptions } : Report.t))
    |> Or_error.combine_errors
  ;;

  let validate_float (source : Source.t) ~reports ~axioms ~transcript =
    let%bind.Or_error blocks = Query.blocks ~count:(List.length axioms) transcript in
    let resolutions =
      List.map2_exn axioms blocks ~f:(fun axiom block -> axiom, Query.resolve block)
      |> String.Map.of_alist_exn
    in
    List.concat_map reports ~f:(fun ({ claim; assumptions } : Report.t) ->
      List.map assumptions ~f:(fun axiom ->
        Map.find resolutions axiom
        |> Option.value
             ~default:(Or_error.error_s [%message "missing axiom resolution" (axiom : string)])
        |> Or_error.tag_s
             ~tag:[%message "Float theorem assumption" (source.file : Filename.t) (claim : Claim.t)]))
    |> Or_error.combine_errors_unit
  ;;

  let source ~repository (source : Source.t) =
    let%bind.Or_error () = Hygiene.kernel_safety source in
    let%bind.Or_error claims = Claim.discover source in
    if List.is_empty claims
    then Ok ()
    else (
      let commands =
        List.map claims ~f:(fun ({ name; _ } : Claim.t) ->
          let name = Query.qualified name in
          [%string "Locate %{name}.\nPrint Assumptions %{name}."])
      in
      let%bind.Or_error transcript =
        Query.execute ~repository source.source commands
        |> Or_error.tag_s
             ~tag:
               [%message
                 "cannot inspect source claims" (source.file : Filename.t) (claims : Claim.t list)]
      in
      let%bind.Or_error reports = inspect source ~claims ~transcript in
      let axioms =
        List.concat_map reports ~f:(fun ({ assumptions; _ } : Report.t) -> assumptions)
        |> String.Set.of_list
        |> Set.to_list
      in
      if List.is_empty axioms
      then Ok ()
      else (
        let commands = List.map axioms ~f:(fun name -> [%string "Locate %{name}."]) in
        let result =
          let%bind.Or_error transcript = Query.execute ~repository source.source commands in
          validate_float source ~reports ~axioms ~transcript
        in
        Or_error.tag_s
          result
          ~tag:
            [%message
              "Float assumptions inspection" (source.file : Filename.t) (claims : Claim.t list)]))
  ;;

  let run ~repository sources =
    List.map sources ~f:(source ~repository) |> Or_error.combine_errors_unit
  ;;
end

let run ~repository audits =
  let%bind.Or_error repository = Or_error.try_with (fun () -> Filename_unix.realpath repository) in
  let%bind.Or_error sources = Source.discover repository in
  List.map audits ~f:(fun (audit : Audit.t) ->
    match audit with
    | Hygiene -> Hygiene.run sources
    | Layout -> Layout.run sources
    | Claims -> Claims.run ~repository sources)
  |> Or_error.combine_errors_unit
;;

let check_command audits =
  Command.basic_or_error
    ~summary:"Audit authored Rocq sources and kernel-reported theorem assumptions"
    (let%map_open.Command repository =
       flag "root" (optional_with_default "." string) ~doc:"DIRECTORY repository root"
     in
     fun () -> run ~repository audits)
;;

let command =
  Command.group
    ~summary:"Check source hygiene, layout and theorem assumptions"
    ~preserve_subcommand_order:()
    ~body:(fun ~path:_ ->
      match run ~repository:"." Audit.all with
      | Ok () -> ()
      | Error error ->
        eprint_s [%sexp (error : Error.t)];
        exit 1)
    (List.map Audit.all ~f:(fun audit -> Audit.to_string audit, check_command [ audit ]))
;;

module Fixture = struct
  let file = "theories/Collections/CollectionsFixture.v"
  let closed = "Theorem closed : True. Proof. exact I. Qed."

  let classical =
    "From Stdlib.Logic Require Import Classical_Prop. Theorem classical_claim : forall P, P \\/ ~ \
     P. Proof. exact classic. Qed."
  ;;

  let reals =
    "From Stdlib.Reals Require Import Reals. Theorem real_claim : forall x y, Rplus x y = Rplus y \
     x. Proof. exact Rplus_comm. Qed."
  ;;

  let repository = Query.scratch
  let while_file = "While/ExamplesWhileFixture.v"
  let ssa_file = "Ssa/ExamplesSsaFixture.v"
  let examples_test_file = "Examples/ExamplesTestFixture.v"

  module Path = struct
    type t =
      { root : Source.Root.t
      ; relative : Filename.t
      }
  end

  let example_paths =
    [ ({ root = Examples; relative = while_file } : Path.t)
    ; ({ root = Examples; relative = ssa_file } : Path.t)
    ; ({ root = Tests; relative = examples_test_file } : Path.t)
    ]
  ;;

  let source ?(root = Source.Root.Theories) ?(package = "Collections") ?(file = file) source =
    let sentences = Lex.scan ~file source |> Or_error.ok_exn in
    ({ file; root; package; source; sentences } : Source.t)
  ;;

  let at ~root relative text =
    let file = Filename.concat (Source.Root.to_string root) relative in
    source ~root ~package:(Source.package ~root relative) ~file text
  ;;

  let examples text =
    List.map example_paths ~f:(fun ({ root; relative } : Path.t) -> at ~root relative text)
  ;;

  let with_repository ~f =
    Core_unix.mkdir_p Query.scratch;
    let directory = Filename_unix.temp_dir ~in_dir:Query.scratch "repository-" "" in
    let relative =
      [ file; "tests/Collections/CollectionsTestFixture.v" ]
      @ List.map example_paths ~f:(fun ({ root; relative } : Path.t) ->
        Filename.concat (Source.Root.to_string root) relative)
    in
    let files = List.map relative ~f:(Filename.concat directory) in
    Exn.protect
      ~f:(fun () ->
        List.iter files ~f:(fun file ->
          Core_unix.mkdir_p (Filename.dirname file);
          Out_channel.write_all file ~data:closed);
        f directory)
      ~finally:(fun () ->
        List.iter files ~f:Core_unix.unlink;
        List.map files ~f:Filename.dirname
        |> List.dedup_and_sort ~compare:String.compare
        |> List.iter ~f:Core_unix.rmdir;
        List.iter Source.Root.all ~f:(fun root ->
          Core_unix.rmdir (Filename.concat directory (Source.Root.to_string root)));
        Core_unix.rmdir directory)
  ;;
end

let%expect_test "clean source ignores nested comments and doubled quotes in strings" =
  let text =
    {|(* Axiom bad : False. (* Theorem ghost : False. Admitted. *) *)
Definition message := "Admitted. "" Axiom bad. (* not a comment *)".
Theorem valid : True. Proof. exact I. Qed.|}
  in
  let source = Fixture.source text in
  print_s [%sexp (Hygiene.run [ source ] : unit Or_error.t)];
  print_s [%sexp (Claim.discover source : Claim.t list Or_error.t)];
  [%expect
    {|
    (Ok ())
    (Ok (((name valid) (line 3))))
    |}]
;;

let%expect_test "proof escapes declarations and unsafe checking identify their file" =
  List.iter
    [ "Axiom bad : False."
    ; "Theorem bad : False. Proof. admit. Qed."
    ; "#[global] Instance bad : local."
    ; "Unset Guard Checking."
    ; "Extraction Language OCaml."
    ; "Print Assumptions valid."
    ; "From Flocq Require Import IEEE754.Binary."
    ; "Record dictionary := { carrier : Type }."
    ]
    ~f:(fun text -> print_s [%sexp (Hygiene.run [ Fixture.source text ] : unit Or_error.t)]);
  [%expect
    {|
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "forbidden proof escape or declaration: Axiom")))
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "forbidden proof escape or declaration: admit")))
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "global instance; dictionaries must be explicit")))
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "disabled kernel checking")))
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem
       "theory extraction or query command belongs in a client or scratch file")))
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem
       "theory extraction or query command belongs in a client or scratch file")))
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "dependency outside Stdlib/Gaulois (Flocq is Float-only)")))
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "record carrier Type field; parameterize the dictionary instead")))
    |}]
;;

let%expect_test "explicitly local instances are distinguished from an instance named local" =
  List.iter
    [ "Local Instance local_ok : True."
    ; "#[local] Instance attribute_ok : True."
    ; "Instance global_bad : local."
    ]
    ~f:(fun text -> print_s [%sexp (Hygiene.run [ Fixture.source text ] : unit Or_error.t)]);
  [%expect
    {|
    (Ok ())
    (Ok ())
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "global instance; dictionaries must be explicit")))
    |}]
;;

let%expect_test "malformed comments and strings fail discovery" =
  List.iter
    [ "(* unfinished"; "Definition x := \"unfinished"; "Theorem unfinished : True" ]
    ~f:(fun text ->
      print_s [%sexp (Lex.scan ~file:Fixture.file text : Lex.Sentence.t list Or_error.t)]);
  [%expect
    {|
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "unterminated Rocq comment")))
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "unterminated Rocq string")))
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "incomplete Rocq sentence (missing final period)")))
    |}]
;;

let%expect_test "layout checks duplicate names package prefixes and placement" =
  let clean = Fixture.source Fixture.closed in
  let duplicate =
    Fixture.source ~root:Tests ~file:"tests/Collections/CollectionsFixture.v" Fixture.closed
  in
  let wrong_prefix = Fixture.source ~file:"theories/Collections/Wrong.v" Fixture.closed in
  let wrong_package = Fixture.source ~package:"Unknown" Fixture.closed in
  print_s [%sexp (Layout.run [ clean ] : unit Or_error.t)];
  print_s [%sexp (Layout.run [ clean; duplicate ] : unit Or_error.t)];
  print_s [%sexp (Layout.run [ wrong_prefix; wrong_package ] : unit Or_error.t)];
  [%expect
    {|
    (Ok ())
    (Error
     ("duplicate Rocq basename" (basename CollectionsFixture.v)
      (files
       (theories/Collections/CollectionsFixture.v
        tests/Collections/CollectionsFixture.v))))
    (Error
     (((file theories/Collections/Wrong.v) (line 1) (claim ())
       (problem "Rocq basename must start with package Collections"))
      ((file theories/Collections/CollectionsFixture.v) (line 1) (claim ())
       (problem "source must be placed under its declared package directory"))))
    |}]
;;

let%expect_test "Rewrite theory and test files have valid package placement" =
  let sources =
    [ Fixture.source
        ~package:Source.rewrite_package
        ~file:"theories/Rewrite/RewriteSyntax.v"
        Fixture.closed
    ; Fixture.source
        ~root:Tests
        ~package:Source.rewrite_package
        ~file:"tests/Rewrite/RewriteSyntaxTest.v"
        Fixture.closed
    ]
  in
  print_s [%sexp (Layout.run sources : unit Or_error.t)];
  print_s [%sexp (Hygiene.run sources : unit Or_error.t)];
  [%expect
    {|
    (Ok ())
    (Ok ())
    |}]
;;

let%expect_test "Rewrite logical load path resolves a compiled theorem dependency" =
  let result =
    Query.with_workspace ~f:(fun repository ->
      let package = Source.rewrite_package in
      let directory = Filename.concat repository [%string "theories/%{package}"] in
      Core_unix.mkdir_p directory;
      let dependency = Filename.concat directory [%string "RewriteSyntax%{Source.extension}"] in
      Out_channel.write_all dependency ~data:Fixture.closed;
      let args = Query.load_paths repository in
      print_s
        [%sexp
          (List.map args ~f:(String.substr_replace_all ~pattern:repository ~with_:"<repository>")
           : string list)];
      let output = Filename.concat repository "Compile.log" in
      let%bind.Or_error _ =
        Query.run_process ~mode:Compile ~directory:repository ~args:(args @ [ dependency ]) ~output
      in
      let source =
        Fixture.source
          ~root:Tests
          ~package
          ~file:"tests/Rewrite/RewriteDependencyTest.v"
          {|From Gaulois.Rewrite Require Import RewriteSyntax.
Theorem dependency_closed : True.
Proof.
  exact closed.
Qed.|}
      in
      let%bind.Or_error () = Hygiene.run [ source ] in
      Claims.source ~repository source)
  in
  print_s [%sexp (result : unit Or_error.t)];
  [%expect
    {|
    (-Q <repository>/theories/Rewrite Gaulois.Rewrite -Q <repository>/examples
     Gaulois.Examples -Q <repository>/tests Gaulois.Tests)
    (Ok ())
    |}]
;;

let%expect_test "theorem discovery tracks modules and generalizes sections" =
  let source =
    Fixture.source
      {|Module Outer. Section Variables. Context (P : Prop) (p : P).
#[local] Theorem generalized : P. Proof. exact p. Qed. End Variables.
Module Inner. End Inner. Module Alias := Inner. End Outer.|}
  in
  print_s [%sexp (Claim.discover source : Claim.t list Or_error.t)];
  print_s [%sexp (Claims.source ~repository:Fixture.repository source : unit Or_error.t)];
  [%expect
    {|
    (Ok (((name Outer.generalized) (line 2))))
    (Ok ())
    |}]
;;

let%expect_test "every authored source root discovers and inspects its theorems" =
  let module Discovery = struct
    type t =
      { file : Filename.t
      ; root : Source.Root.t
      ; package : string
      ; claims : Claim.t list
      }
    [@@deriving sexp_of]
  end
  in
  Fixture.with_repository ~f:(fun repository ->
    let sources = Source.discover repository |> Or_error.ok_exn in
    List.iter sources ~f:(fun ({ file; root; package; _ } as source : Source.t) ->
      let file = String.chop_prefix_exn file ~prefix:[%string "%{repository}/"] in
      let claims = Claim.discover source |> Or_error.ok_exn in
      print_s [%sexp ({ file; root; package; claims } : Discovery.t)]);
    print_s [%sexp (Claims.run ~repository sources : unit Or_error.t)]);
  [%expect
    {|
    ((file theories/Collections/CollectionsFixture.v) (root Theories)
     (package Collections) (claims (((name closed) (line 1)))))
    ((file examples/Ssa/ExamplesSsaFixture.v) (root Examples) (package Examples)
     (claims (((name closed) (line 1)))))
    ((file examples/While/ExamplesWhileFixture.v) (root Examples)
     (package Examples) (claims (((name closed) (line 1)))))
    ((file tests/Collections/CollectionsTestFixture.v) (root Tests)
     (package Collections) (claims (((name closed) (line 1)))))
    ((file tests/Examples/ExamplesTestFixture.v) (root Tests) (package Examples)
     (claims (((name closed) (line 1)))))
    (Ok ())
    |}]
;;

let%expect_test "kernel reports a closed theorem" =
  let source = Fixture.source Fixture.closed in
  print_s [%sexp (Claims.source ~repository:Fixture.repository source : unit Or_error.t)];
  [%expect {| (Ok ()) |}]
;;

let%expect_test "a non Float theorem cannot inherit any axiom" =
  let source = Fixture.source Fixture.classical in
  print_s [%sexp (Claims.source ~repository:Fixture.repository source : unit Or_error.t)];
  [%expect
    {|
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1)
      (claim (classical_claim))
      (problem "theorem depends on axioms: Classical_Prop.classic")))
    |}]
;;

let%expect_test "Float permits only the exact three qualified axiom identities" =
  Set.iter Query.allowed_axioms ~f:(fun name ->
    let line = [%string "Constant %{name}"] in
    print_s [%sexp (Query.resolve [ line ] : unit Or_error.t)]);
  let source =
    Fixture.source ~package:Source.float_package ~file:"theories/Float/FloatFixture.v" Fixture.reals
  in
  print_s [%sexp (Claims.source ~repository:Fixture.repository source : unit Or_error.t)];
  [%expect
    {|
    (Ok ())
    (Ok ())
    (Ok ())
    (Ok ())
    |}]
;;

let%expect_test "Float rejects an unexpected kernel reported axiom" =
  let source =
    Fixture.source
      ~package:Source.float_package
      ~file:"theories/Float/FloatFixture.v"
      Fixture.classical
  in
  print_s [%sexp (Claims.source ~repository:Fixture.repository source : unit Or_error.t)];
  [%expect
    {|
    (Error
     (("Float assumptions inspection" (source.file theories/Float/FloatFixture.v)
       (claims (((name classical_claim) (line 1)))))
      (("Float theorem assumption" (source.file theories/Float/FloatFixture.v)
        (claim ((name classical_claim) (line 1))))
       ("unexpected Float axiom" (name Stdlib.Logic.Classical_Prop.classic)))))
    |}]
;;

let%expect_test "the Float allowance does not extend to examples or tests" =
  List.iter [ Source.Root.Examples; Source.Root.Tests ] ~f:(fun root ->
    let source = Fixture.source ~root ~package:Source.float_package Fixture.classical in
    print_s [%sexp (Claims.source ~repository:Fixture.repository source : unit Or_error.t)]);
  [%expect
    {|
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1)
      (claim (classical_claim))
      (problem "theorem depends on axioms: Classical_Prop.classic")))
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1)
      (claim (classical_claim))
      (problem "theorem depends on axioms: Classical_Prop.classic")))
    |}]
;;

let%expect_test "incomplete and malformed assumption output cannot report closure" =
  print_s [%sexp (Query.blocks ~count:1 "" : string list list Or_error.t)];
  print_s [%sexp (Query.blocks ~count:1 (Query.delimiter 0) : string list list Or_error.t)];
  List.iter
    [ []; [ Query.axioms ]; [ "Error: cannot inspect claim" ]; [ Query.closed; Query.closed ] ]
    ~f:(fun lines -> print_s [%sexp (Query.assumption_names lines : string list Or_error.t)]);
  [%expect
    {|
    (Error "missing assumptions query delimiter")
    (Error ("incomplete assumptions query" (index 0)))
    (Error ("missing or unrecognized assumptions report" (lines ())))
    (Error ("unrecognized axiom report" (lines (Axioms:))))
    (Error
     ("missing or unrecognized assumptions report"
      (lines ("Error: cannot inspect claim"))))
    (Error
     ("missing or unrecognized assumptions report"
      (lines
       ("Closed under the global context" "Closed under the global context"))))
    |}]
;;

let%expect_test "a failed Rocq process never returns a successful report" =
  Query.with_workspace ~f:(fun directory ->
    let output = Filename.concat directory "Query.log" in
    let result =
      Query.run_process
        ~mode:Repl
        ~directory
        ~args:[ "-l"; "/tmp/gaulois-TOOL-1/absent-file.v" ]
        ~output
    in
    print_s [%sexp (result : string Or_error.t)];
    Ok ())
  |> Or_error.ok_exn;
  [%expect
    {|
    (Error
     ("Rocq assumptions query failed" (status (Error (Exit_non_zero 1)))
      (transcript
        "Error: Can't find file /tmp/gaulois-TOOL-1/absent-file.v.\
       \n\
       \n")))
    |}]
;;

let%expect_test "dictionary parameters are accepted and parenthesized carrier fields rejected" =
  List.iter
    [ "Record dictionary {A : Type} := { value : A }."
    ; "Record dictionary := { carrier : (Type) }."
    ]
    ~f:(fun text -> print_s [%sexp (Hygiene.run [ Fixture.source text ] : unit Or_error.t)]);
  [%expect
    {|
    (Ok ())
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "record carrier Type field; parameterize the dictionary instead")))
    |}]
;;

let%expect_test "claims reject disabled kernel checking before querying" =
  let source = Fixture.source "Unset Guard Checking. Theorem bad : True. Proof. exact I. Qed." in
  print_s [%sexp (Claims.source ~repository:Fixture.repository source : unit Or_error.t)];
  [%expect
    {|
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "disabled kernel checking")))
    |}]
;;

let%expect_test "invalid proof replay fails with source and theorem context" =
  let module Inspection = struct
    type t =
      | Unexpected_success
      | Rejected
      | Unexpected_error of Error.t
    [@@deriving sexp_of]
  end
  in
  let source = Fixture.source "Theorem invalid_claim : False. Proof. exact I. Qed." in
  let result : Inspection.t =
    match Claims.source ~repository:Fixture.repository source with
    | Ok () -> Unexpected_success
    | Error error ->
      let diagnostic = Error.to_string_hum error in
      if
        List.for_all
          [ "Rocq assumptions query failed"; Fixture.file; "invalid_claim" ]
          ~f:(fun substring -> String.is_substring diagnostic ~substring)
      then Rejected
      else Unexpected_error error
  in
  print_s [%sexp (result : Inspection.t)];
  [%expect {| Rejected |}]
;;

let%expect_test "quoted comment terminators cannot expose a fake theorem" =
  let source =
    Fixture.source
      {|(* "*)" Theorem ghost : False. (* nested *) "(*" *)
Theorem valid : True. Proof. exact I. Qed.|}
  in
  print_s [%sexp (Hygiene.run [ source ] : unit Or_error.t)];
  print_s [%sexp (Claim.discover source : Claim.t list Or_error.t)];
  print_s [%sexp (Claims.source ~repository:Fixture.repository source : unit Or_error.t)];
  [%expect
    {|
    (Ok ())
    (Ok (((name valid) (line 2))))
    (Ok ())
    |}]
;;

let%expect_test "section assumptions generalize but global hypotheses are axioms" =
  List.iter
    [ "Section S. Context (P : Prop) (p : P). Theorem bound : P. Proof. exact p. Qed. End S."
    ; "Hypothesis global : True."
    ; "Module M. Variable global : Type. End M."
    ]
    ~f:(fun text -> print_s [%sexp (Hygiene.run [ Fixture.source text ] : unit Or_error.t)]);
  [%expect
    {|
    (Ok ())
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "global assumption; bind it in a Section or a theorem instead")))
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "global assumption; bind it in a Section or a theorem instead")))
    |}]
;;

let%expect_test "polymorphic record operations do not introduce carrier fields" =
  let source = Fixture.source "Record operations := { apply : forall {A : Type}, A -> A }." in
  print_s [%sexp (Hygiene.run [ source ] : unit Or_error.t)];
  [%expect {| (Ok ()) |}]
;;

let%expect_test "an aborted theorem cannot fall back to an imported closed constructor" =
  let aborted = Fixture.source "Theorem I : False. Abort." in
  let completed = Fixture.source "Theorem I : True. Proof. exact Logic.I. Qed." in
  print_s [%sexp (Claims.source ~repository:Fixture.repository aborted : unit Or_error.t)];
  print_s [%sexp (Claims.source ~repository:Fixture.repository completed : unit Or_error.t)];
  [%expect
    {|
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim (I))
      (problem "aborted theorem has no proof to inspect")))
    (Ok ())
    |}]
;;

let%expect_test "claim identity must be the exact source constant" =
  print_s
    [%sexp
      (Query.claim_report ~name:"I" [ "Constructor Stdlib.Init.Logic.I"; Query.closed ]
       : string list Or_error.t)];
  print_s
    [%sexp
      (Claims.source
         ~repository:Fixture.repository
         (Fixture.source "Theorem I : True. Proof. exact Logic.I. Qed. Reset I.")
       : unit Or_error.t)];
  [%expect
    {|
    (Error
     ("claim does not resolve to the source declaration" (name I)
      (lines
       ("Constructor Stdlib.Init.Logic.I" "Closed under the global context"))))
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "proof editing command can remove discovered declarations")))
    |}]
;;

let%expect_test "Program admission is rejected without any theorem roots" =
  let source = Fixture.source "Program Definition unfinished : False := _. Admit Obligations." in
  print_s [%sexp (Claim.discover source : Claim.t list Or_error.t)];
  print_s [%sexp (Hygiene.run [ source ] : unit Or_error.t)];
  print_s
    [%sexp
      (Hygiene.run
         [ Fixture.source {|(* Admit Obligations. *) Definition message := "Admit Obligations.".|} ]
       : unit Or_error.t)];
  [%expect
    {|
    (Ok ())
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "admitted Program obligation")))
    (Ok ())
    |}]
;;

let%expect_test "unused axiom imports are rejected in qualified and split spellings" =
  let policy = Import_policy.load () |> Or_error.ok_exn in
  List.iter
    [ "From Stdlib.Logic Require Import Classical_Prop."
    ; "From Stdlib Require Import Logic.Classical_Prop."
    ; "Require Import Stdlib.Logic.Classical_Prop."
    ; "From Stdlib.Logic Require Import Classical."
    ; "From Stdlib.Logic Require Import FunctionalExtensionality ProofIrrelevance."
    ; "From Stdlib Require Import Classical_Prop."
    ; "From Stdlib.Reals Require Import Reals."
    ]
    ~f:(fun imports ->
      let source = Fixture.source (String.concat ~sep:" " [ imports; Fixture.closed ]) in
      print_s [%sexp (Hygiene.source ~policy source : unit Or_error.t)]);
  [%expect
    {|
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem
       "axiom-bearing Stdlib import outside Float: Stdlib.Logic.Classical_Prop")))
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem
       "axiom-bearing Stdlib import outside Float: Stdlib.Logic.Classical_Prop")))
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem
       "axiom-bearing Stdlib import outside Float: Stdlib.Logic.Classical_Prop")))
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem
       "axiom-bearing Stdlib import outside Float: Stdlib.Logic.Classical")))
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem
       "axiom-bearing Stdlib import outside Float: Stdlib.Logic.FunctionalExtensionality")))
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem
       "axiom-bearing Stdlib import outside Float: Stdlib.Classical_Prop")))
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem "axiom-bearing Stdlib import outside Float: Stdlib.Reals.Reals")))
    |}]
;;

let%expect_test "constructive Stdlib imports and approved Float dependencies remain accepted" =
  let source =
    Fixture.source
      "From Stdlib.Lists Require Import List. From Stdlib.ZArith Require Import ZArith. From \
       Stdlib.Logic Require Import Eqdep_dec ProofIrrelevanceFacts. From Stdlib Require Import \
       List ZArith Lia. Require Import Stdlib.Lists.List."
  in
  let float = Fixture.source ~package:Source.float_package Fixture.reals in
  print_s [%sexp (Hygiene.run [ source; float ] : unit Or_error.t)];
  [%expect {| (Ok ()) |}]
;;

let%expect_test "failed closure cannot hide an aborted theorem followed by a replacement" =
  List.iter
    [ "Theorem I : False. Fail Qed. Abort. Definition I : True := Logic.I."
    ; "Theorem I : let p := False in p. Abort. Definition I : True := Logic.I."
    ]
    ~f:(fun text ->
      print_s
        [%sexp
          (Claims.source ~repository:Fixture.repository (Fixture.source text) : unit Or_error.t)]);
  [%expect
    {|
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim (I))
      (problem "aborted theorem has no proof to inspect")))
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim (I))
      (problem "aborted theorem has no proof to inspect")))
    |}]
;;

let%expect_test "unused classical import is a hygiene failure even for a kernel closed theorem" =
  let source =
    Fixture.source
      (String.concat
         ~sep:" "
         [ "From Stdlib.Logic Require Import Classical_Prop."; Fixture.closed ])
  in
  print_s [%sexp (Claims.source ~repository:Fixture.repository source : unit Or_error.t)];
  print_s [%sexp (Hygiene.run [ source ] : unit Or_error.t)];
  [%expect
    {|
    (Ok ())
    (Error
     ((file theories/Collections/CollectionsFixture.v) (line 1) (claim ())
      (problem
       "axiom-bearing Stdlib import outside Float: Stdlib.Logic.Classical_Prop")))
    |}]
;;

let%expect_test "Examples production subdirectories and computed test directory use Examples prefix"
  =
  let sources = Fixture.examples Fixture.closed in
  print_s [%sexp (Layout.run sources : unit Or_error.t)];
  print_s [%sexp (Hygiene.run sources : unit Or_error.t)];
  [%expect
    {|
    (Ok ())
    (Ok ())
    |}]
;;

let%expect_test "Examples paths reject language prefixes and wrong or unknown directories" =
  List.iter
    [ Fixture.at ~root:Examples "While/WhileWrong.v" Fixture.closed
    ; Fixture.at ~root:Examples "Ssa/SsaWrong.v" Fixture.closed
    ; Fixture.at ~root:Tests "Examples/SsaWrongTest.v" Fixture.closed
    ; Fixture.at ~root:Examples "Collections/ExamplesWrong.v" Fixture.closed
    ; Fixture.at ~root:Examples "Unknown/ExamplesUnknown.v" Fixture.closed
    ; Fixture.at ~root:Examples "ExamplesMisplaced.v" Fixture.closed
    ; Fixture.at ~root:Theories "Examples/ExamplesWrongTheory.v" Fixture.closed
    ; Fixture.at ~root:Tests "While/ExamplesWrongTest.v" Fixture.closed
    ; Fixture.at ~root:Tests "Unknown/ExamplesUnknownTest.v" Fixture.closed
    ; Fixture.at ~root:Theories "CollectionsMisplaced.v" Fixture.closed
    ; Fixture.at ~root:Tests "ExamplesMisplacedTest.v" Fixture.closed
    ]
    ~f:(fun source -> print_s [%sexp (Layout.run [ source ] : unit Or_error.t)]);
  [%expect
    {|
    (Error
     ((file examples/While/WhileWrong.v) (line 1) (claim ())
      (problem "Rocq basename must start with package Examples")))
    (Error
     ((file examples/Ssa/SsaWrong.v) (line 1) (claim ())
      (problem "Rocq basename must start with package Examples")))
    (Error
     ((file tests/Examples/SsaWrongTest.v) (line 1) (claim ())
      (problem "Rocq basename must start with package Examples")))
    (Error
     ((file examples/Collections/ExamplesWrong.v) (line 1) (claim ())
      (problem "source must be placed under its declared package directory")))
    (Error
     ((file examples/Unknown/ExamplesUnknown.v) (line 1) (claim ())
      (problem "source must be placed under its declared package directory")))
    (Error
     ((file examples/ExamplesMisplaced.v) (line 1) (claim ())
      (problem "source must be placed under its declared package directory")))
    (Error
     ((file theories/Examples/ExamplesWrongTheory.v) (line 1) (claim ())
      (problem "source must be placed under its declared package directory")))
    (Error
     ((file tests/While/ExamplesWrongTest.v) (line 1) (claim ())
      (problem "source must be placed under its declared package directory")))
    (Error
     ((file tests/Unknown/ExamplesUnknownTest.v) (line 1) (claim ())
      (problem "source must be placed under its declared package directory")))
    (Error
     ((file theories/CollectionsMisplaced.v) (line 1) (claim ())
      (problem "source must be placed under its declared package directory")))
    (Error
     ((file tests/ExamplesMisplacedTest.v) (line 1) (claim ())
      (problem "source must be placed under its declared package directory")))
    |}]
;;

let%expect_test "Examples basename uniqueness spans both production subdirectories and tests" =
  let basename = "ExamplesDuplicate.v" in
  let sources =
    List.map Fixture.example_paths ~f:(fun ({ root; relative } : Fixture.Path.t) ->
      let relative = Filename.concat (Filename.dirname relative) basename in
      Fixture.at ~root relative Fixture.closed)
  in
  print_s [%sexp (Layout.run sources : unit Or_error.t)];
  [%expect
    {|
    (Error
     ("duplicate Rocq basename" (basename ExamplesDuplicate.v)
      (files
       (examples/While/ExamplesDuplicate.v examples/Ssa/ExamplesDuplicate.v
        tests/Examples/ExamplesDuplicate.v))))
    |}]
;;

let%expect_test "Examples production sources retain theory hygiene and Float dependency boundaries" =
  List.iter
    [ "Print nat."
    ; "Extraction Language OCaml."
    ; "From Gaulois.Float Require Import FloatFixture."
    ]
    ~f:(fun text ->
      List.iter
        (List.take (Fixture.examples text) 2)
        ~f:(fun source -> print_s [%sexp (Hygiene.run [ source ] : unit Or_error.t)]));
  [%expect
    {|
    (Error
     ((file examples/While/ExamplesWhileFixture.v) (line 1) (claim ())
      (problem
       "theory extraction or query command belongs in a client or scratch file")))
    (Error
     ((file examples/Ssa/ExamplesSsaFixture.v) (line 1) (claim ())
      (problem
       "theory extraction or query command belongs in a client or scratch file")))
    (Error
     ((file examples/While/ExamplesWhileFixture.v) (line 1) (claim ())
      (problem
       "theory extraction or query command belongs in a client or scratch file")))
    (Error
     ((file examples/Ssa/ExamplesSsaFixture.v) (line 1) (claim ())
      (problem
       "theory extraction or query command belongs in a client or scratch file")))
    (Error
     ((file examples/While/ExamplesWhileFixture.v) (line 1) (claim ())
      (problem "only Gaulois.Float may depend on Float")))
    (Error
     ((file examples/Ssa/ExamplesSsaFixture.v) (line 1) (claim ())
      (problem "only Gaulois.Float may depend on Float")))
    |}]
;;

let%expect_test "Examples and computed test theorems reject the exact Float real axioms" =
  List.iter (Fixture.examples Fixture.reals) ~f:(fun source ->
    print_s [%sexp (Claim.discover source : Claim.t list Or_error.t)];
    print_s [%sexp (Claims.source ~repository:Fixture.repository source : unit Or_error.t)]);
  [%expect
    {|
    (Ok (((name real_claim) (line 1))))
    (Error
     ((file examples/While/ExamplesWhileFixture.v) (line 1) (claim (real_claim))
      (problem
       "theorem depends on axioms: ClassicalDedekindReals.sig_forall_dec, FunctionalExtensionality.functional_extensionality_dep")))
    (Ok (((name real_claim) (line 1))))
    (Error
     ((file examples/Ssa/ExamplesSsaFixture.v) (line 1) (claim (real_claim))
      (problem
       "theorem depends on axioms: ClassicalDedekindReals.sig_forall_dec, FunctionalExtensionality.functional_extensionality_dep")))
    (Ok (((name real_claim) (line 1))))
    (Error
     ((file tests/Examples/ExamplesTestFixture.v) (line 1) (claim (real_claim))
      (problem
       "theorem depends on axioms: ClassicalDedekindReals.sig_forall_dec, FunctionalExtensionality.functional_extensionality_dep")))
    |}]
;;

let%expect_test "Examples and test logical module paths resolve compiled theorem dependencies" =
  let result =
    Query.with_workspace ~f:(fun repository ->
      let sources = Fixture.examples Fixture.closed in
      let args = Query.load_paths repository in
      let output = Filename.concat repository "Compile.log" in
      let%bind.Or_error () =
        List.fold_result sources ~init:() ~f:(fun () ({ file; source; _ } : Source.t) ->
          let file = Filename.concat repository file in
          Core_unix.mkdir_p (Filename.dirname file);
          Out_channel.write_all file ~data:source;
          let%map.Or_error _ =
            Query.run_process ~mode:Compile ~directory:repository ~args:(args @ [ file ]) ~output
          in
          ())
      in
      let linked =
        {|From Gaulois.Examples.While Require Import ExamplesWhileFixture.
From Gaulois.Examples.Ssa Require Import ExamplesSsaFixture.
From Gaulois.Tests.Examples Require Import ExamplesTestFixture.
Theorem linked : True /\ True /\ True.
Proof.
  exact (conj ExamplesWhileFixture.closed
    (conj ExamplesSsaFixture.closed ExamplesTestFixture.closed)).
Qed.|}
      in
      let sources = Fixture.examples linked in
      let%bind.Or_error () = Layout.run sources in
      let%bind.Or_error () = Hygiene.run sources in
      Claims.run ~repository sources)
  in
  print_s [%sexp (result : unit Or_error.t)];
  [%expect {| (Ok ()) |}]
;;
