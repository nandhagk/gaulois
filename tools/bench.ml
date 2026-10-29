open Core
module A = Gaulois_extracted.Algorithms
module R = Gaulois_extracted.Rules_solver

module Config = struct
  let default_start = 8
  let default_steps = 3
  let default_repetitions = 3
  let minimum_size = 2
  let maximum_size = 512
  let maximum_steps = 8
  let maximum_repetitions = 20
  let scale = 2

  type t =
    { sizes : int Nonempty_list.t
    ; repetitions : int
    }
  [@@deriving sexp_of]

  let create ~start ~steps ~repetitions =
    if start < minimum_size || start > maximum_size
    then Or_error.error_s [%message "invalid starting size" (start : int) (maximum_size : int)]
    else if steps < 1 || steps > maximum_steps
    then Or_error.error_s [%message "invalid number of sizes" (steps : int) (maximum_steps : int)]
    else if repetitions < 1 || repetitions > maximum_repetitions
    then Or_error.error_s [%message "invalid repetitions" (repetitions : int)]
    else (
      let rec following size remaining =
        if remaining = 0
        then Ok []
        else if size > maximum_size / scale
        then Or_error.error_s [%message "generated size exceeds limit" (maximum_size : int)]
        else (
          let size = size * scale in
          let%map.Or_error tail = following size (remaining - 1) in
          size :: tail)
      in
      let%map.Or_error tail = following start (steps - 1) in
      { sizes = Nonempty_list.create start tail; repetitions })
  ;;
end

module Workload = struct
  type t =
    | Trie
    | Prepare
    | Dfs
    | Scc
    | Wto
    | Worklist
    | Total
    | Rules
  [@@deriving enumerate, sexp_of, string ~capitalize:"kebab-case"]
end

module Edge = struct
  type t =
    { source : int
    ; target : int
    }
end

module Input = struct
  let block_size = 4
  let worklist_fuel_per_unknown = 4
  let edge_predicate = 0
  let reach_predicate = 1
  let first_variable = 0
  let second_variable = 1

  let outgoing ~size source =
    let forward =
      if source + 1 < size then [ ({ source; target = source + 1 } : Edge.t) ] else []
    in
    if source mod block_size = block_size - 1
    then ({ source; target = source - block_size + 1 } : Edge.t) :: forward
    else forward
  ;;

  let graph size : (int, Edge.t) A.Graph.t =
    { entries = [ 0 ]
    ; nodes = List.init size ~f:Fn.id
    ; out = outgoing ~size
    ; source = (fun ({ source; _ } : Edge.t) -> source)
    ; target = (fun ({ target; _ } : Edge.t) -> target)
    }
  ;;

  let system size : (int, int, bool) A.System.t =
    { constraints = List.init size ~f:Fn.id
    ; target = Fn.id
    ; rhs =
        (fun key ->
          if key = 0
          then A.Query.Ask (size - 1, fun (_ : bool) -> A.Query.Ret true)
          else
            A.Query.Ask
              ( key - 1
              , fun value ->
                  if key = size - 1
                  then A.Query.Side (0, value, A.Query.Ret value)
                  else A.Query.Ret value ))
    }
  ;;

  let declarations size : (int, int, bool) A.System.static =
    { deps = (fun key -> [ (if key = 0 then size - 1 else key - 1) ])
    ; side_targets = (fun key -> if key = size - 1 then [ 0 ] else [])
    }
  ;;

  let atom predicate variables : int R.atom =
    { pred0 = predicate; args = List.map variables ~f:(fun variable -> R.TVar variable) }
  ;;

  let program : int R.program =
    let reach = atom reach_predicate [ first_variable ] in
    let edge = atom edge_predicate [ first_variable; second_variable ] in
    let next = atom reach_predicate [ second_variable ] in
    { penc = R.nat_encoding
    ; arity = (fun predicate -> if predicate = edge_predicate then 2 else 1)
    ; rules = [ ({ head = reach; body = [ R.LPos edge; R.LPos next ] } : int R.rule) ]
    }
  ;;

  let facts size =
    let code = R.Pos.of_succ_nat in
    (reach_predicate, [ code (size - 1) ])
    :: List.init (size - 1) ~f:(fun source -> edge_predicate, [ code source; code (source + 1) ])
  ;;
end

module Measurement = struct
  module Scaling = struct
    type t =
      { input : float option
      ; elapsed : float option
      }
    [@@deriving sexp_of]
  end

  module Input_size = struct
    type t =
      { size : int
      ; edges : int
      ; constraints : int
      ; facts : int
      ; rules : int
      }
    [@@deriving sexp_of]

    let create ~size (workload : Workload.t) =
      let empty = { size; edges = 0; constraints = 0; facts = 0; rules = 0 } in
      match workload with
      | Trie -> empty
      | Prepare | Dfs | Scc | Wto -> { empty with edges = size - 1 + (size / Input.block_size) }
      | Worklist | Total -> { empty with constraints = size }
      | Rules -> { empty with facts = size; rules = List.length Input.program.rules }
    ;;
  end

  type t =
    { workload : Workload.t
    ; input : Input_size.t
    ; output_count : int
    ; repetitions : int
    ; elapsed_seconds : float
    ; seconds_per_run : float
    ; scaling : Scaling.t
    }
  [@@deriving sexp_of]

  let scaling ~size ~seconds_per_run previous : Scaling.t =
    match previous with
    | None -> { input = None; elapsed = None }
    | Some ({ input = { size = old_size; _ }; seconds_per_run = old_time; _ } : t) ->
      { input = Some (Float.of_int size /. Float.of_int old_size)
      ; elapsed = (if Float.(old_time > 0.) then Some (seconds_per_run /. old_time) else None)
      }
  ;;
end

let require_count ~size count =
  if count = size
  then Ok count
  else Or_error.error_s [%message "unexpected generated workload result" (size : int) (count : int)]
;;

let run_system ~size ~workload =
  let system = Input.system size in
  let declarations = Input.declarations size in
  let scheduler = A.rpo_scheduler A.nat_encoding system declarations in
  let%bind.Or_error solution =
    match (workload : Workload.t) with
    | Total ->
      Ok
        (A.solve_total
           A.nat_encoding
           A.nat_encoding
           A.bool_lattice
           scheduler
           A.Joining
           system
           declarations)
    | Worklist ->
      let dependencies =
        A.Declared (declarations, A.index_system A.nat_encoding system declarations)
      in
      let fuel = A.Pos.of_succ_nat (size * Input.worklist_fuel_per_unknown) in
      let%map.Or_error assignment =
        A.run_worklist
          A.nat_encoding
          A.nat_encoding
          A.bool_lattice
          scheduler
          A.Joining
          system
          dependencies
          fuel
        |> Or_error.of_option ~error:(Error.of_string "generated worklist exhausted fuel")
      in
      A.lookup A.nat_encoding A.bool_lattice assignment
    | Trie | Prepare | Dfs | Scc | Wto | Rules ->
      Or_error.error_string "workload is not a constraint engine"
  in
  if A.check_post A.bool_lattice system solution
  then List.count system.constraints ~f:solution |> require_count ~size
  else Or_error.error_string "generated solution failed the full checker"
;;

let run_rules size =
  let%bind.Or_error database =
    R.solve_program Input.program (Input.facts size)
    |> Or_error.of_option ~error:(Error.of_string "generated Rules program failed stratification")
  in
  List.init size ~f:(fun key -> [ R.Pos.of_succ_nat key ])
  |> List.count ~f:(R.db_holds Input.program database Input.reach_predicate)
  |> require_count ~size
;;

let run_workload ~size (workload : Workload.t) =
  match workload with
  | Trie ->
    let keys = List.init size ~f:Fn.id in
    let trie =
      List.fold keys ~init:A.Trie.Empty ~f:(fun trie key ->
        A.Trie.set (A.nat_encoding key) key trie)
    in
    List.length (A.Trie.elements trie) |> require_count ~size
  | Worklist | Total -> run_system ~size ~workload
  | Rules -> run_rules size
  | Prepare | Dfs | Scc | Wto ->
    let graph = Input.graph size in
    let prepared = A.prepare A.nat_encoding graph in
    let count =
      match workload with
      | Prepare -> List.length (A.Map.elements prepared.out_index)
      | Dfs ->
        let result = A.dfs A.nat_encoding graph prepared A.FinSet.empty graph.entries in
        List.length result.preorder
      | Scc ->
        let result = A.scc A.nat_encoding graph prepared in
        List.sum (module Int) result.components ~f:List.length
      | Wto ->
        let order = A.wto_total A.nat_encoding graph prepared in
        if A.check_wto A.nat_encoding graph prepared order
        then List.length (A.wto_order order)
        else 0
      | Trie | Worklist | Total | Rules -> 0
    in
    require_count ~size count
;;

let measure ~size ~repetitions ~previous workload =
  let%bind.Or_error clock = Core_unix.Clock.gettime in
  Or_error.try_with_join
  @@ fun () ->
  let start = clock Monotonic in
  let%bind.Or_error counts =
    List.init repetitions ~f:(fun (_ : int) -> run_workload ~size workload)
    |> Or_error.combine_errors
  in
  let elapsed_seconds = Int63.to_float (Int63.( - ) (clock Monotonic) start) /. 1e9 in
  let seconds_per_run = elapsed_seconds /. Float.of_int repetitions in
  Ok
    ({ workload
     ; input = Measurement.Input_size.create ~size workload
     ; output_count = Option.value (List.last counts) ~default:0
     ; repetitions
     ; elapsed_seconds
     ; seconds_per_run
     ; scaling = Measurement.scaling ~size ~seconds_per_run previous
     }
     : Measurement.t)
;;

let run ({ sizes; repetitions } : Config.t) =
  List.map Workload.all ~f:(fun workload ->
    List.fold_result (Nonempty_list.to_list sizes) ~init:None ~f:(fun previous size ->
      let%map.Or_error measurement = measure ~size ~repetitions ~previous workload in
      print_s [%sexp (measurement : Measurement.t)];
      Some measurement)
    |> Or_error.map ~f:(fun (_ : Measurement.t option) -> ()))
  |> Or_error.combine_errors_unit
;;

let command =
  Command.basic_or_error
    ~summary:"Measure reproducible generated workloads (experiments, no performance guarantee)"
    (let%map_open.Command start =
       flag
         "start"
         (optional_with_default Config.default_start int)
         ~doc:[%string "N starting size (default %{Config.default_start#Int})"]
     and steps =
       flag
         "steps"
         (optional_with_default Config.default_steps int)
         ~doc:[%string "N number of doubled sizes (default %{Config.default_steps#Int})"]
     and repetitions =
       flag
         "repetitions"
         (optional_with_default Config.default_repetitions int)
         ~doc:[%string "N runs per size (default %{Config.default_repetitions#Int})"]
     in
     fun () ->
       let%bind.Or_error config = Config.create ~start ~steps ~repetitions in
       run config)
;;

let%expect_test "sizes double reproducibly" =
  print_s [%sexp (Config.create ~start:4 ~steps:3 ~repetitions:1 : Config.t Or_error.t)];
  [%expect {| (Ok ((sizes (4 8 16)) (repetitions 1))) |}]
;;

let%expect_test "invalid sizes counts repetitions and excessive growth are rejected" =
  List.iter
    [ Config.create ~start:0 ~steps:1 ~repetitions:1
    ; Config.create ~start:4 ~steps:0 ~repetitions:1
    ; Config.create ~start:4 ~steps:1 ~repetitions:0
    ; Config.create ~start:512 ~steps:2 ~repetitions:1
    ]
    ~f:(fun result -> print_s [%sexp (result : Config.t Or_error.t)]);
  [%expect
    {|
    (Error ("invalid starting size" (start 0) (maximum_size 512)))
    (Error ("invalid number of sizes" (steps 0) (maximum_steps 8)))
    (Error ("invalid repetitions" (repetitions 0)))
    (Error ("generated size exceeds limit" (maximum_size 512)))
    |}]
;;

let%expect_test "all extracted workloads compute nontrivial generated outputs" =
  List.iter Workload.all ~f:(fun workload ->
    let result = run_workload ~size:8 workload in
    print_s [%message (workload : Workload.t) (result : int Or_error.t)]);
  [%expect
    {|
    ((workload Trie) (result (Ok 8)))
    ((workload Prepare) (result (Ok 8)))
    ((workload Dfs) (result (Ok 8)))
    ((workload Scc) (result (Ok 8)))
    ((workload Wto) (result (Ok 8)))
    ((workload Worklist) (result (Ok 8)))
    ((workload Total) (result (Ok 8)))
    ((workload Rules) (result (Ok 8)))
    |}]
;;

let%expect_test "measurement output includes sizes timing and scaling" =
  let result = measure ~size:8 ~repetitions:1 ~previous:None Workload.Total in
  let result =
    Or_error.map result ~f:(fun measurement ->
      { measurement with elapsed_seconds = 0.; seconds_per_run = 0. })
  in
  print_s [%sexp (result : Measurement.t Or_error.t)];
  [%expect
    {|
    (Ok
     ((workload Total)
      (input ((size 8) (edges 0) (constraints 8) (facts 0) (rules 0)))
      (output_count 8) (repetitions 1) (elapsed_seconds 0) (seconds_per_run 0)
      (scaling ((input ()) (elapsed ())))))
    |}];
  let previous = Or_error.ok_exn result in
  let scaling =
    Measurement.scaling ~size:16 ~seconds_per_run:2. (Some { previous with seconds_per_run = 1. })
  in
  print_s [%sexp (scaling : Measurement.Scaling.t)];
  [%expect {| ((input (2)) (elapsed (2))) |}]
;;
