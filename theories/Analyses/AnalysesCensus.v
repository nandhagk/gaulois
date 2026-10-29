(** * Region summaries and static operand counts

    A postorder fold reuses each child summary and records every syntactic occurrence.
    For example, a loop containing an atom that reads x twice contributes two reads of x.
    Builds on: ViewsRegion, ViewsSkeleton and CollectionsMap. *)

From Stdlib Require Import List Bool PArith NArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Views Require Import ViewsSkeleton ViewsRegion.
Import List.ListNotations Skeleton.

(** * Postorder region tables *)

(** Child rows retain their occurrence identity by prefixing their local direction. *)
Definition region_prefix {R} (d : dir) (rows : list (position * R)) : list (position * R) :=
  map (fun pr => (d :: fst pr, snd pr)) rows.

(** Each recursive call returns its summary together with already materialised table rows.
    Prefixing and concatenation cost their materialised row and position sizes; source subtrees
    are never summarised again. The summary carrier is unrestricted. *)
Fixpoint region_fold {A G R} (alg : summary_algebra A G R) (s : stmt A G) :
    R * list (position * R) :=
  let result :=
    match s with
    | Atom a => (on_atom alg a, [])
    | Seq x y =>
      let '(rx, tx) := region_fold alg x in
      let '(ry, ty) := region_fold alg y in
      (on_seq alg rx ry, region_prefix DFirst tx ++ region_prefix DSecond ty)
    | If g x y =>
      let '(rx, tx) := region_fold alg x in
      let '(ry, ty) := region_fold alg y in
      (on_if alg g rx ry, region_prefix DFirst tx ++ region_prefix DSecond ty)
    | Block x =>
      let '(rx, tx) := region_fold alg x in (on_block alg rx, region_prefix DBody tx)
    | Loop x =>
      let '(rx, tx) := region_fold alg x in (on_loop alg rx, region_prefix DBody tx)
    | Jump n => (on_jump alg n, [])
    | JumpIf g n => (on_jump_if alg g n, [])
    | JumpTable g ns n => (on_jump_table alg g ns n, [])
    end in
  (fst result, ([], fst result) :: snd result).

(** Install the materialised rows in a canonical encoded-key map. *)
Fixpoint region_bind {R} (rows : list (position * R)) : Map.t position R :=
  match rows with
  | [] => Map.empty
  | (p, r) :: rest => Map.set position_encoding p r (region_bind rest)
  end.

(** The table records the fold at every valid position, including the root. *)
Definition region_table {A G R} (alg : summary_algebra A G R) (prog : stmt A G) :
    Map.t position R := region_bind (snd (region_fold alg prog)).

Local Definition region_dir_dec (x y : dir) : {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Local Definition region_position_dec := list_eq_dec region_dir_dec.

Local Fixpoint region_lookup {R} (p : position) (rows : list (position * R)) : option R :=
  match rows with
  | [] => None
  | (q, r) :: rest =>
    if region_position_dec p q then Some r else region_lookup p rest
  end.

Local Lemma region_bind_get {R} (p : position) (rows : list (position * R)) :
  Map.get position_encoding p (region_bind rows) = region_lookup p rows.
Proof.
  induction rows as [|[q r] rows IH]; cbn [region_bind region_lookup].
  - apply Map.get_empty.
  - destruct (region_position_dec p q) as [->|Hdifferent].
    + apply Map.get_set_same.
    + rewrite Map.get_set_other by exact Hdifferent; exact IH.
Qed.

Local Lemma region_lookup_app {R} p (left right : list (position * R)) :
  region_lookup p (left ++ right) =
  match region_lookup p left with Some r => Some r | None => region_lookup p right end.
Proof.
  induction left as [|[q r] left IH]; cbn [app region_lookup]; [reflexivity|].
  destruct (region_position_dec p q); [reflexivity|exact IH].
Qed.

Local Lemma region_lookup_prefix_nil {R} d (rows : list (position * R)) :
  region_lookup [] (region_prefix d rows) = None.
Proof.
  induction rows as [|[q r] rows IH];
    cbn [region_prefix map region_lookup fst snd]; [reflexivity|].
  destruct (region_position_dec [] (d :: q)); [discriminate|exact IH].
Qed.

Local Lemma region_lookup_prefix_cons {R} d e p (rows : list (position * R)) :
  region_lookup (d :: p) (region_prefix e rows) =
  if region_dir_dec d e then region_lookup p rows else None.
Proof.
  induction rows as [|[q r] rows IH]; cbn [region_prefix map region_lookup fst snd].
  - destruct (region_dir_dec d e); reflexivity.
  - destruct (region_dir_dec d e) as [->|Hdifferent].
    + destruct (region_position_dec (e :: p) (e :: q)) as [Hsame|Hdifferent],
        (region_position_dec p q) as [Hequal|Hunequal]; try congruence.
      exact IH.
    + destruct (region_position_dec (d :: p) (e :: q)); [congruence|].
      change (region_lookup (d :: p) (region_prefix e rows) = None).
      rewrite IH; destruct (region_dir_dec d e); congruence.
Qed.

Local Lemma region_fold_summary {A G R} (alg : summary_algebra A G R) (s : stmt A G) :
  fst (region_fold alg s) = summarise alg s.
Proof.
  induction s as [a|x IHx y IHy|g x IHx y IHy|x IHx|x IHx|n|g n|g ns n];
    cbn [region_fold summarise]; try reflexivity.
  - destruct (region_fold alg x), (region_fold alg y); cbn in *; congruence.
  - destruct (region_fold alg x), (region_fold alg y); cbn in *; congruence.
  - destruct (region_fold alg x); cbn in *; congruence.
  - destruct (region_fold alg x); cbn in *; congruence.
Qed.

Local Lemma region_fold_root {A G R} (alg : summary_algebra A G R) (s : stmt A G) :
  region_lookup [] (snd (region_fold alg s)) = Some (fst (region_fold alg s)).
Proof.
  destruct s; cbn [region_fold];
    repeat match goal with
    | |- context [region_fold ?fold_alg ?child] => destruct (region_fold fold_alg child)
    end; reflexivity.
Qed.

Local Lemma region_fold_lookup {A G R} (alg : summary_algebra A G R) (s : stmt A G) :
  forall p, region_lookup p (snd (region_fold alg s)) =
    match sub s p with Some t => Some (summarise alg t) | None => None end.
Proof.
  induction s as [a|x IHx y IHy|g x IHx y IHy|x IHx|x IHx|n|g n|g ns n];
    intros [|d p].
  all: try (rewrite region_fold_root, region_fold_summary; reflexivity).
  all: cbn [region_fold];
    repeat match goal with
    | |- context [region_fold ?fold_alg ?child] =>
      let Hfold := fresh "Hfold" in
      let r := fresh "summary" in let rows := fresh "rows" in
      destruct (region_fold fold_alg child) as [r rows] eqn:Hfold;
      try rewrite Hfold in IHx; try rewrite Hfold in IHy
    end;
    cbn [snd region_lookup];
    destruct (region_position_dec (d :: p) []) as [Himpossible|Hdifferent];
    [discriminate|].
  all: try rewrite region_lookup_app.
  all: repeat rewrite region_lookup_prefix_cons.
  all: destruct d; cbn [sub child snd] in *.
  all: repeat match goal with
    | |- context [region_dir_dec ?d ?e] => destruct (region_dir_dec d e)
    end; try congruence; auto.
  all: rewrite IHx; destruct (sub x p); reflexivity.
Qed.

(** Table lookup agrees with the independent recursive summary at every position. *)
Theorem region_table_agrees {A G R} (alg : summary_algebra A G R) (prog : stmt A G)
    (p : position) :
  Map.get position_encoding p (region_table alg prog) =
  match sub prog p with Some s => Some (summarise alg s) | None => None end.
Proof.
  unfold region_table; rewrite region_bind_get; apply region_fold_lookup.
Qed.

(** * Static occurrence census *)

(** The atom inventory traverses each syntactic loop body once. *)
Fixpoint census_atoms {A G} (prog : stmt A G) : list A :=
  match prog with
  | Atom a => [a]
  | Seq x y | If _ x y => census_atoms x ++ census_atoms y
  | Block x | Loop x => census_atoms x
  | Jump _ | JumpIf _ _ | JumpTable _ _ _ => []
  end.

(** Absent count bindings denote zero. *)
Definition census_get {V} (EV : encoding V) (counts : Map.t V N) (v : V) : N :=
  match Map.get EV v counts with Some n => n | None => 0%N end.

(** Every operand occurrence increments its key, including duplicates in a single atom. *)
Fixpoint census_add {V} (EV : encoding V) (vs : list V) (counts : Map.t V N) : Map.t V N :=
  match vs with
  | [] => counts
  | v :: rest => census_add EV rest (Map.set EV v (N.succ (census_get EV counts v)) counts)
  end.

(** Syntax traversal threads one count map through both children without dynamic iteration. *)
Fixpoint census_visit {A G V} (EV : encoding V) (uses : A -> list V) (prog : stmt A G)
    (counts : Map.t V N) : Map.t V N :=
  match prog with
  | Atom a => census_add EV (uses a) counts
  | Seq x y | If _ x y => census_visit EV uses y (census_visit EV uses x counts)
  | Block x | Loop x => census_visit EV uses x counts
  | Jump _ | JumpIf _ _ | JumpTable _ _ _ => counts
  end.

(** The census counts static operand occurrences in one syntax traversal. *)
Definition occurrence_census {A G V} (EV : encoding V) (uses : A -> list V)
    (prog : stmt A G) : Map.t V N := census_visit EV uses prog Map.empty.

Local Lemma census_add_exact {V} (EV : encoding V) (vs : list V) (v : V) :
  forall counts, census_get EV (census_add EV vs counts) v =
    (census_get EV counts v + N.of_nat (length
      (filter (fun x => Pos.eqb (encode EV x) (encode EV v)) vs)))%N.
Proof.
  induction vs as [|x vs IH]; intro counts; cbn [census_add filter length].
  - lia.
  - rewrite IH; unfold census_get at 1.
    destruct (Pos.eqb (encode EV x) (encode EV v)) eqn:Hsame.
    + apply Pos.eqb_eq in Hsame; apply (encode_injective EV) in Hsame; subst x.
      rewrite Map.get_set_same; cbn; lia.
    + rewrite Map.get_set_other; [fold (census_get EV counts v); lia|].
      intro Heq; subst x; rewrite Pos.eqb_refl in Hsame; discriminate.
Qed.

Local Lemma census_visit_exact {A G V} (EV : encoding V) (uses : A -> list V)
    (prog : stmt A G) (v : V) : forall counts,
  census_get EV (census_visit EV uses prog counts) v =
    (census_get EV counts v + N.of_nat (length
      (filter (fun x => Pos.eqb (encode EV x) (encode EV v))
        (concat (map uses (census_atoms prog))))))%N.
Proof.
  induction prog; intro counts; cbn [census_visit census_atoms map concat].
  - rewrite app_nil_r; apply census_add_exact.
  - rewrite IHprog2, IHprog1, map_app, concat_app, filter_app, length_app; lia.
  - rewrite IHprog2, IHprog1, map_app, concat_app, filter_app, length_app; lia.
  - apply IHprog.
  - apply IHprog.
  - cbn; lia.
  - cbn; lia.
  - cbn; lia.
Qed.

(** Lookup is exactly the flattened static occurrence count, with absent keys read as zero. *)
Theorem occurrence_census_exact {A G V} (EV : encoding V) (uses : A -> list V)
    (prog : stmt A G) (v : V) :
  (match Map.get EV v (occurrence_census EV uses prog) with
   | Some n => n | None => 0%N end) =
  N.of_nat (length (filter (fun x => Pos.eqb (encode EV x) (encode EV v))
    (concat (map uses (census_atoms prog))))).
Proof.
  change (census_get EV (census_visit EV uses prog Map.empty) v =
    N.of_nat (length (filter (fun x => Pos.eqb (encode EV x) (encode EV v))
      (concat (map uses (census_atoms prog)))))).
  rewrite census_visit_exact; unfold census_get; rewrite Map.get_empty; lia.
Qed.
