(** * Structured skeletons and their continuation machine

    Binary statements use relative labels and explicit continuation frames.
    For example, jumping to depth zero in a block completes that block.
    Builds on: CollectionsEncoding and ViewsSemantics. *)

From Stdlib Require Import List Bool Arith Lia PArith.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Views Require Import ViewsSemantics.
Import List.ListNotations.

Module Skeleton.

(** Statements separate client operations and guards from structured control. *)
Inductive stmt (A G : Type) : Type :=
  | Atom (a : A)
  | Seq (s1 s2 : stmt A G)
  | If (g : G) (s1 s2 : stmt A G)
  | Block (s : stmt A G)
  | Loop (s : stmt A G)
  | Jump (n : nat)
  | JumpIf (g : G) (n : nat)
  | JumpTable (g : G) (ns : list nat) (n : nat).

Arguments Atom {A G}.
Arguments Seq {A G}.
Arguments If {A G}.
Arguments Block {A G}.
Arguments Loop {A G}.
Arguments Jump {A G}.
Arguments JumpIf {A G}.
Arguments JumpTable {A G}.

End Skeleton.
Import Skeleton.

(** Directions select binary children or the body of a labelled statement. *)
Inductive dir : Type :=
  | DFirst
  | DSecond
  | DBody.

(** Positions list directions from the root outwards. *)
Definition position : Type := list dir.

(** Directions have the codes one, two and three. *)
Definition dir_encoding : encoding dir.
Proof.
  refine (Encoding _ (fun d =>
    match d with
    | DFirst => 1%positive
    | DSecond => 2%positive
    | DBody => 3%positive
    end) _).
  intros [] [] Hcode; try discriminate; reflexivity.
Defined.

(** Position codes preserve each direction in order. *)
Definition position_encoding : encoding position := list_encoding dir_encoding.

(** A direction exists only for the corresponding statement shape. *)
Definition child {A G} (s : stmt A G) (d : dir) : option (stmt A G) :=
  match s, d with
  | Seq s1 _, DFirst | If _ s1 _, DFirst => Some s1
  | Seq _ s2, DSecond | If _ _ s2, DSecond => Some s2
  | Block s, DBody | Loop s, DBody => Some s
  | _, _ => None
  end.

(** Lookup follows a position and rejects a missing child. *)
Fixpoint sub {A G} (s : stmt A G) (p : position) : option (stmt A G) :=
  match p with
  | [] => Some s
  | d :: p =>
    match child s d with
    | Some c => sub c p
    | None => None
    end
  end.

(** Valid positions occur once, in preorder. *)
Fixpoint positions {A G} (s : stmt A G) : list position :=
  match s with
  | Seq s1 s2 | If _ s1 s2 =>
    [] :: map (cons DFirst) (positions s1) ++ map (cons DSecond) (positions s2)
  | Block s | Loop s => [] :: map (cons DBody) (positions s)
  | _ => [[]]
  end.

(** Every relative label must refer to an enclosing block or loop. *)
Fixpoint labels_ok {A G} (d : nat) (s : stmt A G) : bool :=
  match s with
  | Seq s1 s2 | If _ s1 s2 => labels_ok d s1 && labels_ok d s2
  | Block s | Loop s => labels_ok (S d) s
  | Jump n | JumpIf _ n => n <? d
  | JumpTable _ ns n => forallb (fun n => n <? d) ns && (n <? d)
  | Atom _ => true
  end.

(** Clients provide observable atoms, partial guards and jump store effects. *)
Record skeleton_client (A G St O : Type) : Type := SkeletonClient {
  init_store : St -> Prop;
  atom_step : A -> St -> list O -> St -> Prop;
  atom_trap : A -> St -> Prop;
  atom_stop : A -> St -> Prop;
  guard_bool : G -> St -> option bool;
  guard_index : G -> St -> option nat;
  jump_effect : position -> nat -> St -> St -> Prop
}.

Arguments SkeletonClient {A G St O}.
Arguments init_store {A G St O}.
Arguments atom_step {A G St O}.
Arguments atom_trap {A G St O}.
Arguments atom_stop {A G St O}.
Arguments guard_bool {A G St O}.
Arguments guard_index {A G St O}.
Arguments jump_effect {A G St O}.

(** Client laws distinguish steps, program traps and resource stops and make jumps total. *)
Record skeleton_client_laws {A G St O} (C : skeleton_client A G St O) : Prop := {
  jump_total : forall p n st, exists st', jump_effect C p n st st';
  atom_progress : forall a st,
    (exists l st', atom_step C a st l st') \/ atom_trap C a st \/ atom_stop C a st;
  atom_trap_halts : forall a st, atom_trap C a st ->
    ~ (exists l st', atom_step C a st l st');
  atom_stop_halts : forall a st, atom_stop C a st ->
    ~ (exists l st', atom_step C a st l st');
  atom_trap_not_stop : forall a st, ~ (atom_trap C a st /\ atom_stop C a st)
}.

Arguments jump_total {A G St O C}.
Arguments atom_progress {A G St O C}.
Arguments atom_trap_halts {A G St O C}.
Arguments atom_stop_halts {A G St O C}.
Arguments atom_trap_not_stop {A G St O C}.

(** Frames retain the owner of each pending structured continuation. *)
Inductive frame : Type :=
  | FSeq (p : position)
  | FJoin (p : position)
  | FBlock (p : position)
  | FLoop (p : position).

(** A machine state either enters a statement or returns from it. *)
Inductive mstate (St : Type) : Type :=
  | Go (p : position) (k : list frame) (st : St)
  | Ret (p : position) (k : list frame) (st : St).

Arguments Go {St}.
Arguments Ret {St}.

(** A jump skips administrative frames and counts only labelled frames. *)
Fixpoint resume {St} (n : nat) (k : list frame) (st : St) : option (mstate St) :=
  match k with
  | [] => None
  | FSeq _ :: k | FJoin _ :: k => resume n k st
  | FBlock p :: k =>
    match n with
    | 0 => Some (Ret p k st)
    | S n => resume n k st
    end
  | FLoop p :: k =>
    match n with
    | 0 => Some (Go (p ++ [DBody]) (FLoop p :: k) st)
    | S n => resume n k st
    end
  end.

(** Machine rules preserve client event lists and make control steps silent. *)
Inductive skel_step {A G St O} (prog : stmt A G) (C : skeleton_client A G St O) :
    mstate St -> list O -> mstate St -> Prop :=
  | step_atom : forall p k st a l st', sub prog p = Some (Atom a) ->
      atom_step C a st l st' -> skel_step prog C (Go p k st) l (Ret p k st')
  | step_seq : forall p k st s1 s2, sub prog p = Some (Seq s1 s2) ->
      skel_step prog C (Go p k st) [] (Go (p ++ [DFirst]) (FSeq p :: k) st)
  | step_if : forall p k st g s1 s2 b, sub prog p = Some (If g s1 s2) ->
      guard_bool C g st = Some b -> skel_step prog C (Go p k st) []
        (Go (p ++ [if b then DFirst else DSecond]) (FJoin p :: k) st)
  | step_block : forall p k st s, sub prog p = Some (Block s) ->
      skel_step prog C (Go p k st) [] (Go (p ++ [DBody]) (FBlock p :: k) st)
  | step_loop : forall p k st s, sub prog p = Some (Loop s) ->
      skel_step prog C (Go p k st) [] (Go (p ++ [DBody]) (FLoop p :: k) st)
  | step_jump : forall p k st n st' m, sub prog p = Some (Jump n) ->
      jump_effect C p n st st' -> resume n k st' = Some m ->
      skel_step prog C (Go p k st) [] m
  | step_jump_if_taken : forall p k st g n st' m, sub prog p = Some (JumpIf g n) ->
      guard_bool C g st = Some true -> jump_effect C p n st st' ->
      resume n k st' = Some m -> skel_step prog C (Go p k st) [] m
  | step_jump_if_skipped : forall p k st g n, sub prog p = Some (JumpIf g n) ->
      guard_bool C g st = Some false -> skel_step prog C (Go p k st) [] (Ret p k st)
  | step_jump_table : forall p k st g ns n i st' m,
      sub prog p = Some (JumpTable g ns n) -> guard_index C g st = Some i ->
      jump_effect C p (nth i ns n) st st' -> resume (nth i ns n) k st' = Some m ->
      skel_step prog C (Go p k st) [] m
  | step_ret_seq : forall c p k st, skel_step prog C (Ret c (FSeq p :: k) st) []
      (Go (p ++ [DSecond]) (FJoin p :: k) st)
  | step_ret_join : forall c p k st,
      skel_step prog C (Ret c (FJoin p :: k) st) [] (Ret p k st)
  | step_ret_block : forall c p k st,
      skel_step prog C (Ret c (FBlock p :: k) st) [] (Ret p k st)
  | step_ret_loop : forall c p k st, skel_step prog C (Ret c (FLoop p :: k) st) []
      (Go (p ++ [DBody]) (FLoop p :: k) st).

(** Initial states enter the root with an empty continuation. *)
Definition skeleton_semantics {A G St O} (prog : stmt A G) (C : skeleton_client A G St O) :
    semantics (mstate St) O :=
  {| initial := fun m => exists st, m = Go [] [] st /\ init_store C st;
     step := skel_step prog C |}.

(** Both machine phases expose the current client store. *)
Definition store_of {St} (m : mstate St) : St :=
  match m with
  | Go _ _ st | Ret _ _ st => st
  end.

(** Both machine phases expose their continuation stack. *)
Definition stack_of {St} (m : mstate St) : list frame :=
  match m with
  | Go _ k _ | Ret _ k _ => k
  end.

(** Endings classify root completion and the client's atom or guard failures. *)
Definition skeleton_endings {A G St O} (prog : stmt A G) (C : skeleton_client A G St O) :
    endings (mstate St) :=
  {| final := fun m => match m with
       | Ret [] [] _ => True
       | _ => False
       end;
     trapped := fun m => match m with
       | Go p _ st => match sub prog p with
         | Some (Atom a) => atom_trap C a st
         | Some (If g _ _) | Some (JumpIf g _) => guard_bool C g st = None
         | Some (JumpTable g _ _) => guard_index C g st = None
         | _ => False
         end
       | Ret _ _ _ => False
       end;
     stopped := fun m => match m with
       | Go p _ st => match sub prog p with
         | Some (Atom a) => atom_stop C a st
         | _ => False
         end
       | Ret _ _ _ => False
       end |}.

(** * Position facts *)

Lemma sub_app {A G} (s : stmt A G) p q :
  sub s (p ++ q) =
    match sub s p with
    | Some t => sub t q
    | None => None
    end.
Proof.
  revert s; induction p as [|d p IH]; intro s; cbn; [reflexivity|].
  destruct (child s d); [apply IH|reflexivity].
Qed.

Lemma sub_child {A G} (s : stmt A G) p t d :
  sub s p = Some t -> sub s (p ++ [d]) = child t d.
Proof.
  intro Hsub; rewrite sub_app, Hsub; cbn; destruct (child t d); reflexivity.
Qed.

(** * Canonical continuation contexts *)

(** Descending to a child records the continuation belonging to its owner. *)
Definition child_frame {A G} (s : stmt A G) (d : dir) (p : position) : frame :=
  match s with
  | Seq _ _ =>
    match d with
    | DFirst => FSeq p
    | _ => FJoin p
    end
  | Block _ => FBlock p
  | Loop _ => FLoop p
  | _ => FJoin p
  end.

(** A context records exactly the ancestor frames of a valid position. *)
Inductive context {A G} (prog : stmt A G) : position -> list frame -> Prop :=
  | context_root : context prog [] []
  | context_child : forall p k s d t, context prog p k -> sub prog p = Some s ->
      child s d = Some t -> context prog (p ++ [d]) (child_frame s d p :: k).

Arguments context_root {A G prog}.
Arguments context_child {A G prog p k s d t}.

(** Lookup computes the canonical context while following a position once. *)
Fixpoint locate_from {A G} (s : stmt A G) (base p : position) (k : list frame) :
    option (stmt A G * list frame) :=
  match p with
  | [] => Some (s, k)
  | d :: p =>
    match child s d with
    | Some t => locate_from t (base ++ [d]) p (child_frame s d base :: k)
    | None => None
    end
  end.

(** Root lookup supplies both the subtree and its unique continuation. *)
Definition locate {A G} (prog : stmt A G) (p : position) := locate_from prog [] p [].

Lemma locate_from_app {A G} (s : stmt A G) base p q k :
  locate_from s base (p ++ q) k =
  match locate_from s base p k with
  | Some (t, k') => locate_from t (base ++ p) q k'
  | None => None
  end.
Proof.
  revert s base k; induction p as [|d p IH]; intros s base k; cbn.
  - rewrite app_nil_r; reflexivity.
  - destruct (child s d) as [t|]; [|reflexivity].
    rewrite IH; rewrite <- app_assoc; reflexivity.
Qed.

Lemma context_locate {A G} (prog : stmt A G) p k :
  context prog p k -> exists s, locate prog p = Some (s, k) /\ sub prog p = Some s.
Proof.
  intro Hctx; induction Hctx as [|p k s d t Hctx [u [Hloc Hsub]] Howner Hchild].
  - exists prog; split; reflexivity.
  - assert (u = s) by congruence; subst u; exists t; split.
    + unfold locate in *; rewrite locate_from_app, Hloc; cbn; rewrite Hchild.
      reflexivity.
    + rewrite (sub_child prog p s d Howner); exact Hchild.
Qed.

Lemma locate_from_context {A G} (prog s : stmt A G) base p k t k' :
  context prog base k -> sub prog base = Some s ->
  locate_from s base p k = Some (t, k') ->
  context prog (base ++ p) k' /\ sub prog (base ++ p) = Some t.
Proof.
  revert s base k; induction p as [|d p IH]; intros s base k Hctx Hsub Hloc; cbn in Hloc.
  - inversion Hloc; subst; rewrite app_nil_r; split; assumption.
  - destruct (child s d) as [u|] eqn:Hchild; [|discriminate].
    replace (base ++ d :: p) with ((base ++ [d]) ++ p) by
      (rewrite <- app_assoc; reflexivity).
    eapply IH; [eapply context_child; eassumption| |exact Hloc].
    rewrite (sub_child prog base s d Hsub); exact Hchild.
Qed.

Lemma locate_context {A G} (prog : stmt A G) p s k :
  locate prog p = Some (s, k) -> context prog p k /\ sub prog p = Some s.
Proof.
  intro Hloc; exact (locate_from_context prog prog [] p [] s k context_root eq_refl Hloc).
Qed.

Lemma context_unique {A G} (prog : stmt A G) p k k' :
  context prog p k -> context prog p k' -> k = k'.
Proof.
  intros Hctx Hctx'; destruct (context_locate prog p k Hctx) as [s [Hloc _]].
  destruct (context_locate prog p k' Hctx') as [s' [Hloc' _]]; congruence.
Qed.

Lemma locate_from_sub {A G} (s : stmt A G) base p k :
  option_map fst (locate_from s base p k) = sub s p.
Proof.
  revert s base k; induction p as [|d p IH]; intros s base k; cbn; [reflexivity|].
  destruct (child s d); [apply IH|reflexivity].
Qed.

Lemma sub_context {A G} (prog : stmt A G) p s :
  sub prog p = Some s -> exists k, context prog p k.
Proof.
  intro Hsub; pose proof (locate_from_sub prog [] p []) as Hloc.
  rewrite Hsub in Hloc; destruct (locate prog p) as [[t k]|] eqn:Hlookup;
    change (option_map fst (locate prog p) = Some s) in Hloc;
    rewrite Hlookup in Hloc; cbn in Hloc; [|discriminate].
  exists k; exact (proj1 (locate_context prog p t k Hlookup)).
Qed.

Lemma context_sub {A G} (prog : stmt A G) p k :
  context prog p k -> exists s, sub prog p = Some s.
Proof.
  intro Hctx; destruct (context_locate prog p k Hctx) as [s [_ Hsub]]; eauto.
Qed.

(** Every frame in a canonical stack describes a valid owner and its outer context. *)
Fixpoint stack_valid {A G} (prog : stmt A G) (k : list frame) : Prop :=
  match k with
  | [] => True
  | f :: k => stack_valid prog k /\
    match f with
    | FSeq p => context prog p k /\ exists s1 s2, sub prog p = Some (Seq s1 s2)
    | FJoin p => context prog p k /\
      ((exists s1 s2, sub prog p = Some (Seq s1 s2)) \/
       (exists g s1 s2, sub prog p = Some (If g s1 s2)))
    | FBlock p => context prog p k /\ exists s, sub prog p = Some (Block s)
    | FLoop p => context prog p k /\ exists s, sub prog p = Some (Loop s)
    end
  end.

Lemma context_stack_valid {A G} (prog : stmt A G) p k :
  context prog p k -> stack_valid prog k.
Proof.
  intro Hctx; induction Hctx as [|p k s d t Hctx IH Hsub Hchild]; [exact I|].
  destruct s; destruct d; cbn in Hchild; try discriminate; cbn.
  all: split; [exact IH|].
  all: split; [exact Hctx|]; eauto.
Qed.

Lemma context_return {A G} (prog : stmt A G) c f k :
  context prog c (f :: k) ->
  exists p d s t, c = p ++ [d] /\ sub prog p = Some s /\ child s d = Some t /\
    f = child_frame s d p /\ context prog p k.
Proof.
  intro Hctx; inversion Hctx as [|p k' s d t Hparent Hsub Hchild Heqp Heqk]; subst.
  exists p, d, s, t; repeat split; assumption.
Qed.

Lemma resume_context {A G St} (prog : stmt A G) n k (st : St) m :
  stack_valid prog k -> resume n k st = Some m ->
  match m with
  | Go p k _ | Ret p k _ => context prog p k
  end.
Proof.
  revert n; induction k as [|f k IH]; intros n Hvalid Hresume; [discriminate|].
  destruct Hvalid as [Htail Hframe]; destruct f as [p|p|p|p]; cbn in Hresume.
  - eapply IH; eassumption.
  - eapply IH; eassumption.
  - destruct n as [|n]; [inversion Hresume; subst; exact (proj1 Hframe)|].
    eapply IH; eassumption.
  - destruct n as [|n]; [|eapply IH; eassumption].
    inversion Hresume; subst; destruct Hframe as [Hctx [s Hsub]].
    eapply (context_child (s := Loop s) (d := DBody));
      [exact Hctx|exact Hsub|reflexivity].
Qed.

(** Reachable states retain the unique syntactic continuation of their position. *)
Definition machine_valid {A G St} (prog : stmt A G) (m : mstate St) : Prop :=
  match m with
  | Go p k _ | Ret p k _ => context prog p k
  end.

Lemma machine_valid_step {A G St O} (prog : stmt A G) (C : skeleton_client A G St O)
    m l m' : machine_valid prog m -> skel_step prog C m l m' -> machine_valid prog m'.
Proof.
  intros Hvalid Hstep; destruct Hstep; cbn in *.
  - exact Hvalid.
  - eapply (context_child (s := Seq s1 s2) (d := DFirst)); eassumption || reflexivity.
  - destruct b.
    + eapply (context_child (s := If g s1 s2) (d := DFirst)); eassumption || reflexivity.
    + eapply (context_child (s := If g s1 s2) (d := DSecond)); eassumption || reflexivity.
  - eapply (context_child (s := Block s) (d := DBody)); eassumption || reflexivity.
  - eapply (context_child (s := Loop s) (d := DBody)); eassumption || reflexivity.
  - eapply resume_context; [eapply context_stack_valid; exact Hvalid|eassumption].
  - eapply resume_context; [eapply context_stack_valid; exact Hvalid|eassumption].
  - exact Hvalid.
  - eapply resume_context; [eapply context_stack_valid; exact Hvalid|eassumption].
  - destruct (context_stack_valid prog _ _ Hvalid) as [_ [Hctx [s1 [s2 Hsub]]]].
    eapply (context_child (s := Seq s1 s2) (d := DSecond));
      [exact Hctx|exact Hsub|reflexivity].
  - exact (proj1 (proj2 (context_stack_valid prog _ _ Hvalid))).
  - exact (proj1 (proj2 (context_stack_valid prog _ _ Hvalid))).
  - destruct (context_stack_valid prog _ _ Hvalid) as [_ [Hctx [s Hsub]]].
    eapply (context_child (s := Loop s) (d := DBody));
      [exact Hctx|exact Hsub|reflexivity].
Qed.

Lemma reachable_machine_valid {A G St O} (prog : stmt A G)
    (C : skeleton_client A G St O) m :
  reachable_state (skeleton_semantics prog C) m -> machine_valid prog m.
Proof.
  intros [m0 [tr [[st [-> Hinit]] Hrun]]].
  assert (Hvalid : machine_valid prog (Go [] [] st)) by constructor.
  revert Hvalid; induction Hrun as [m|m l m' tr t Hstep Hrun IH]; intro Hvalid.
  - exact Hvalid.
  - apply IH; exact (machine_valid_step prog C m l m' Hvalid Hstep).
Qed.

Lemma nodup_cons_map (d : dir) (xs : list position) :
  NoDup xs -> NoDup (map (cons d) xs).
Proof.
  intro Hnodup; induction Hnodup as [|x xs Hnot Hnodup IH]; cbn; constructor.
  - intro Hin; apply in_map_iff in Hin; destruct Hin as [y [Heq Hin]].
    inversion Heq; subst; contradiction.
  - exact IH.
Qed.

Lemma positions_nodup_binary d e (xs ys : list position) :
  d <> e -> NoDup xs -> NoDup ys ->
  NoDup ([] :: map (cons d) xs ++ map (cons e) ys).
Proof.
  intros Hne Hxs Hys; constructor.
  - intro Hin; apply in_app_or in Hin; destruct Hin as [Hin|Hin];
      apply in_map_iff in Hin; destruct Hin as [p [Hbad _]]; discriminate.
  - apply NoDup_app; repeat split.
    + apply nodup_cons_map; exact Hxs.
    + apply nodup_cons_map; exact Hys.
    + intros p Hin Hin'; apply in_map_iff in Hin; apply in_map_iff in Hin'.
      destruct Hin as [q [Heq _]], Hin' as [r [Heq' _]]; congruence.
Qed.

(** The position enumeration contains exactly the valid positions, without duplicates. *)
Theorem positions_exact {A G} (prog : stmt A G) :
  NoDup (positions prog) /\
  (forall p, In p (positions prog) <-> exists s, sub prog p = Some s).
Proof.
  induction prog as [a|s1 [H1 E1] s2 [H2 E2]|g s1 [H1 E1] s2 [H2 E2]|
    s [H E]|s [H E]|n|g n|g ns n]; split.
  all: try solve [cbn; constructor; [tauto|constructor]].
  all: try solve [apply positions_nodup_binary; [discriminate|exact H1|exact H2]].
  all: try solve [cbn; constructor; [intro Hin; apply in_map_iff in Hin;
    destruct Hin as [p [Hbad _]]; discriminate|apply nodup_cons_map; exact H]].
  all: intros [|d p]; cbn; try solve [split; [intros _; eexists; reflexivity|tauto]].
  all: try solve [destruct d; cbn; split; [tauto|intros [? Hbad]; discriminate]].
  all: rewrite ?in_app_iff, ?in_map_iff.
  all: destruct d; cbn.
  all: try solve [split; [intros [Hbad|Hbad]; [discriminate|];
    destruct Hbad as [q [Hbad _]]; discriminate|intros [? Hbad]; discriminate]].
  all: split.
  all: try solve [intros [Hbad|Hin]; [discriminate|];
    destruct Hin as [[q [Heq Hin]]|[q [Heq Hin]]]; inversion Heq; subst;
    first [apply E1|apply E2]; exact Hin].
  all: try solve [intro Hex; first [apply E1 in Hex|apply E2 in Hex];
    right; first [left; exists p|right; exists p]; split; [reflexivity|exact Hex]].
  all: try solve [intros [Hbad|[q [Heq Hin]]]; [discriminate|]; inversion Heq; subst;
    apply E; exact Hin].
  all: try solve [intro Hex; apply E in Hex; right; exists p; split; [reflexivity|exact Hex]].
  all: try solve [intros [Hbad|Hfalse]; [discriminate|contradiction]].
  all: try solve [intros [? Hbad]; discriminate].
  all: try solve [intro Hex; right; right; exists p; split; [reflexivity|];
    apply (proj2 (E2 p)); exact Hex].
Qed.

(** * Progress and endings *)

(** Only block and loop frames contribute to relative label depth. *)
Fixpoint label_count (k : list frame) : nat :=
  match k with
  | [] => 0
  | FSeq _ :: k | FJoin _ :: k => label_count k
  | FBlock _ :: k | FLoop _ :: k => S (label_count k)
  end.

Lemma resume_total {St} n k (st : St) :
  n < label_count k -> exists m, resume n k st = Some m.
Proof.
  revert n; induction k as [|f k IH]; intros n Hbound; cbn in Hbound; [lia|].
  destruct f; cbn in *; try (apply IH; exact Hbound).
  all: destruct n; [eexists; reflexivity|apply IH; lia].
Qed.

Lemma context_labels_ok {A G} (prog : stmt A G) p k s :
  labels_ok 0 prog = true -> context prog p k -> sub prog p = Some s ->
  labels_ok (label_count k) s = true.
Proof.
  intros Hlabels Hctx; revert s.
  induction Hctx as [|p k owner d t Hctx IH Hsub Hchild]; intros s Hlookup.
  - inversion Hlookup; subst; exact Hlabels.
  - rewrite (sub_child prog p owner d Hsub), Hchild in Hlookup.
    inversion Hlookup; subst s.
    specialize (IH owner Hsub).
    destruct owner; destruct d; cbn in Hchild; try discriminate; inversion Hchild; subst;
      cbn [child_frame label_count labels_ok] in *; try exact IH;
      apply andb_true_iff in IH; tauto.
Qed.

Lemma nth_label_bound ns n i d :
  forallb (fun x => x <? d) ns = true -> n < d -> nth i ns n < d.
Proof.
  revert i; induction ns as [|x ns IH]; intros [|i] Hall Hn; cbn in *; try exact Hn.
  - apply andb_true_iff in Hall; apply Nat.ltb_lt; tauto.
  - apply andb_true_iff in Hall; apply IH; tauto.
Qed.

Lemma machine_progress {A G St O} (prog : stmt A G) (C : skeleton_client A G St O) m :
  labels_ok 0 prog = true -> skeleton_client_laws C -> machine_valid prog m ->
  running (skeleton_semantics prog C) m \/ final (skeleton_endings prog C) m \/
    trapped (skeleton_endings prog C) m \/ stopped (skeleton_endings prog C) m.
Proof.
  intros Hlabels Hlaws Hvalid; destruct m as [p k st|p k st].
  - destruct (context_sub prog p k Hvalid) as [s Hsub].
    pose proof (context_labels_ok prog p k s Hlabels Hvalid Hsub) as Hlocal.
    destruct s as [a|s1 s2|g s1 s2|s|s|n|g n|g ns n].
    + destruct (atom_progress Hlaws a st) as [[l [st' Hatom]]|[Htrap|Hstop]].
      * left; exists l, (Ret p k st'); econstructor; eassumption.
      * right; right; left; cbn; rewrite Hsub; exact Htrap.
      * right; right; right; cbn; rewrite Hsub; exact Hstop.
    + left; eexists [], _; eapply step_seq; exact Hsub.
    + destruct (guard_bool C g st) as [b|] eqn:Hguard.
      * left; eexists [], _; eapply step_if; eassumption.
      * right; right; left; cbn; rewrite Hsub; exact Hguard.
    + left; eexists [], _; eapply step_block; exact Hsub.
    + left; eexists [], _; eapply step_loop; exact Hsub.
    + destruct (jump_total Hlaws p n st) as [st' Heffect].
      destruct (resume_total n k st' (proj1 (Nat.ltb_lt _ _) Hlocal)) as [m Hresume].
      left; exists [], m; eapply step_jump; eassumption.
    + destruct (guard_bool C g st) as [[|]|] eqn:Hguard.
      * destruct (jump_total Hlaws p n st) as [st' Heffect].
        destruct (resume_total n k st' (proj1 (Nat.ltb_lt _ _) Hlocal)) as [m Hresume].
        left; exists [], m; eapply step_jump_if_taken; eassumption.
      * left; eexists [], _; eapply step_jump_if_skipped; eassumption.
      * right; right; left; cbn; rewrite Hsub; exact Hguard.
    + destruct (guard_index C g st) as [i|] eqn:Hguard.
      * cbn in Hlocal; apply andb_true_iff in Hlocal; destruct Hlocal as [Hall Hdefault].
        apply Nat.ltb_lt in Hdefault.
        destruct (jump_total Hlaws p (nth i ns n) st) as [st' Heffect].
        destruct (resume_total (nth i ns n) k st'
          (nth_label_bound ns n i (label_count k) Hall Hdefault)) as [m Hresume].
        left; exists [], m; eapply step_jump_table; eassumption.
      * right; right; left; cbn; rewrite Hsub; exact Hguard.
  - destruct k as [|f k].
    + inversion Hvalid; subst; right; left; exact I.
    + left; destruct f; eexists [], _; constructor.
Qed.

Lemma step_not_trapped {A G St O} (prog : stmt A G) (C : skeleton_client A G St O)
    m l m' : skeleton_client_laws C -> skel_step prog C m l m' ->
  ~ trapped (skeleton_endings prog C) m.
Proof.
  intros Hlaws Hstep; destruct Hstep; cbn [skeleton_endings trapped].
  all: try match goal with
  | Hsub : sub _ _ = Some _ |- _ => rewrite Hsub
  end.
  all: cbn; try tauto; try congruence.
  intro Htrap; eapply (atom_trap_halts Hlaws _ _ Htrap); eauto.
Qed.

Lemma step_not_stopped {A G St O} (prog : stmt A G) (C : skeleton_client A G St O)
    m l m' : skeleton_client_laws C -> skel_step prog C m l m' ->
  ~ stopped (skeleton_endings prog C) m.
Proof.
  intros Hlaws Hstep; destruct Hstep; cbn [skeleton_endings stopped].
  all: try match goal with
  | Hsub : sub _ _ = Some _ |- _ => rewrite Hsub
  end.
  all: cbn; try tauto.
  intro Hstop; eapply (atom_stop_halts Hlaws _ _ Hstop); eauto.
Qed.

(** The skeleton's final, trapped and stopped states halt and have disjoint endings. *)
Theorem skeleton_endings_wf {A G St O} (prog : stmt A G)
    (C : skeleton_client A G St O) :
  skeleton_client_laws C -> endings_wf (skeleton_semantics prog C) (skeleton_endings prog C).
Proof.
  intro Hlaws; constructor.
  - intros [p k st|p k st] Hfinal [l [m Hstep]]; [exact Hfinal|].
    destruct p, k; cbn in Hfinal; try contradiction; inversion Hstep.
  - intros m Htrap [l [m' Hstep]]; exact (step_not_trapped prog C m l m' Hlaws Hstep Htrap).
  - intros m Hstop [l [m' Hstep]]; exact (step_not_stopped prog C m l m' Hlaws Hstep Hstop).
  - intros [p k st|p k st]; cbn; tauto.
  - intros [p k st|p k st]; cbn; tauto.
  - intros [p k st|p k st]; cbn; [|tauto].
    destruct (sub prog p) as [s|]; [destruct s|]; cbn; try tauto.
    intros Htrap Hstop; exact (atom_trap_not_stop Hlaws _ _ (conj Htrap Hstop)).
Qed.

(** Well-labelled programs and lawful clients never reach a stuck machine state. *)
Theorem skeleton_not_stuck {A G St O} (prog : stmt A G) (C : skeleton_client A G St O) :
  labels_ok 0 prog = true -> skeleton_client_laws C ->
  forall m, reachable_state (skeleton_semantics prog C) m ->
    ~ stuck (skeleton_semantics prog C) (skeleton_endings prog C) m.
Proof.
  intros Hlabels Hlaws m Hreachable Hstuck.
  destruct (machine_progress prog C m Hlabels Hlaws
    (reachable_machine_valid prog C m Hreachable)) as [Hrun|[Hfinal|[Htrap|Hstop]]];
    unfold stuck in Hstuck; tauto.
Qed.
