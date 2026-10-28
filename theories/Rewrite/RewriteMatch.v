(** * Indexed first-order pattern matching

    Matching follows a finite pattern while recording canonical classes for its holes.
    For example, two occurrences of one hole must select the same canonical child class.
    Builds on: CollectionsMap, RewriteSyntax, RewriteEgraph and RewriteIndex. *)

From Stdlib Require Import List Bool PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Rewrite Require Import RewriteSyntax RewriteEgraph RewriteIndex.
Import List.ListNotations.

(** Hole enumeration retains repetitions and the left-to-right order of children. *)
Fixpoint rwp_holes {K Sort V H} (p : rw_pattern K Sort V H) : list H :=
  match p with
  | RWHole _ h => [h]
  | RWPVar _ _ => []
  | RWPApp _ _ ps => flat_map rwp_holes ps
  end.

(** Assignments are finite maps to canonical class identifiers. *)
Definition rw_assignment (H : Type) := Map.t H rw_id.

(** Coverage supplies a represented finite term for every occurring hole. *)
Definition rw_covers {K Sort V H} (EH : encoding H) (g : rw_graph K Sort V)
    (p : rw_pattern K Sort V H) (a : rw_assignment H)
    (sub : rw_substitution K Sort V H) : Prop :=
  forall h, In h (rwp_holes p) ->
    exists c t, Map.get EH h a = Some c /\ sub h = Some t /\ rw_represents g c t.

Definition rw_key_eq_dec {A} (E : encoding A) (x y : A) : {x = y} + {x <> y}.
Proof.
  destruct (Pos.eq_dec (encode E x) (encode E y)) as [Heq|Hne].
  - left; exact (encode_injective E x y Heq).
  - right; intro Heq; apply Hne; now subst y.
Defined.

(** Extensions preserve every existing binding, including repeated-hole choices. *)
Definition rw_assignment_extends {H} (EH : encoding H) (a b : rw_assignment H) : Prop :=
  forall h c, Map.get EH h a = Some c -> Map.get EH h b = Some c.

Lemma rw_assignment_extends_refl {H} (EH : encoding H) (a : rw_assignment H) :
  rw_assignment_extends EH a a.
Proof.
  intros h c Hget; exact Hget.
Qed.

Lemma rw_assignment_extends_trans {H} (EH : encoding H) (a b c : rw_assignment H) :
  rw_assignment_extends EH a b -> rw_assignment_extends EH b c ->
  rw_assignment_extends EH a c.
Proof.
  intros Hab Hbc h id Hget; apply Hbc, Hab; exact Hget.
Qed.

(** A hole either adds a canonical binding or checks its previous canonical choice. *)
Definition rw_bind {H} (EH : encoding H) (h : H) (root : rw_id)
    (a : rw_assignment H) : list (rw_assignment H) :=
  match Map.get EH h a with
  | Some old => if Pos.eq_dec old root then [a] else []
  | None => [Map.set EH h root a]
  end.

Lemma rw_bind_spec {H} (EH : encoding H) h root (a b : rw_assignment H) :
  In b (rw_bind EH h root a) ->
  rw_assignment_extends EH a b /\ Map.get EH h b = Some root /\
  (Map.wf EH a -> Map.wf EH b) /\
  (forall j c, Map.get EH j b = Some c ->
    Map.get EH j a = Some c \/ j = h).
Proof.
  unfold rw_bind; destruct (Map.get EH h a) as [old|] eqn:Hget.
  - destruct (Pos.eq_dec old root) as [->|Hne]; cbn; [|contradiction].
    intros [<-|Hfalse]; [|contradiction]; split; [apply rw_assignment_extends_refl|].
    split; [exact Hget|]; split; [auto|intros; auto].
  - cbn; intros [<-|Hfalse]; [|contradiction]; split.
    + intros j c Hbound; destruct (rw_key_eq_dec EH j h) as [->|Hne].
      * congruence.
      * rewrite Map.get_set_other by exact Hne; exact Hbound.
    + split; [apply Map.get_set_same|]; split; [apply Map.wf_set|].
      intros j c Hbound; destruct (rw_key_eq_dec EH j h) as [->|Hne]; [auto|].
      left; rewrite Map.get_set_other in Hbound by exact Hne; exact Hbound.
Qed.

(** Variable buckets are prepared once, separately from the operator incidence index. *)
Definition rw_variable_keys {K Sort V} (node : rw_node K Sort V) : list V :=
  match node with
  | RWNVar _ v => [v]
  | RWNApp _ _ _ => []
  end.

(** A bound first-child hole narrows the search to its indexed parents. *)
Definition rw_match_candidates {K Sort V H} (EK : encoding K) (EH : encoding H)
    (g : rw_graph K Sort V) (ix : rw_index K) (op : K)
    (ps : list (rw_pattern K Sort V H)) (a : rw_assignment H) : list rw_id :=
  match ps with
  | RWHole _ h :: _ =>
    match Map.get EH h a with
    | Some c => rw_parent_nodes g ix c
    | None => rw_lookup_list EK op (rw_index_ops ix)
    end
  | _ => rw_lookup_list EK op (rw_index_ops ix)
  end.

(** Candidate ownership compares resolved class identifiers and rejects missing classes. *)
Definition rw_same_class {K Sort V} (g : rw_graph K Sort V) (a b : rw_id) : bool :=
  match rw_find g a, rw_find g b with
  | Some ra, Some rb => Pos.eqb ra rb
  | _, _ => false
  end.

Lemma rw_same_class_spec {K Sort V} (g : rw_graph K Sort V) a b :
  rw_same_class g a b = true <-> exists root,
    rw_find g a = Some root /\ rw_find g b = Some root.
Proof.
  unfold rw_same_class; destruct (rw_find g a) as [ra|] eqn:Ha;
    destruct (rw_find g b) as [rb|] eqn:Hb; cbn; split; try discriminate;
    try (intros [r [Hr Hs]]; congruence).
  - intro Heq; apply Pos.eqb_eq in Heq; subst rb; eauto.
  - intros [r [Hr Hs]]; injection Hr as <-; injection Hs as <-; apply Pos.eqb_refl.
Qed.

(** Sequential child matching carries all earlier hole bindings into the next child. *)
Fixpoint rw_match_children {H} (fs : list (rw_id -> rw_assignment H -> list (rw_assignment H)))
    (ids : list rw_id) (a : rw_assignment H) : list (rw_assignment H) :=
  match fs, ids with
  | [], [] => [a]
  | f :: fs, id :: ids => flat_map (rw_match_children fs ids) (f id a)
  | _, _ => []
  end.

(** Recursive matching descends through the pattern, so graph cycles need no fuel. *)
Fixpoint rw_match_on {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (g : rw_graph K Sort V) (ix : rw_index K)
    (vars : Map.t V (list rw_id)) (p : rw_pattern K Sort V H)
    (root : rw_id) (a : rw_assignment H) {struct p} : list (rw_assignment H) :=
  match p with
  | RWHole s h =>
    match rw_find g root, rw_class_sort g root with
    | Some canonical, Some ty =>
      if rw_key_eq_dec ES s ty then rw_bind EH h canonical a else []
    | _, _ => []
    end
  | RWPVar s v =>
    flat_map (fun n =>
      match rw_node_at g n with
      | Some (owner, RWNVar ty w) =>
        if rw_key_eq_dec ES s ty then
          if rw_key_eq_dec EV v w then
            if rw_same_class g root owner then [a] else []
          else []
        else []
      | _ => []
      end) (rw_lookup_list EV v vars)
  | RWPApp s op ps =>
    flat_map (fun n =>
      match rw_node_at g n with
      | Some (owner, RWNApp ty other ids) =>
        if rw_key_eq_dec ES s ty then
          if rw_key_eq_dec EK op other then
            if rw_same_class g root owner then
              rw_match_children (map (rw_match_on EK ES EV EH g ix vars) ps) ids a
            else []
          else []
        else []
      | _ => []
      end) (rw_match_candidates EK EH g ix op ps a)
  end.

(** A structural match records graph nodes and canonical hole bindings independently of search. *)
Inductive rw_matches {K Sort V H} (EH : encoding H) (g : rw_graph K Sort V)
    (a : rw_assignment H) : rw_pattern K Sort V H -> rw_id -> Prop :=
  | rw_matches_hole : forall s h c canonical,
      rw_find g c = Some canonical -> rw_class_sort g c = Some s ->
      Map.get EH h a = Some canonical -> rw_matches EH g a (RWHole s h) c
  | rw_matches_var : forall s v c,
      rw_represents g c (RWVar s v) -> rw_matches EH g a (RWPVar s v) c
  | rw_matches_app : forall s op ps c n owner canonical ids,
      rw_node_at g n = Some (owner, RWNApp s op ids) ->
      rw_find g owner = Some canonical -> rw_find g c = Some canonical ->
      Forall2 (rw_matches EH g a) ps ids -> rw_matches EH g a (RWPApp s op ps) c.

Lemma rw_matches_extends {K Sort V H} (EH : encoding H) (g : rw_graph K Sort V)
    (a b : rw_assignment H) p root :
  rw_assignment_extends EH a b -> rw_matches EH g a p root -> rw_matches EH g b p root.
Proof.
  intros Hext Hmatch; revert p root Hmatch.
  fix IH 3; intros p root Hmatch.
  destruct Hmatch as [s h c canonical Hfind Hsort Hget|s v c Hrepr|
    s op ps c n owner canonical ids Hnode Howner Hfind Hargs].
  - eapply rw_matches_hole; [exact Hfind|exact Hsort|apply Hext; exact Hget].
  - apply rw_matches_var; exact Hrepr.
  - eapply rw_matches_app; [exact Hnode|exact Howner|exact Hfind|].
    clear Hnode Howner Hfind.
    induction Hargs as [|p id ps ids Hhead Htail IHtail].
    + constructor.
    + constructor; [apply IH; exact Hhead|exact IHtail].
Qed.

(** Every successful binding retains its input and adds only holes in this pattern. *)
Definition rw_match_output {K Sort V H} (EH : encoding H) (g : rw_graph K Sort V)
    (p : rw_pattern K Sort V H) root (a b : rw_assignment H) : Prop :=
  rw_assignment_extends EH a b /\ rw_matches EH g b p root /\
  (Map.wf EH a -> Map.wf EH b) /\
  forall h c, Map.get EH h b = Some c -> Map.get EH h a = Some c \/ In h (rwp_holes p).

Lemma rw_match_children_sound {K Sort V H} (EH : encoding H) (g : rw_graph K Sort V)
    ps fs ids a b :
  Forall2 (fun p f => forall root a b, In b (f root a) ->
    rw_match_output EH g p root a b) ps fs ->
  In b (rw_match_children fs ids a) ->
  rw_assignment_extends EH a b /\ Forall2 (rw_matches EH g b) ps ids /\
  (Map.wf EH a -> Map.wf EH b) /\
  (forall h c, Map.get EH h b = Some c ->
    Map.get EH h a = Some c \/ In h (flat_map rwp_holes ps)).
Proof.
  intro Hfs; revert ids a b; induction Hfs as [|p f ps fs Hf Hfs IHfs];
    intros [|id ids] a b Hin; cbn [rw_match_children] in Hin; try contradiction.
  - destruct Hin as [<-|Hfalse]; [|contradiction]; split.
    + apply rw_assignment_extends_refl.
    + split; [constructor|]; split; [auto|intros; auto].
  - apply in_flat_map in Hin; destruct Hin as [mid [Hhead Htail]].
    destruct (Hf id a mid Hhead) as [Ham [Hmatch [Hwf Hdom]]].
    destruct (IHfs ids mid b Htail) as [Hmb [Hargs [Hwf' Hdom']]].
    split; [eapply rw_assignment_extends_trans; eauto|]; split.
    + constructor; [eapply rw_matches_extends; eauto|exact Hargs].
    + split; [auto|]; intros h c Hget.
      destruct (Hdom' h c Hget) as [Hmid|Hin]; [|right; apply in_or_app; auto].
      destruct (Hdom h c Hmid) as [Hold|Hin]; [auto|right; apply in_or_app; auto].
Qed.

Lemma rw_match_on_sound {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (g : rw_graph K Sort V) ix vars p :
  forall root a b, In b (rw_match_on EK ES EV EH g ix vars p root a) ->
    rw_match_output EH g p root a b.
Proof.
  induction p as [s h|s v|s op ps IHps]; intros root a b Hin.
  - cbn [rw_match_on] in Hin.
    destruct (rw_find g root) as [canonical|] eqn:Hfind;
      destruct (rw_class_sort g root) as [ty|] eqn:Hsort; try contradiction.
    destruct (rw_key_eq_dec ES s ty) as [->|Hne]; [|contradiction].
    destruct (rw_bind_spec EH h canonical a b Hin) as [Hext [Hget [Hwf Hdom]]].
    split; [exact Hext|]; split.
    + eapply rw_matches_hole; eauto.
    + split; [exact Hwf|]; intros j c Hj; destruct (Hdom j c Hj); cbn; auto.
  - cbn [rw_match_on] in Hin; apply in_flat_map in Hin.
    destruct Hin as [n [Hcandidate Hin]].
    destruct (rw_node_at g n) as [[owner [ty w|ty other ids]]|] eqn:Hnode;
      try contradiction.
    destruct (rw_key_eq_dec ES s ty) as [->|Hne]; [|contradiction].
    destruct (rw_key_eq_dec EV v w) as [->|Hne]; [|contradiction].
    destruct (rw_same_class g root owner) eqn:Hsame; [|contradiction].
    destruct Hin as [<-|Hfalse]; [|contradiction].
    apply rw_same_class_spec in Hsame; destruct Hsame as [canonical [Hroot Howner]].
    split; [apply rw_assignment_extends_refl|]; split.
    + apply rw_matches_var; eapply rw_repr_var; eauto.
    + split; [auto|intros; auto].
  - cbn [rw_match_on] in Hin; apply in_flat_map in Hin.
    destruct Hin as [n [Hcandidate Hin]].
    destruct (rw_node_at g n) as [[owner [ty w|ty other ids]]|] eqn:Hnode;
      try contradiction.
    destruct (rw_key_eq_dec ES s ty) as [->|Hne]; [|contradiction].
    destruct (rw_key_eq_dec EK op other) as [->|Hne]; [|contradiction].
    destruct (rw_same_class g root owner) eqn:Hsame; [|contradiction].
    apply rw_same_class_spec in Hsame; destruct Hsame as [canonical [Hroot Howner]].
    assert (Hfs : Forall2 (fun p f => forall root a b, In b (f root a) ->
      rw_match_output EH g p root a b) ps (map (rw_match_on EK ES EV EH g ix vars) ps)).
    { clear Hin Hcandidate; induction IHps as [|p Hp ps Hps IHps]; cbn.
      - constructor.
      - constructor; [exact Hp|exact IHps]. }
    destruct (rw_match_children_sound EH g ps _ ids a b Hfs Hin)
      as [Hext [Hargs [Hwf Hdom]]].
    split; [exact Hext|]; split.
    + eapply rw_matches_app; eauto.
    + split; [exact Hwf|exact Hdom].
Qed.

(** * Semantic witnesses and completeness *)

Lemma rw_matches_sound {K Sort V H} (EH : encoding H) (sig : rw_signature K Sort V)
    (g : rw_graph K Sort V) a :
  rw_graph_wf sig g -> forall p root, rw_matches EH g a p root -> forall sub t,
  rw_covers EH g p a sub -> rw_instantiate sub p = Some t -> rw_represents g root t.
Proof.
  intro Hwf; fix IH 3; intros p root Hmatch sub t Hcover Hinst.
  destruct Hmatch as [s h root canonical Hfind Hsort Hget|s v root Hrepr|
    s op ps root n owner canonical ids Hnode Howner Hfind Hargs].
  - destruct (Hcover h (or_introl eq_refl)) as [c [u [Hbound [Hsub Hrepr]]]].
    cbn [rw_instantiate] in Hinst; assert (c = canonical) by congruence; subst c.
    assert (u = t) by congruence; subst u.
    eapply rw_represents_alias; [|exact Hrepr].
    rewrite Hfind.
    exact (proj1 (proj2 (rw_layout_find sig g (rw_wf_layout sig g Hwf) _ _ Hfind))).
  - cbn [rw_instantiate] in Hinst; injection Hinst as <-; exact Hrepr.
  - rewrite rw_instantiate_app in Hinst.
    destruct (rw_instantiate_args sub ps) as [ts|] eqn:Hinsts; [|discriminate].
    injection Hinst as <-; eapply rw_repr_app; [exact Hnode|exact Howner|exact Hfind|].
    clear Hnode Howner Hfind.
    change (forall h, In h (flat_map rwp_holes ps) ->
      exists c t, Map.get EH h a = Some c /\ sub h = Some t /\ rw_represents g c t) in Hcover.
    revert ts Hinsts Hcover; induction Hargs as [|p id ps ids Hhead Htail IHtail];
      intros ts Hinsts Hcover.
    + cbn [rw_instantiate_args] in Hinsts; injection Hinsts as <-; constructor.
    + change (match rw_instantiate sub p with
        | None => None
        | Some u => match rw_instantiate_args sub ps with
          | None => None
          | Some us => Some (u :: us)
          end
        end = Some ts) in Hinsts.
      destruct (rw_instantiate sub p) as [u|] eqn:Hinst; [|discriminate].
      destruct (rw_instantiate_args sub ps) as [us|] eqn:Hrest; [|discriminate].
      injection Hinsts as <-; constructor.
      * eapply (IH p id Hhead sub u); [|exact Hinst].
        intros h Hin; apply Hcover; cbn; apply in_or_app; auto.
      * apply IHtail; [reflexivity|].
        intros h Hin; apply Hcover; cbn; apply in_or_app; auto.
Qed.

Lemma rw_matches_holes {K Sort V H} (EH : encoding H) (sig : rw_signature K Sort V)
    (g : rw_graph K Sort V) a :
  rw_graph_wf sig g -> forall p root, rw_matches EH g a p root ->
  forall h, In h (rwp_holes p) ->
  exists c, Map.get EH h a = Some c /\ rw_find g c = Some c.
Proof.
  intro Hwf; fix IH 3; intros p root Hmatch h Hin.
  destruct Hmatch as [s j root canonical Hfind Hsort Hget|s v root Hrepr|
    s op ps root n owner canonical ids Hnode Howner Hfind Hargs].
  - cbn in Hin; destruct Hin as [<-|Hfalse]; [|contradiction].
    exists canonical; split; [exact Hget|].
    exact (proj1 (proj2 (rw_layout_find sig g (rw_wf_layout sig g Hwf) _ _ Hfind))).
  - contradiction.
  - cbn in Hin; apply in_flat_map in Hin; destruct Hin as [p [Hp Hin]].
    clear Hnode Howner Hfind.
    induction Hargs as [|q id ps ids Hhead Htail IHtail]; [contradiction|].
    destruct Hp as [<-|Hp]; [eapply IH; eauto|apply IHtail; exact Hp].
Qed.

(** A witness model couples every stored canonical class to this exact substitution. *)
Definition rw_assignment_model {K Sort V H} (EH : encoding H) (g : rw_graph K Sort V)
    (sub : rw_substitution K Sort V H) (a : rw_assignment H) : Prop :=
  Map.wf EH a /\ forall h c, Map.get EH h a = Some c ->
    rw_find g c = Some c /\ exists t, sub h = Some t /\ rw_represents g c t.

Lemma rw_assignment_model_empty {K Sort V H} (EH : encoding H) (g : rw_graph K Sort V)
    (sub : rw_substitution K Sort V H) : rw_assignment_model EH g sub Map.empty.
Proof.
  split; [apply Map.wf_empty|]; intros h c Hget; rewrite Map.get_empty in Hget; discriminate.
Qed.

Lemma rw_bind_complete {K Sort V H} (EH : encoding H) (sig : rw_signature K Sort V)
    (g : rw_graph K Sort V) sub a h root canonical t :
  rw_graph_wf sig g -> rw_clean g -> rw_assignment_model EH g sub a ->
  sub h = Some t -> rw_represents g root t -> rw_find g root = Some canonical ->
  exists b, In b (rw_bind EH h canonical a) /\ rw_assignment_model EH g sub b.
Proof.
  intros Hwf Hclean [Hmap Hmodel] Hsub Hrepr Hfind.
  unfold rw_bind; destruct (Map.get EH h a) as [old|] eqn:Hget.
  - destruct (Hmodel h old Hget) as [Hold [u [Hsubu Hrepru]]].
    assert (u = t) by congruence; subst u.
    assert (Heq : old = canonical).
    { pose proof (Hclean old root t Hrepru Hrepr) as Hsame; congruence. }
    subst old; destruct (Pos.eq_dec canonical canonical) as [Heq|Hne]; [|contradiction].
    exists a; split; [cbn; auto|]; split; assumption.
  - exists (Map.set EH h canonical a); split; [cbn; auto|]; split.
    + apply Map.wf_set; exact Hmap.
    + intros j c Hbound; destruct (rw_key_eq_dec EH j h) as [->|Hne].
      * rewrite Map.get_set_same in Hbound; injection Hbound as <-; split.
        -- exact (proj1 (proj2 (rw_layout_find sig g (rw_wf_layout sig g Hwf) _ _ Hfind))).
        -- exists t; split; [exact Hsub|].
           eapply rw_represents_alias; [|exact Hrepr].
           exact (eq_trans Hfind
             (eq_sym (proj1 (proj2
               (rw_layout_find sig g (rw_wf_layout sig g Hwf) _ _ Hfind))))).
      * rewrite Map.get_set_other in Hbound by exact Hne; apply Hmodel; exact Hbound.
Qed.

Lemma rw_operator_candidate {K Sort V} (EK : encoding K) (g : rw_graph K Sort V)
    ix n owner s op ids :
  rw_index_agrees EK g ix -> rw_node_at g n = Some (owner, RWNApp s op ids) ->
  In n (rw_lookup_list EK op (rw_index_ops ix)).
Proof.
  intros [_ [_ [_ [_ [_ [_ [Hops _]]]]]]] Hnode; apply Hops; eauto.
Qed.

Lemma rw_match_candidates_complete {K Sort V H} (EK : encoding K) (EH : encoding H)
    (g : rw_graph K Sort V) ix sub a n owner s op ps ids ts :
  rw_clean g -> rw_index_agrees EK g ix -> rw_assignment_model EH g sub a ->
  rw_node_at g n = Some (owner, RWNApp s op ids) ->
  rw_instantiate_args sub ps = Some ts -> Forall2 (rw_represents g) ids ts ->
  In n (rw_match_candidates EK EH g ix op ps a).
Proof.
  intros Hclean Hix [Hmap Hmodel] Hnode Hinst Hrepr.
  unfold rw_match_candidates; destruct ps as [|[ty h|ty v|ty other children] ps];
    try (eapply rw_operator_candidate; eauto).
  destruct (Map.get EH h a) as [c|] eqn:Hget; [|eapply rw_operator_candidate; eauto].
  change (match sub h with
    | None => None
    | Some t => match rw_instantiate_args sub ps with
      | None => None
      | Some rest => Some (t :: rest)
      end
    end = Some ts) in Hinst.
  destruct (sub h) as [t|] eqn:Hsub; [|discriminate].
  destruct (rw_instantiate_args sub ps) as [rest|] eqn:Hrest; [|discriminate].
  injection Hinst as <-; inversion Hrepr as [|child u children us Hchild Hchildren]; subst.
  destruct (Hmodel h c Hget) as [Hfind [u [Hsubu Hrepru]]].
  assert (u = t) by congruence; subst u.
  assert (Hchildfind : rw_find g child = Some c).
  { rewrite <- (Hclean c child t Hrepru Hchild); exact Hfind. }
  apply (proj2 (rw_parent_nodes_agree EK g ix c n Hix)).
  exists c, owner, s, op, (child :: children), child.
  split; [exact Hfind|]; split; [exact Hchildfind|]; split; [exact Hnode|cbn; auto].
Qed.

Lemma rw_match_children_complete {K Sort V H} (EH : encoding H) (g : rw_graph K Sort V)
    sub ps fs :
  Forall2 (fun p f => forall root t a, rw_instantiate sub p = Some t ->
    rw_represents g root t -> rw_assignment_model EH g sub a ->
    exists b, In b (f root a) /\ rw_assignment_model EH g sub b) ps fs ->
  forall ids ts a, rw_instantiate_args sub ps = Some ts ->
  Forall2 (rw_represents g) ids ts -> rw_assignment_model EH g sub a ->
  exists b, In b (rw_match_children fs ids a) /\ rw_assignment_model EH g sub b.
Proof.
  intro Hfs; induction Hfs as [|p f ps fs Hf Hfs IHfs]; intros ids ts a Hinst Hrepr Hmodel.
  - cbn [rw_instantiate_args] in Hinst; injection Hinst as <-.
    inversion Hrepr; subst; exists a; split; [cbn; auto|exact Hmodel].
  - change (match rw_instantiate sub p with
      | None => None
      | Some t => match rw_instantiate_args sub ps with
        | None => None
        | Some ts => Some (t :: ts)
        end
      end = Some ts) in Hinst.
    destruct (rw_instantiate sub p) as [t|] eqn:Hhead; [|discriminate].
    destruct (rw_instantiate_args sub ps) as [rest|] eqn:Hrest; [|discriminate].
    injection Hinst as <-; inversion Hrepr as [|id u children us Hchild Hchildren]; subst.
    destruct (Hf id t a eq_refl Hchild Hmodel) as [mid [Hmid Hmodelmid]].
    destruct (IHfs children rest mid eq_refl Hchildren Hmodelmid) as [b [Hb Hmodelb]].
    exists b; split; [|exact Hmodelb]; cbn [rw_match_children].
    apply in_flat_map; exists mid; auto.
Qed.

Lemma rw_match_on_complete {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (g : rw_graph K Sort V) ix vars sub :
  rw_graph_wf sig g -> rw_clean g -> rw_index_agrees EK g ix ->
  rw_table_incidence EV g rw_variable_keys vars ->
  forall p, rwp_typed sig (fun h => option_map rw_sort (sub h)) p ->
  forall root t a, rw_instantiate sub p = Some t -> rw_represents g root t ->
  rw_assignment_model EH g sub a ->
  exists b, In b (rw_match_on EK ES EV EH g ix vars p root a) /\
    rw_assignment_model EH g sub b.
Proof.
  intros Hwf Hclean Hix Hvars.
  apply (rwp_typed_ind_all sig (fun h => option_map rw_sort (sub h))
    (fun p => forall root t a, rw_instantiate sub p = Some t ->
      rw_represents g root t -> rw_assignment_model EH g sub a ->
      exists b, In b (rw_match_on EK ES EV EH g ix vars p root a) /\
        rw_assignment_model EH g sub b)).
  - intros s h Hsort root t a Hinst Hrepr Hmodel.
    cbn [rw_instantiate] in Hinst; rewrite Hinst in Hsort; cbn in Hsort.
    injection Hsort as Hsort.
    destruct (rw_represents_find g root t Hrepr) as [canonical Hfind].
    assert (Hclass : rw_class_sort g root = Some s).
    { rewrite <- Hsort; apply (rw_layout_represents_sort sig g _ _
        (rw_wf_layout sig g Hwf) Hrepr). }
    cbn [rw_match_on]; rewrite Hfind, Hclass.
    destruct (rw_key_eq_dec ES s s) as [Heq|Hne]; [|contradiction].
    eapply rw_bind_complete; eauto.
  - intros s v Hsort root t a Hinst Hrepr Hmodel.
    cbn [rw_instantiate] in Hinst; injection Hinst as <-.
    inversion Hrepr as [c n owner canonical s' v' Hnode Howner Hfind|]; subst.
    exists a; split; [|exact Hmodel]; cbn [rw_match_on]; apply in_flat_map; exists n; split.
    + apply (proj2 Hvars); exists owner, (RWNVar s v); split; [exact Hnode|cbn; auto].
    + rewrite Hnode.
      destruct (rw_key_eq_dec ES s s) as [Heq|Hne]; [|contradiction].
      destruct (rw_key_eq_dec EV v v) as [Heq'|Hne]; [|contradiction].
      assert (Hsame : rw_same_class g root owner = true).
      { apply rw_same_class_spec; exists canonical; auto. }
      rewrite Hsame; cbn; auto.
  - intros s op ps Htyped IHps Hshape root t a Hinst Hrepr Hmodel.
    rewrite rw_instantiate_app in Hinst.
    destruct (rw_instantiate_args sub ps) as [ts|] eqn:Hinsts; [|discriminate].
    injection Hinst as <-.
    inversion Hrepr as [|c n owner canonical s' op' ids ts' Hnode Howner Hfind Hargs]; subst.
    assert (Hfs : Forall2 (fun p f => forall root t a, rw_instantiate sub p = Some t ->
      rw_represents g root t -> rw_assignment_model EH g sub a ->
      exists b, In b (f root a) /\ rw_assignment_model EH g sub b)
      ps (map (rw_match_on EK ES EV EH g ix vars) ps)).
    { clear Hinsts Htyped Hshape; induction IHps as [|p ps Hp Hps IHps]; cbn.
      - constructor.
      - constructor; assumption. }
    destruct (rw_match_children_complete EH g sub ps _ Hfs ids ts a Hinsts Hargs Hmodel)
      as [b [Hb Hmodelb]].
    exists b; split; [|exact Hmodelb]; cbn [rw_match_on]; apply in_flat_map; exists n; split.
    + eapply rw_match_candidates_complete; eauto.
    + rewrite Hnode.
      destruct (rw_key_eq_dec ES s s) as [Heq|Hne]; [|contradiction].
      destruct (rw_key_eq_dec EK op op) as [Heq'|Hne]; [|contradiction].
      assert (Hsame : rw_same_class g root owner = true).
      { apply rw_same_class_spec; exists canonical; auto. }
      rewrite Hsame; exact Hb.
Qed.

(** * Duplicate-free finite results *)

Lemma rw_assignment_elements_injective {H} (EH : encoding H) (a b : rw_assignment H) :
  Map.wf EH a -> Map.wf EH b -> Map.elements a = Map.elements b -> a = b.
Proof.
  intros Ha Hb Helements; apply (Map.extensionality EH a b Ha Hb); intro h.
  destruct (Map.get EH h a) as [c|] eqn:Hget.
  - symmetry; apply Map.elements_sound; [exact Hb|].
    rewrite <- Helements; apply (Map.elements_complete EH); assumption.
  - destruct (Map.get EH h b) as [c|] eqn:Hother; [|reflexivity].
    assert (Hbound : Map.get EH h a = Some c).
    { apply Map.elements_sound; [exact Ha|]; rewrite Helements.
      apply (Map.elements_complete EH); assumption. }
    congruence.
Qed.

Definition rw_assignment_key_encoding {H} (EH : encoding H) :=
  list_encoding (pair_encoding EH positive_encoding).

(** A trie keyed by canonical binding lists removes duplicate search derivations. *)
Fixpoint rw_assignment_table {H} (EH : encoding H) (results : list (rw_assignment H)) :
    Map.t (list (H * rw_id)) (rw_assignment H) :=
  match results with
  | [] => Map.empty
  | a :: rest => Map.set (rw_assignment_key_encoding EH) (Map.elements a) a
      (rw_assignment_table EH rest)
  end.

Lemma rw_assignment_table_wf {H} (EH : encoding H) results :
  Map.wf (rw_assignment_key_encoding EH) (rw_assignment_table EH results).
Proof.
  induction results as [|a rest IHrest]; cbn [rw_assignment_table].
  - apply Map.wf_empty.
  - apply Map.wf_set; exact IHrest.
Qed.

Lemma rw_assignment_table_sound {H} (EH : encoding H) results key a :
  Map.get (rw_assignment_key_encoding EH) key (rw_assignment_table EH results) = Some a ->
  In a results /\ key = Map.elements a.
Proof.
  induction results as [|b rest IHrest]; cbn [rw_assignment_table].
  - rewrite Map.get_empty; discriminate.
  - destruct (rw_key_eq_dec (rw_assignment_key_encoding EH) key (Map.elements b))
      as [->|Hne].
    + rewrite Map.get_set_same; intro Heq; injection Heq as <-; split; [cbn; auto|reflexivity].
    + rewrite Map.get_set_other by exact Hne; intro Hget.
      destruct (IHrest Hget) as [Hin Heq]; split; [cbn; auto|exact Heq].
Qed.

Lemma rw_assignment_table_complete {H} (EH : encoding H) results a :
  Forall (Map.wf EH) results -> In a results ->
  Map.get (rw_assignment_key_encoding EH) (Map.elements a)
    (rw_assignment_table EH results) = Some a.
Proof.
  intros Hwf Hin; induction Hwf as [|b rest Hb Hrest IHrest]; [contradiction|].
  cbn [rw_assignment_table]; destruct Hin as [<-|Hin]; [apply Map.get_set_same|].
  destruct (rw_key_eq_dec (rw_assignment_key_encoding EH) (Map.elements a) (Map.elements b))
    as [Heq|Hne].
  - assert (Ha : Map.wf EH a) by (rewrite Forall_forall in Hrest; apply Hrest; exact Hin).
    assert (a = b) by (eapply rw_assignment_elements_injective; eauto).
    subst b; apply Map.get_set_same.
  - rewrite Map.get_set_other by exact Hne; apply IHrest; exact Hin.
Qed.

Definition rw_distinct_assignments {H} (EH : encoding H) (results : list (rw_assignment H)) :=
  map snd (Map.elements (rw_assignment_table EH results)).

Lemma rw_distinct_assignments_in {H} (EH : encoding H) results a :
  Forall (Map.wf EH) results -> (In a (rw_distinct_assignments EH results) <-> In a results).
Proof.
  intro Hwf; unfold rw_distinct_assignments; split.
  - intro Hin; apply in_map_iff in Hin; destruct Hin as [[key b] [Heq Hin]]; cbn in Heq.
    subst b; apply (Map.elements_sound (rw_assignment_key_encoding EH)) in Hin;
      [|apply rw_assignment_table_wf].
    exact (proj1 (rw_assignment_table_sound EH results key a Hin)).
  - intro Hin; apply in_map_iff; exists (Map.elements a, a); split; [reflexivity|].
    apply (Map.elements_complete (rw_assignment_key_encoding EH));
      [apply rw_assignment_table_wf|].
    apply rw_assignment_table_complete; assumption.
Qed.

Lemma rw_keyed_values_nodup {A B} (key : B -> A) (entries : list (A * B)) :
  NoDup (map fst entries) -> (forall k b, In (k, b) entries -> k = key b) ->
  NoDup (map snd entries).
Proof.
  induction entries as [|[k b] entries IHentries]; cbn; intros Hnodup Hkey; [constructor|].
  inversion Hnodup as [|j keys Houtside Htail]; subst; constructor.
  - intro Hin; apply in_map_iff in Hin; destruct Hin as [[j c] [Heq Hin]]; cbn in Heq.
    subst c; apply Houtside; apply in_map_iff; exists (j, b); split; [|exact Hin].
    cbn; rewrite (Hkey j b (or_intror Hin)), (Hkey k b (or_introl eq_refl)); reflexivity.
  - apply IHentries; [exact Htail|]; intros j c Hin; apply Hkey; cbn; auto.
Qed.

Lemma rw_distinct_assignments_nodup {H} (EH : encoding H) results :
  NoDup (rw_distinct_assignments EH results).
Proof.
  unfold rw_distinct_assignments; apply (rw_keyed_values_nodup Map.elements).
  - apply (Map.elements_nodup (rw_assignment_key_encoding EH)); apply rw_assignment_table_wf.
  - intros key a Hin; apply (Map.elements_sound (rw_assignment_key_encoding EH)) in Hin;
      [|apply rw_assignment_table_wf].
    exact (proj2 (rw_assignment_table_sound EH results key a Hin)).
Qed.

(** * Public matcher and its contracts *)

Definition rw_match_raw {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (g : rw_graph K Sort V) root p : list (rw_assignment H) :=
  rw_match_on EK ES EV EH g (rw_build_index EK g)
    (rw_build_table EV g rw_variable_keys) p root Map.empty.

Lemma rw_match_raw_output {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (g : rw_graph K Sort V) root p a :
  In a (rw_match_raw EK ES EV EH g root p) -> rw_match_output EH g p root Map.empty a.
Proof.
  apply rw_match_on_sound.
Qed.

(** Matching returns each finite canonical hole assignment once, using prepared incidence tables. *)
Definition rw_match {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (g : rw_graph K Sort V) (root : rw_id) (p : rw_pattern K Sort V H) :
    list (rw_assignment H) :=
  rw_distinct_assignments EH (rw_match_raw EK ES EV EH g root p).

Lemma rw_match_in {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (g : rw_graph K Sort V) root p a :
  In a (rw_match EK ES EV EH g root p) <-> In a (rw_match_raw EK ES EV EH g root p).
Proof.
  apply rw_distinct_assignments_in; rewrite Forall_forall; intros b Hin.
  destruct (rw_match_raw_output EK ES EV EH g root p b Hin) as [_ [_ [Hwf _]]].
  apply Hwf; apply Map.wf_empty.
Qed.

(** Any covered instantiation of a returned match is represented at the requested class. *)
Theorem rw_match_sound {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (g : rw_graph K Sort V)
    (root : rw_id) (p : rw_pattern K Sort V H) (a : rw_assignment H)
    (sub : rw_substitution K Sort V H) (t : rw_term K Sort V) :
  rw_graph_wf sig g -> In a (rw_match EK ES EV EH g root p) -> rw_covers EH g p a sub ->
  rw_instantiate sub p = Some t -> rw_represents g root t.
Proof.
  intros Hwf Hin Hcover Hinst; apply rw_match_in in Hin.
  destruct (rw_match_raw_output EK ES EV EH g root p a Hin) as [_ [Hmatch _]].
  eapply rw_matches_sound; eauto.
Qed.

(** A represented, sort-respecting instantiation occurs among the matches of a clean graph. *)
Theorem rw_match_complete {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V) (g : rw_graph K Sort V)
    (root : rw_id) (p : rw_pattern K Sort V H) (sub : rw_substitution K Sort V H)
    (t : rw_term K Sort V) :
  rw_graph_wf sig g -> rw_clean g ->
  rwp_typed sig (fun h => option_map rw_sort (sub h)) p ->
  rw_instantiate sub p = Some t -> rw_represents g root t ->
  exists a, In a (rw_match EK ES EV EH g root p) /\ rw_covers EH g p a sub.
Proof.
  intros Hwf Hclean Htyped Hinst Hrepr.
  destruct (rw_match_on_complete EK ES EV EH sig g (rw_build_index EK g)
    (rw_build_table EV g rw_variable_keys) sub Hwf Hclean
    (rw_build_index_agrees EK sig g Hwf) (rw_build_table_correct EV sig g _ Hwf)
    p Htyped root t Map.empty Hinst Hrepr (rw_assignment_model_empty EH g sub))
    as [a [Hin [Hmap Hmodel]]].
  change (In a (rw_match_raw EK ES EV EH g root p)) in Hin.
  destruct (rw_match_raw_output EK ES EV EH g root p a Hin) as [_ [Hmatch _]].
  exists a; split; [apply rw_match_in; exact Hin|].
  intros h Hhole; destruct (rw_matches_holes EH sig g a Hwf p root Hmatch h Hhole)
    as [c [Hget Hfind]].
  destruct (Hmodel h c Hget) as [_ [u [Hsub Hrepru]]]; exists c, u; auto.
Qed.

(** Returned assignments are well-formed finite maps. *)
Theorem rw_match_assignment_wf {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (g : rw_graph K Sort V) root p a :
  In a (rw_match EK ES EV EH g root p) -> Map.wf EH a.
Proof.
  intro Hin; apply rw_match_in in Hin.
  destruct (rw_match_raw_output EK ES EV EH g root p a Hin) as [_ [_ [Hwf _]]].
  apply Hwf; apply Map.wf_empty.
Qed.

(** A match binds exactly the holes that occur in the pattern. *)
Theorem rw_match_domain {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (g : rw_graph K Sort V) root p a :
  rw_graph_wf sig g -> In a (rw_match EK ES EV EH g root p) ->
  forall h, (exists c, Map.get EH h a = Some c) <-> In h (rwp_holes p).
Proof.
  intros Hwf Hin h; apply rw_match_in in Hin.
  destruct (rw_match_raw_output EK ES EV EH g root p a Hin) as [_ [Hmatch [_ Hdom]]].
  split.
  - intros [c Hget]; destruct (Hdom h c Hget) as [Hempty|Hhole]; [|exact Hhole].
    rewrite Map.get_empty in Hempty; discriminate.
  - intro Hhole; destruct (rw_matches_holes EH sig g a Hwf p root Hmatch h Hhole)
      as [c [Hget Hfind]]; eauto.
Qed.

(** Repeated holes use canonical identifiers, including when child edges retain aliases. *)
Theorem rw_match_canonical {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (g : rw_graph K Sort V) root p a :
  rw_graph_wf sig g -> In a (rw_match EK ES EV EH g root p) ->
  forall h c, Map.get EH h a = Some c -> rw_find g c = Some c.
Proof.
  intros Hwf Hin h c Hget.
  assert (Hhole : In h (rwp_holes p)).
  { apply (proj1 (rw_match_domain EK ES EV EH sig g root p a Hwf Hin h)); eauto. }
  apply rw_match_in in Hin.
  destruct (rw_match_raw_output EK ES EV EH g root p a Hin) as [_ [Hmatch _]].
  destruct (rw_matches_holes EH sig g a Hwf p root Hmatch h Hhole) as [d [Hbound Hfind]].
  assert (c = d) by congruence; subst d; exact Hfind.
Qed.

(** Distinct graph derivations never duplicate the same finite assignment in the result. *)
Theorem rw_match_nodup {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (g : rw_graph K Sort V) root p :
  NoDup (rw_match EK ES EV EH g root p).
Proof.
  apply rw_distinct_assignments_nodup.
Qed.
