(** * Flat tables with list keys

    Tables specialize maps to lists of positive numbers, including the empty list.
    For example, the keys [1] and [1; 2] denote independent bindings.
    Builds on: CollectionsEncoding, CollectionsMap. *)

From Stdlib Require Import List PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.

Module Table.

(** List keys use the shared injective encoding. *)
Definition key : encoding (list positive) := list_encoding positive_encoding.

(** A table is one flat map, with no prefix nodes. *)
Definition t (V : Type) : Type := Map.t (list positive) V.

(** Empty tables contain no binding. *)
Definition empty {V} : t V := Map.empty.

(** Stored keys occupy their encoded positions. *)
Definition wf {V} (t : t V) : Prop := Map.wf key t.

(** Lookup reads the complete list key. *)
Definition get {V} (k : list positive) (t : t V) : option V := Map.get key k t.

(** Setting replaces the binding at the complete list key. *)
Definition set {V} (k : list positive) (v : V) (t : t V) : Table.t V := Map.set key k v t.

(** Removing clears only the supplied complete key. *)
Definition remove {V} (k : list positive) (t : t V) : Table.t V := Map.remove key k t.

(** Emptiness uses the canonical map root. *)
Definition is_empty {V} (t : t V) : bool := Map.is_empty t.

(** Folding visits bindings in encoded trie order. *)
Definition fold {V B} (f : B -> list positive -> V -> B) (t : t V) (b : B) : B :=
  Map.fold f t b.

(** Enumeration retains the map's encoded trie order. *)
Definition elements {V} (t : t V) : list (list positive * V) := Map.elements t.

(** Size counts complete keys. *)
Definition size {V} (t : t V) : nat := Map.size t.

Section Laws.
Context {V : Type}.
Variables (t t' : Table.t V) (k k1 k2 : list positive) (v : V).

(** Empty tables bind no key. *)
Theorem get_empty : get k (@empty V) = None.
Proof.
  apply Map.get_empty.
Qed.

(** Setting a key makes its value readable. *)
Theorem get_set_same : get k (set k v t) = Some v.
Proof.
  apply Map.get_set_same.
Qed.

(** Setting another key preserves lookup. *)
Theorem get_set_other : k1 <> k2 -> get k1 (set k2 v t) = get k1 t.
Proof.
  apply Map.get_set_other.
Qed.

(** Removing a key makes its lookup fail. *)
Theorem get_remove_same : get k (remove k t) = None.
Proof.
  apply Map.get_remove_same.
Qed.

(** Removing another key preserves lookup. *)
Theorem get_remove_other : k1 <> k2 -> get k1 (remove k2 t) = get k1 t.
Proof.
  apply Map.get_remove_other.
Qed.

(** Empty tables satisfy the stored-key invariant. *)
Theorem wf_empty : wf (@empty V).
Proof.
  apply Map.wf_empty.
Qed.

(** Setting preserves the stored-key invariant. *)
Theorem wf_set : wf t -> wf (set k v t).
Proof.
  apply Map.wf_set.
Qed.

(** Removing preserves the stored-key invariant. *)
Theorem wf_remove : wf t -> wf (remove k t).
Proof.
  apply Map.wf_remove.
Qed.

(** Well-formed tables with identical lookups are equal. *)
Theorem extensionality :
  wf t -> wf t' -> (forall k, get k t = get k t') -> t = t'.
Proof.
  apply (Map.extensionality key).
Qed.

(** Every enumerated binding is readable. *)
Theorem elements_sound : wf t -> In (k, v) (elements t) -> get k t = Some v.
Proof.
  apply Map.elements_sound.
Qed.

(** Every readable binding occurs in the enumeration. *)
Theorem elements_complete : wf t -> get k t = Some v -> In (k, v) (elements t).
Proof.
  apply Map.elements_complete.
Qed.

(** A well-formed table enumerates each key once. *)
Theorem elements_nodup : wf t -> NoDup (List.map fst (elements t)).
Proof.
  apply Map.elements_nodup.
Qed.

(** Folding agrees with a left fold over the enumeration. *)
Theorem fold_elements : forall (B : Type) (f : B -> list positive -> V -> B) (b : B),
  fold f t b = List.fold_left (fun acc kv => f acc (fst kv) (snd kv)) (elements t) b.
Proof.
  apply Map.fold_elements.
Qed.

(** Size equals the enumeration length. *)
Theorem size_elements : size t = List.length (elements t).
Proof.
  apply Map.size_elements.
Qed.

(** Well-formed tables are empty exactly when every lookup fails. *)
Theorem is_empty_spec : wf t -> (is_empty t = true <-> forall k, get k t = None).
Proof.
  apply Map.is_empty_spec.
Qed.

End Laws.
End Table.
Import Table.
