Require Import ssreflect Setoid.

Class equiv_on (T : Type) :=
  {
    equiv_rel : T -> T -> Prop;
    equiv_rel_is_equiv : Equivalence equiv_rel
  }.
Arguments equiv_rel _ {_} _ _.
Existing Instance equiv_rel_is_equiv.

Notation "a ≡{ T } b" := (@equiv_rel T _ a b) (at level 70).

Instance ext_equiv {A B} `{equiv_on B} : equiv_on (A -> B).
Proof.
  exists (fun (f1 : A -> B) (f2 : A -> B) => forall x, f1 x ≡{B} f2 x).
  split.
  - move => ? ?. reflexivity.
  - move => x y ? z. now symmetry.
  - move => x y z ? ? a. now transitivity (y a).
Defined.

Instance nat_equiv : equiv_on nat := {| equiv_rel := eq |}.
Instance bool_equiv : equiv_on bool := {| equiv_rel := eq |}.
Instance Prop_equiv : equiv_on Prop := {| equiv_rel := iff |}.

Definition surjection_wrt {A} {B} (e : equiv_on B) (f : A -> B) :=
  forall b, exists a, f a ≡{B} b.
