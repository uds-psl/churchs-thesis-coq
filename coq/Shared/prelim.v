Require Export Setoid Morphisms.
Require Export equiv_on embed_nat Dec.

Notation "'if!' x 'is' p 'then' a 'else' b" := (match x with p => a | _ => b end) (at level 0, p pattern).

Notation "'fun!' '⟨' x ',' y '⟩' '=>' b" := (fun p => let (x,y) := unembed p in b) (at level 30, b at next level).

Notation "'∑' x .. y , p" := (sig (fun x => .. (sig (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' '∑'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

From Coq.Logic Require Import ConstructiveEpsilon.

Set Implicit Arguments.

Definition mu_nat_p := constructive_indefinite_ground_description_nat.

Lemma mu_nat_p_min P d H : forall m, m < proj1_sig (@mu_nat_p P d H) -> ~ P m.
Proof.
  intros. unfold mu_nat_p, constructive_indefinite_ground_description_nat in *.
  eapply linear_search_smallest. split. 2:eassumption. firstorder.
Qed.

Lemma mu_nat_p_least (P : nat -> Prop) d H : forall m, P m -> m >= proj1_sig (@mu_nat_p P d H).
Proof.
  intros. unfold mu_nat_p, constructive_indefinite_ground_description_nat in *.
  destruct (Compare_dec.le_lt_dec (proj1_sig (linear_search P d 0 (let (n, p) := H in O_witness P n (stop P n p)))) m).
  eassumption. exfalso.
  eapply linear_search_smallest. split. 2:eassumption. eapply le_0_n. eassumption.
Qed.

Lemma mu_nat_p_irrel (P : nat -> Prop) d H1 H2 : proj1_sig (@mu_nat_p P d H1) = proj1_sig (@mu_nat_p P d H2).
Proof.
  eapply PeanoNat.Nat.le_antisymm; eapply mu_nat_p_least, proj2_sig.
Qed.

Definition mu_nat (f : nat -> bool) (H : exists n, f n = true) : nat.
Proof.
  eapply mu_nat_p in H. eapply H. intros. decide equality.
Defined.

Definition mu_nat_spec (f : nat -> bool) (H : exists n, f n = true) : f (mu_nat f H) = true.
Proof.
  unfold mu_nat. now destruct mu_nat_p.
Qed.

Opaque mu_nat.
