From SyntheticComputability.Synthetic Require Import DecidabilityFacts SemiDecidabilityFacts.
From SyntheticComputability.Shared Require Export prelim embed_nat.
Require Import List.
Export EmbedNatNotations.

(** ** Enumerable predicates  *)

Lemma enumerable_semi_decidable {X} {p : X -> Prop} :
  discrete X -> enumerable p -> semi_decidable p.
Proof.
  unfold enumerable, enumerator.
  intros [d Hd] [f Hf].
  exists (fun x n => if! f n is Some y then d (x,y) else false).
  intros x. rewrite Hf. split.
  - intros [n Hn]. exists n.
    rewrite Hn. now eapply Hd.
  - intros [n Hn]. exists n.
    destruct (f n); inversion Hn.
    eapply Hd in Hn. now subst.
Qed.

Definition enumerator__T' X f := forall x : X, exists n : nat, f n = Some x.
Notation enumerator__T f X := (enumerator__T' X f).
Definition enumerable__T X := exists f : nat -> option X, enumerator__T f X.

Lemma semi_decidable_enumerable {X} {p : X -> Prop} :
  enumerable__T X -> semi_decidable p -> enumerable p.
Proof.
  unfold semi_decidable, semi_decider.
  intros [e He] [f Hf].
  exists (fun p => let (n, m) := unembed p in
           if! e n is Some x then if f x m then Some x else None else None).
  intros x. rewrite Hf. split.
  - intros [n Hn]. destruct (He x) as [m Hm].
    exists (embed (m,n)). now rewrite embedP, Hm, Hn.
  - intros [mn Hmn]. destruct (unembed mn) as (m, n).
    destruct (e m) as [x'|]; try congruence.
    destruct (f x' n) eqn:E; inversion Hmn. subst.
    exists n. exact E.
Qed.

Theorem dec_count_enum {X} {p : X -> Prop} :
  decidable p -> enumerable__T X -> enumerable p.
Proof.
  intros ? % decidable_semi_decidable ?.
  now eapply semi_decidable_enumerable.
Qed.

Theorem dec_count_enum' X (p : X -> Prop) :
  decidable p -> enumerable__T X -> enumerable (fun x => ~ p x).
Proof.
  intros ? % dec_compl ?. eapply dec_count_enum; eauto.
Qed.

Lemma enumerable_enumerable_T X :
  enumerable (fun _ : X => True) <-> enumerable__T X.
Proof.
  split.
  - intros [e He]. exists e. intros x. now eapply He.
  - intros [c Hc]. exists c. intros x. split; eauto.
Qed.

Lemma projection X Y (p : X * Y -> Prop) :
  enumerable p -> enumerable (fun x => exists y, p (x,y)).
Proof.
  intros [f].
  exists (fun n => match f n with Some (x, y) => Some x | None => None end).
  intros; split.
  - intros [y ?]. eapply H in H0 as [n]. exists n. now rewrite H0.
  - intros [n ?]. destruct (f n) as [ [] | ] eqn:E; inv H0.
    exists y. eapply H. eauto.
Qed.

Lemma projection' X Y (p : X * Y -> Prop) :
  enumerable p -> enumerable (fun y => exists x, p (x,y)).
Proof.
  intros [f].
  exists (fun n => match f n with Some (x, y) => Some y | None => None end).
  intros y; split.
  - intros [x ?]. eapply H in H0 as [n]. exists n. now rewrite H0.
  - intros [n ?]. destruct (f n) as [ [] | ] eqn:E; inv H0.
    exists x. eapply H. eauto.
Qed.

Lemma enumerable_graph {X} {Y} (f : X -> Y) :
  enumerable__T X ->
  enumerable (fun p => exists x, p = ( x, f x )).
Proof.
  intros [e He].
  exists (fun n => if! e n is Some x then Some (x, f x) else None).
  intros y. split.
  - intros [x ->]. specialize (He x) as [n Hn]. exists n.
    now rewrite Hn.
  - intros [n Hn].
    destruct (e n); inv Hn. eauto.
Qed.

Instance equiv_ran {A B} : equiv_on (A -> option B) | 100.
Proof.
  exists (fun f1 f2 => forall x, (exists n, f1 n = Some x) <-> (exists n, f2 n = Some x)).
  split; red.
  - reflexivity.
  - intros x y H1 z. now rewrite H1.
  - intros f1 f2 f3 H1 H2 x.
    now rewrite H1, H2.
Defined.

Notation "f ≡{ran} g" := (@equiv_rel _  equiv_ran f g) (at level 80).

Lemma enumerates_ext {X} {p q : X -> Prop} {f g} :
  enumerator f p -> enumerator g q -> f ≡{ran} g -> p ≡{_} q.
Proof.
  unfold enumerator. cbn.
  intros Hp Hq E x.
  now rewrite Hp, E, Hq.
Qed. 

(** Type enumerability facts  *)

Definition nat_enum (n : nat) := Some n.
Lemma enumerator__T_nat :
  enumerator__T nat_enum nat.
Proof.
  intros n. cbv. eauto.
Qed.

Definition unit_enum (n : nat) := Some tt.
Lemma enumerator__T_unit :
  enumerator__T unit_enum unit.
Proof.
  intros []. cbv. now exists 0.
Qed. 

Definition bool_enum (n : nat) := Some (if! n is 0 then true else false).
Lemma enumerator__T_bool :
  enumerator__T bool_enum bool.
Proof.
  intros []. cbv.
  - now exists 0.
  - now exists 1.
Qed.

Definition prod_enum {X Y} (f1 : nat -> option X) (f2 : nat -> option Y) : nat -> option (X * Y) :=
  fun! ⟨n, m⟩ => if! (f1 n, f2 m) is (Some x, Some y) then Some (x, y) else None.
Lemma enumerator__T_prod {X Y} f1 f2 :
  enumerator__T f1 X -> enumerator__T f2 Y ->
  enumerator__T (prod_enum f1 f2) (X * Y).
Proof.
  intros H1 H2 (x, y).
  destruct (H1 x) as [n1 Hn1], (H2 y) as [n2 Hn2].
  exists (embed (n1, n2)). unfold prod_enum.
  now rewrite embedP, Hn1, Hn2.
Qed.

Definition option_enum {X} (f : nat -> option X) n :=
  match n with 0 => Some None | S n => Some (f n) end.
Lemma enumerator__T_option {X} f :
  enumerator__T f X -> enumerator__T (option_enum f) (option X).
Proof.
  intros H [x | ].
  - destruct (H x) as [n Hn]. exists (S n). cbn. now rewrite Hn.
  - exists 0. reflexivity.
Qed.

(** embedability  *)

Definition retraction' {X} {Y} (I : X -> Y) R := forall x : X, R (I x) = Some x.
Notation retraction I R X Y := (@retraction' X Y I R).

Definition retract X Y := exists I R, retraction I R X Y.
Definition countable X := retract X nat.

Lemma countable_discrete X :
  countable X -> discrete X.
Proof.
  intros (I & R & H).
  exists (fun '(x,y)=> Nat.eqb (I x) (I y)).
  intros [x y].
  red. rewrite PeanoNat.Nat.eqb_eq.
  split.
  - congruence.
  - intros H1 % (f_equal R). rewrite !H in H1. congruence.
Qed.

Lemma countable_enumerable X :
  countable X -> enumerable__T X.
Proof.
  intros (I & R & H).
  exists R. intros x. exists (I x). eapply H.
Qed.

Lemma enumerable_discrete_countable X :
  discrete X -> enumerable__T X -> countable X.
Proof.
  intros [d Hd] [e He].
  unshelve eexists (fun x => mu_nat (fun n => if! e n is Some y then d (x, y) else false) _).
  - abstract (destruct (He x) as [n Hn]; exists n; rewrite Hn; now eapply Hd).
  - exists e. intros x.
    pose proof (mu_nat_spec (fun n : nat => if! e n is (Some y) then d (x, y) else (false)) (enumerable_discrete_countable_subproof X d Hd e He x)) as H.
    cbn in H.
    destruct (e (mu_nat (fun n : nat => if! e n is (Some y) then d (x, y) else (false)) (enumerable_discrete_countable_subproof X d Hd e He x))).
    + eapply Hd in H. now subst.
    + congruence.
Qed.

(** Type classes *)

Existing Class enumerator__T'.
(* Existing Class enumerable__T. *)

Lemma enumerator_enumerable {X} {f} :
  enumerator__T f X -> enumerable__T X.
Proof.
  intros H. exists f. eapply H.
Qed.
Hint Resolve enumerator_enumerable : core.

Existing Instance enumerator__T_prod.
Existing Instance enumerator__T_option.
Existing Instance enumerator__T_bool.
Existing Instance enumerator__T_nat.

Lemma enumerable_graph' (f : nat -> nat) :
  enumerable (fun p => exists x, p = ⟨ x, f x ⟩).
Proof.
  destruct (enumerable_graph f) as [e He].
  - eauto.
  - exists (fun n => if! e n is Some (x, y) then Some ⟨ x, y ⟩ else None).
    intros xy.
    split.
    + intros [x ->].
      destruct (He (x, f x)) as [[n] _]; eauto.
      exists n. rewrite H. eauto.
    + intros [n H].
      destruct (e n) as [ [x fx] | ] eqn:E; inv H.
      destruct (He (x, fx)) as [_ []].
      * eauto.
      * exists x. inv H. eauto.
Qed.
