Require Import ssreflect Setoid embed_nat.
From Coq.Logic Require Import ConstructiveEpsilon.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Definition mu_nat := constructive_indefinite_ground_description_nat.

Lemma mu_nat_min P d H : forall m, m < proj1_sig (@mu_nat P d H) -> ~ P m.
Proof.
  intros. unfold mu_nat, constructive_indefinite_ground_description_nat in *.
  eapply linear_search_smallest. split. 2:eassumption. firstorder.
Qed.

(* Require Import Equations.Prop.DepElim. *)

(* Lemma linear_search_prf (P : nat -> Prop) (P_dec : forall n : nat, {P n} + {~ P n}) (start : nat) (pr1 pr2 : before_witness P start) : *)
(*       proj1_sig (linear_search P P_dec start pr1) = proj1_sig (linear_search P P_dec start pr2). *)
(* Proof. *)
(* Admitted. *)

(* Lemma mu_nat_prf P d H1 H2 : proj1_sig (@mu_nat P d H1) = proj1_sig (@mu_nat P d H2). *)
(* Proof. *)
(*   unfold mu_nat, constructive_indefinite_ground_description_nat in *. *)
(*   eapply linear_search_prf. *)
(* Qed. *)


Definition monotonic {X} (f : nat -> option X) :=
  forall n1 x, f n1 = Some x -> forall n2, n2 >= n1 -> f n2 = Some x.

Definition agnostic {X} (f : nat -> option X) :=
  forall n1 n2 y1 y2, f n1 = Some y1 -> f n2 = Some y2 -> y1 = y2.

Lemma monotonic_agnostic {X} (f : nat -> option X) :
  monotonic f -> agnostic f.
Proof.
  move => mono n1 n2 y1 y2 H1 H2.
  destruct (Compare_dec.le_ge_dec n1 n2) as [l | g].
  - eapply mono in l; eauto. congruence.
  - eapply mono in g; eauto. congruence.
Qed.

Class partiality :=
  {

    part : Type -> Type ;

    hasvalue : forall A, part A -> A -> Prop ;
    hasvalue_det : forall A x (a1 a2 : A), hasvalue x a1 -> hasvalue x a2 -> a1 = a2 ;

    ter A (x : part A) := exists a, hasvalue x a ;
    equiv A (x y : part A) := forall a, hasvalue x a <-> hasvalue y a ;

    ret : forall A, A -> part A ;
    ret_hasvalue : forall A (a : A), hasvalue (ret a) a ;

    undef : forall {A}, part A;
    undef_hasvalue : forall A (a : A), ~ hasvalue undef a ;

    bind : forall A B, part A -> (A -> part B) -> part B ;
    bind_hasvalue : forall A B x(f : A -> part B) b, hasvalue (bind x f) b <-> exists a, hasvalue x a /\ hasvalue (f a) b;

    par : forall A B, part A -> part B -> part (A + B) ;
    par_hasvalue1 : forall A B (x : part A) (y : part B) a, hasvalue (par x y) (inl a) -> hasvalue x a ;
    par_hasvalue2 : forall A B (x : part A) (y : part B) b, hasvalue (par x y) (inr b) -> hasvalue y b ;
    par_hasvalue3 : forall A B (x : part A) (y : part B), ter x \/ ter y -> ter (par x y) ;

    mu : (nat -> bool) -> part nat ;
    mu_hasvalue : forall (f : nat -> bool) n, hasvalue (mu f) n <-> (f n = true /\ forall m, m < n -> f m = false);

    seval : forall A, part A -> nat -> option A ;
    seval_mono : forall A x, monotonic (@seval A x) ;
    seval_hasvalue : forall A x (a : A), hasvalue x a <-> exists n, seval x n = Some a ;

  }.

Notation "a =! b" := (hasvalue a b) (at level 50).

Notation "A ↛ B" := (A -> part B) (at level 10).

Instance part_equiv_Equivalence `{partiality} {A} :
  Equivalence (@equiv _ A).
Proof.
  firstorder.
Qed.

Section assume_part.

  Context {impl : partiality}.

  Definition eval' {A} (x : part A) (H : ter x) : {a : A | hasvalue x a}.
  Proof.
    assert (Hx : exists n, seval x n <> None). {
      destruct H as [a [n H] % seval_hasvalue]. exists n. congruence.
    }
    eapply constructive_indefinite_ground_description_nat in Hx as [n Hx].
    - destruct seval eqn:E; try congruence. exists a. eapply seval_hasvalue. firstorder.
    - move => n. destruct seval; firstorder congruence.
  Qed.

  Definition eval {A} (x : part A) (H : ter x) : A := proj1_sig (eval' H).
  Definition eval_hasvalue {A} (x : part A) (H : ter x) : hasvalue x (eval H) := proj2_sig (eval' H).

  Definition mkpart {A} (f : nat -> option A) := let f' n := match f n with Some a => true | None => false end in bind (mu f') (fun n => match f n with Some a => ret a | None => undef end).

  Lemma mkpart_hasvalue1 {A} (f : nat -> option A) :
    forall a, mkpart f =! a -> exists n, f n = Some a.
  Proof.
    move => a.
    rewrite /mkpart bind_hasvalue.
    move => [] x [] / mu_hasvalue [] ter_mu Hmu Hf.
    exists x. destruct (f x). eapply (hasvalue_det (ret_hasvalue a0)) in Hf as ->.
    reflexivity. eapply undef_hasvalue in Hf as [].
  Qed.

  Lemma mkpart_ter {A} (f : nat -> option A) n a :
    f n = Some a -> ter (mkpart f).
  Proof.
    move => Hn. unfold ter.
    rewrite /mkpart. setoid_rewrite bind_hasvalue. 
    assert (Hf : exists n, f n <> None). exists n. firstorder congruence.
    assert (d : forall n : nat, {(fun n0 : nat => f n0 <> None) n} + {~ (fun n0 : nat => f n0 <> None) n}). { move => n0. destruct (f n0); firstorder congruence. }
    edestruct (mu_nat d Hf) as [m Hm] eqn:E. eapply (f_equal (@proj1_sig _ _)) in E.  cbn in E.
    destruct (f m) as [a0|]eqn:E2; try congruence.
    exists a0, m.
    (* assert (a0 = a) as -> by (eapply Hagn; eauto).  *)
    rewrite mu_hasvalue. repeat split.
    + rewrite E2. reflexivity.
    + subst. move => m' Hle.
      destruct (f m') eqn:E3.
      * eapply mu_nat_min in Hle. firstorder congruence.
      * reflexivity.
    + rewrite E2. eapply ret_hasvalue.
  Qed.

  Lemma mkpart_hasvalue2 {A} (f : nat -> option A) n a :
    agnostic f -> f n = Some a -> mkpart f =! a.
  Proof.
    move => Hagn Hn.
    destruct (mkpart_ter Hn) as [a' H].
    destruct (mkpart_hasvalue1 H) as [n' H'].
    now assert (a' = a) as -> by (eapply Hagn; eauto).
  Qed.

  Lemma mkpart_hasvalue {A} (f : nat -> option A) :
    agnostic f -> forall a, mkpart f =! a <-> exists n, f n = Some a.
  Proof.
    split.
    eapply mkpart_hasvalue1.
    move => [n Hn]. eapply mkpart_hasvalue2; eauto.
  Qed.  

  Lemma mu_ter (f : nat -> bool) n :
    f n = true ->
    ter (mu f).
  Proof.
    move => H.
    assert (He : exists n, f n = true) by eauto.
    assert (d : forall n, {f n = true} + {~ f n = true}) by (move => n'; destruct (f n'); firstorder congruence).
    destruct (mu_nat d He) as [n' Hn'] eqn:E.
    eapply (f_equal (@proj1_sig _ _)) in E.
    exists n'. eapply mu_hasvalue. split.
    - eauto.
    - move => m Hlt. cbn in E. subst.
      eapply mu_nat_min in Hlt. destruct (f m); congruence.
  Qed.


  Lemma ret_hasvalue_inv {A} (a1 a2 : A) :
    ret a1 =! a2 -> a1 = a2.
  Proof.
    move => H.
    eapply hasvalue_det. eapply ret_hasvalue. eauto.
  Qed.

End assume_part.
  
