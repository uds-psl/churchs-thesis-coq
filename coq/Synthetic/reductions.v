From stdpp Require Import prelude.
Require Import ssreflect.

Require Import Definitions DecidabilityFacts EnumerabilityFacts.
Require Export prelim.

(** ** Many-one reducibility *)

Definition reduces_m {X Y} (f : X -> Y) (P : X -> Prop) (Q : Y -> Prop) :=
  forall x, P x <-> Q (f x).
Definition red_m {X Y} (P : X -> Prop) (Q : Y -> Prop) :=
  exists f : X -> Y, reduces_m f P Q.
Notation "P ⪯ₘ Q" := (red_m P Q) (at level 50).
Notation "p ≡ₘ q" := (p ⪯ₘ q /\ q ⪯ₘ p) (at level 50).

Instance red_m_reflexive {X} : Reflexive (@red_m X X).
Proof.
  exists (fun x => x). firstorder.
Qed.

Lemma red_m_transitive {X Y Z} {p : X -> Prop} (q : Y -> Prop) (r : Z -> Prop) :
  p ⪯ₘ q -> q ⪯ₘ r -> p ⪯ₘ r.
Proof.
  move => [f Hf] [g Hg].
  exists (g ∘ f). firstorder.
Qed.

Lemma red_m_transports {X Y} (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ₘ q -> decidable q -> decidable p.
Proof.
  move => [f Hf] [d Hd].
  exists (d ∘ f). firstorder.
Qed.

Definition compl {X} (p : X -> Prop) := fun x => ~ p x.

Lemma red_m_complement {X Y} (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ₘ q -> compl p ⪯ₘ compl q.
Proof.
  firstorder.
Qed.

Definition PEM := forall P, P \/ ~ P.

Lemma red_m_compl_compl_PEM :
  (forall X (p : X -> Prop), p ⪯ₘ compl (compl p)) -> PEM.
Proof.
  move => H P.
  assert (forall P : Prop, ~~ P -> P). {
    move => Q.
    destruct (H unit (fun _ => Q)) as [f Hf % (fun Hf => Hf tt)].
    eapply Hf.
  }
  eapply H0. tauto.
Qed.

Lemma red_m_compl_compl_PEM_2 :
  (forall X (p : X -> Prop), compl (compl p) ⪯ₘ p) -> PEM.
Proof.
  move => H P.
  assert (forall P : Prop, ~~ P -> P). {
    move => Q.
    destruct (H unit (fun _ => Q)) as [f Hf % (fun Hf => Hf tt)].
    eapply Hf.
  }
  eapply H0. tauto.
Qed.

Lemma red_m_compl_compl_PEM_3 :
  (forall X Y (p : X -> Prop) (q : Y -> Prop), compl p ⪯ₘ compl q -> p ⪯ₘ q) -> PEM.
Proof.
  move => H.
  eapply red_m_compl_compl_PEM.
  move => *.
  eapply H. 
  exists (fun x => x). firstorder.
Qed.

Section upper_semi_lattice.

  Context {X Y : Prop}.
  Variables (p : X -> Prop) (q : Y -> Prop).

  Definition join : X + Y -> Prop := fun z => match z with inl x => p x | inr y => q y end.

  Lemma red_m_join_p :
    p ⪯ₘ join.
  Proof.
    exists inl. firstorder.
  Qed.

  Lemma red_m_join_q :
    q ⪯ₘ join.
  Proof.
    exists inr. firstorder.
  Qed.

  Lemma red_m_join_least {Z} (r : Z -> Prop) :
    p ⪯ₘ r -> q ⪯ₘ r -> join ⪯ₘ r.
  Proof.
    move => [f Hf] [g Hg].
    exists (fun z => match z with inl x => f x | inr y => g y end).
    move => []; firstorder.
  Qed.

End upper_semi_lattice.

Lemma red_m_decidable_nontriv {X Y} {p : X -> Prop} {q : Y -> Prop} :
  decidable p -> (exists y1, q y1) -> (exists y2, ~ q y2) -> p ⪯ₘ q.
Proof.
  intros [f H] [y1 H1] [y2 H2].
  exists (fun x => if f x then y1 else y2).
  move => x. specialize (H x). destruct (f x); firstorder.
Qed.

Definition stable {X} (p : X -> Prop) := forall x, ~~ p x -> p x.

Lemma red_m_transports_stable {X Y} {p : X -> Prop} {q : Y -> Prop} :
  stable q -> p ⪯ₘ q -> stable p.
Proof.
  move => Hp [f Hf] y Hy.
  eapply Hf, Hp.
  now rewrite <- (Hf y).
Qed.

Definition K (f : nat -> bool) := exists n, f n = true.

Lemma semi_decidable_red_K_iff {X} {p : X -> Prop} :
  semi_decidable p <-> p ⪯ₘ K.
Proof.
  reflexivity.
Qed.
