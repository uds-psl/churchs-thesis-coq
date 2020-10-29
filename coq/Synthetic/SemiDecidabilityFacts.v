Require Import SyntheticComputability.Synthetic.DecidabilityFacts partial.
Require Import List.

(** ** Semidecidable predicates  *)

Lemma decidable_semi_decidable {X} {p : X -> Prop} :
  decidable p -> semi_decidable p.
Proof.
  intros [f H].
  exists (fun x n => f x). intros x.
  unfold decider, reflects in H.
  rewrite H. firstorder. econstructor.
Qed.

Lemma decidable_compl_semi_decidable {X} {p : X -> Prop} :
  decidable p -> semi_decidable (compl p).
Proof.
  intros H.
  now eapply decidable_semi_decidable, dec_compl.
Qed.

Lemma reflects_cases {P} {b} :
  reflects b P -> b = true /\ P \/ b = false /\ ~ P.
Proof.
  destruct b; firstorder congruence.
Qed.

Lemma d_semi_decidable_impl {X} {p q : X -> Prop} :
  decidable p -> semi_decidable q -> semi_decidable (fun x => p x -> q x).
Proof.
  intros [f Hf] [g Hg].
  exists (fun x n => if f x then g x n else true).
  intros x. split.
  - intros H. destruct (reflects_cases (Hf x)) as [ [-> H2] | [-> H2] ].
    + firstorder.
    + now exists 0.
  - intros [n H]. revert H.
    destruct (reflects_cases (Hf x)) as [ [-> H2] | [-> H2]]; intros H.
    + firstorder.
    + firstorder.
Qed.

Lemma d_co_semi_decidable_impl {X} {p q : X -> Prop} :
  decidable p -> semi_decidable (compl q) -> semi_decidable (compl (fun x => p x -> q x)).
Proof.
  intros [f Hf] [g Hg].
  exists (fun x n => if f x then g x n else false).
  intros x. split.
  - intros H. destruct (reflects_cases (Hf x)) as [ [-> H2] | [-> H2] ].
    + red in H. firstorder.
    + firstorder.
  - intros [n H]. revert H.
    destruct (reflects_cases (Hf x)) as [ [-> H2] | [-> H2]]; intros H.
    + firstorder.
    + firstorder.
Qed.

Lemma co_semi_decidable_impl {X} {p q : X -> Prop} :
  (* (forall x, ~~ p x -> p x) -> *)
  semi_decidable (compl (compl p)) -> decidable q -> semi_decidable (compl (fun x => p x -> q x)).
Proof.
  intros [f Hf] [g Hg].
  exists (fun x n => if g x then false else f x n).
  intros x. split.
  - intros H. destruct (reflects_cases (Hg x)) as [ [-> H2] | [-> H2] ].
    + firstorder.
    + eapply Hf. firstorder.
  - intros [n H]. revert H.
    destruct (reflects_cases (Hg x)) as [ [-> H2] | [-> H2]]; intros H.
    + congruence.
    + intros ?. firstorder.
Qed.

Lemma semi_decidable_impl {X} {p q : X -> Prop} :
  semi_decidable (compl p) -> decidable q -> semi_decidable (fun x => p x -> q x).
Proof.
  intros [f Hf] [g Hg].
  exists (fun x n => if g x then true else f x n).
  intros x. split.
  - intros H. destruct (reflects_cases (Hg x)) as [ [-> H2] | [-> H2] ].
    + now exists 0.
    + eapply Hf. firstorder.
  - intros [n H]. revert H.
    destruct (reflects_cases (Hg x)) as [ [-> H2] | [-> H2]]; intros H.
    + eauto.
    + intros. firstorder.
Qed.

Lemma semi_decidable_or {X} {p q : X -> Prop} :
  semi_decidable p -> semi_decidable q -> semi_decidable (fun x => p x \/ q x).
Proof.
  intros [f Hf] [g Hg].
  exists (fun x n => orb (f x n) (g x n)).
  red in Hf, Hg |- *. intros x.
  rewrite Hf, Hg.
  setoid_rewrite Bool.orb_true_iff.
  clear. firstorder.
Qed.

Lemma semi_decidable_and {X} {p q : X -> Prop} :
  semi_decidable p -> semi_decidable q -> semi_decidable (fun x => p x /\ q x).
Proof.
  intros [f Hf] [g Hg].
  exists (fun x n => andb (existsb (f x) (seq 0 n)) (existsb (g x) (seq 0 n))).
  red in Hf, Hg |- *. intros x.
  rewrite Hf, Hg.
  setoid_rewrite Bool.andb_true_iff.
  setoid_rewrite existsb_exists.
  repeat setoid_rewrite in_seq. cbn.
  clear.
  split.
  - intros [[n1 Hn1] [n2 Hn2]]. 
    exists (1 + n1 + n2). firstorder lia. 
  - firstorder.
Qed.

Lemma semi_decidable_projection_iff X (p : X -> Prop) :
  semi_decidable p <-> exists (q : nat * X -> Prop), decidable q /\ forall x, p x <-> exists n, q (n, x).
Proof.
  split.
  - intros [d Hd].
    exists (fun '(n, x) => d x n = true). split. 
    + exists (fun '(n,x) => d x n). intros [n x]. firstorder congruence.
    + intros x. eapply Hd.
  - intros (q & [f Hf] & Hq).
    exists (fun x n => f (n, x)). unfold semi_decider, decider, reflects in *.
    intros x. rewrite Hq. now setoid_rewrite Hf.
Qed.

Lemma sdec_compute_lor {X} {p q : X -> Prop} :
  semi_decidable p -> semi_decidable q -> (forall x, p x \/ q x) -> exists f : X -> bool, forall x, if f x then p x else q x.
Proof.
  intros [f_p Hp] [f_q Hq] Ho.
  unshelve eexists.
  - refine (fun x => let (n, H) := mu_nat (P := fun n => orb (f_p x n) (f_q x n) = true) (ltac:(cbn; decide equality)) _ in f_p x n).
    destruct (Ho x) as [[n H] % Hp | [n H] % Hq].
    + exists n. now rewrite H.
    + exists n. rewrite H. now destruct f_p.
  - intros x. cbn -[mu_nat]. destruct mu_nat.
    specialize (Hp x). specialize (Hq x).
    destruct (f_p) eqn:E1. eapply Hp. eauto.
    destruct (f_q) eqn:E2. eapply Hq. eauto.
    inversion e.
Qed.

Definition co_semi_decidable {X} (p : X -> Prop) : Prop :=
  exists f : X -> nat -> bool, forall x : X, p x <-> (forall n : nat, f x n = false).

Lemma co_semi_decidable_and {X} {p q : X -> Prop} :
  co_semi_decidable p -> co_semi_decidable q -> co_semi_decidable (fun x => p x /\ q x).
Proof.
  intros [f Hf] [g Hg].
  exists (fun x n => orb (f x n) (g x n)).
  intros x. rewrite Hf, Hg.
  setoid_rewrite Bool.orb_false_iff.
  clear. firstorder.
Qed.

Lemma forall_neg_exists_iff (f : nat -> bool) :
  (forall n, f n = false) <-> ~ exists n, f n = true.
Proof.
  split.
  - intros H [n Hn]. rewrite H in Hn. congruence.
  - intros H n. destruct (f n) eqn:E; try reflexivity.
    destruct H. eauto.
Qed.

Lemma co_semi_decidable_stable :
  forall X (p : X -> Prop), co_semi_decidable p -> stable p.
Proof.
  intros X p [f Hf] x Hx.
  eapply Hf. eapply forall_neg_exists_iff. rewrite Hf, forall_neg_exists_iff in Hx. 
  tauto.
Qed.
