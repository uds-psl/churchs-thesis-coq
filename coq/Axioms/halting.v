From SyntheticComputability Require Import DecidabilityFacts EnumerabilityFacts SemiDecidabilityFacts ListEnumerabilityFacts prelim axioms embed_nat reductions partial.
Require Import ssreflect.

(** * Halting problems  *)

Section assm.

Lemma sec_enum (p : nat -> Prop) : semi_decidable p <-> enumerable p.
Proof.
  split.
  - intros. eapply semi_decidable_enumerable; eauto.
  - intros. eapply enumerable_semi_decidable; eauto.
    eapply discrete_iff. econstructor. exact _.
Qed.

Lemma dec_to_enum (p : nat -> Prop) :
  decidable p -> enumerable p.
Proof.
  intros. eapply dec_count_enum; eauto.
Qed.

Variable ax : EA.
Context {Part : partiality}.

Notation φ := (proj1_sig ax).
Notation φ_spec := (proj2_sig ax).
Notation W := (W ax).

Lemma W_spec : forall p : nat -> Prop, enumerable p <-> exists c, W c ≡{nat -> Prop} p.
Proof.
  eapply (EA_to_EA'_prf ax).
Qed.

Definition K0 := fun x => W x x.  

Lemma K0_enumerable : ~ enumerable (compl K0).
Proof.
  intros He. eapply W_spec in He as [c].
  specialize (H c). cbn in H. firstorder.
Qed.

Lemma K0_undec : ~ decidable K0. 
Proof.
  now move => / dec_compl / dec_to_enum / K0_enumerable.
Qed.

Lemma K0_compl_undec : ~ decidable (compl K0).
Proof.
  now move => / dec_to_enum / K0_enumerable.
Qed.

Lemma enumerable_W : enumerable (fun '(x, y) => W x y).
Proof.
  exists (fun p => let (n,m) := unembed p in if φ n m is Some m then Some (n, m) else None).
  move => [n m].
  split.
  - move => H.
    destruct ax as [e He].
    cbv in H. destruct H as [n' H].
    exists (embed (n, n')). rewrite embedP. cbn. now rewrite H.
  - unfold W.
    move => [p H].
    destruct (unembed p) as [n' m'].
    exists m'.
    destruct (φ n' m') eqn:E; inversion H; now subst.
Qed.

Lemma K0_enum : enumerable K0.
Proof.
  destruct enumerable_W as [f Hf].
  exists (fun n => if f n is Some (n, m) then if Nat.eqb n m then Some n else None else None).
  move => m. split.
  - move => / (Hf (m,m)) [n H].
    exists n. now rewrite H PeanoNat.Nat.eqb_refl.
  - move => [n H].
    eapply (Hf (m, m)). exists n.
    destruct (f n); try congruence.
    destruct p as (n', m').
    now destruct (NPeano.Nat.eqb_spec n' m'); inv H.
Qed.

Lemma semi_decidable_K : semi_decidable K.
Proof.
  eapply semi_decidable_red_K_iff. reflexivity.
Qed.

Lemma enumerable_red_K_iff {p : nat -> Prop} :
  enumerable p <-> p ⪯ₘ K.
Proof.
  rewrite <- sec_enum. eapply semi_decidable_red_K_iff.
Qed.

Lemma K0_red_K : K0 ⪯ₘ K.
Proof.
  rewrite <- semi_decidable_red_K_iff, sec_enum.
  eapply K0_enum.
Qed.

Lemma K_compl_undec : ~ decidable (compl K).
Proof.
  intros H.
  eapply K0_compl_undec, red_m_transports. eapply red_m_complement, K0_red_K. eassumption.
Qed.

Definition K_nat := fun f => exists n : nat, f n <> 0.

Lemma K_nat_equiv :
  K_nat ≡ₘ K.
Proof.
  split.
  - exists (fun f x => negb (Nat.eqb (f x) 0)).
    move => f. unfold K_nat, K.
    setoid_rewrite Bool.negb_true_iff.
    now setoid_rewrite NPeano.Nat.eqb_neq.
  - exists (fun f x => if f x then 1 else 0).
    move => f. unfold K_nat, K.
    split.
    + move => [] n Hn. exists n.
      rewrite Hn. eauto.
    + move => [] n Hn. exists n.
      destruct (f n); congruence.
Qed.

Lemma K_nat_equiv_compl :
  compl K_nat ≡{_} (fun f => forall n : nat, f n = 0).
Proof.
  move => f.
  split; move => H.
  - move => n. destruct (f n) eqn:E. reflexivity.
    destruct H. exists n. now rewrite E.
  - move => []. firstorder.
Qed.

Lemma K_forall_undec :
  ~ decidable (fun f => forall n : nat, f n = 0).
Proof.
  rewrite Proper_decidable.
  2:{ intros ?. symmetry. eapply K_nat_equiv_compl. }
  intros H. eapply K_compl_undec.
  eapply red_m_transports. eapply red_m_complement. eapply K_nat_equiv. eassumption.
Qed.

End assm.
