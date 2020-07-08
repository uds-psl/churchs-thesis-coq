From SyntheticComputability Require Import Synthetic.DecidabilityFacts Synthetic.EnumerabilityFacts reductions partial embed_nat.
Require Import ssreflect Setoid Program Lia.
Require Import prelim Lia Nat.

Definition least p n k := n <= k /\ p k /\ forall i, n <= i -> p i -> k <= i.

Section WO.

  Variable f: nat -> bool.

  (* Guardedness predicate *)
  Inductive G (n: nat) : Prop :=
  | GI : (f n = false -> G (S n)) -> G n.

  Lemma G_sig n :
    G n -> { k | least (fun k => f k = true) n k }.
  Proof.
    induction 1 as [n _ IH].
    destruct (f n) eqn:H.
    - exists n. repeat split; eauto.
    - destruct (IH eq_refl) as (k & Hle & Hk & Hleast).
      exists k. repeat split.
      + lia.
      + exact Hk.
      + intros i Hi. inversion Hi.
        * congruence.
        * eapply Hleast; eauto. lia.
  Defined.

  Lemma G_zero n :
    G n -> G 0.
  Proof.
    induction n as [|n IH].
    - intros H. exact H.
    - intros H. apply IH. constructor. intros _. exact H.
  Defined.
   
  Theorem wo :
    (exists n, f n = true) -> { n | least (fun n => f n = true) 0 n }.
  Proof.
    intros H. apply (G_sig 0).
    destruct H as [n H].  (* witness needed *)
    apply (G_zero n).
    constructor. rewrite H. discriminate.
  Defined.

End WO.

Definition mu_nat (p : nat -> Prop) (d : forall x, dec (p x)) (H : exists x, p x) : ∑ x, least p 0 x.
Proof.
  destruct (wo (fun n => if d n then true else false)) as (n & H1 & H2 & H3).
  - destruct H as [n Hn]. exists n. destruct (d n); eauto.
  - exists n. repeat split.
    + lia.
    + destruct (d n); cbn in *; congruence.
    + intros. eapply H3. lia. destruct (d i); cbn in *; congruence.
Qed.

Lemma AC_dec_least (p : nat -> Prop) : (forall n, {p n} + {~ p n}) -> (exists n, p n) -> ∑ n, least p 0 n.
Proof.
  intros d H.
  assert (exists n, (fun n => if! d n is left _ then true else false) n = true) as [n (H1 & H2 & H3)] % wo.
  { destruct H as [n Hn]. exists n. destruct (d n); firstorder. }
  exists n; repeat split; eauto.
  - now destruct (d n); inv H2.
  - intros. eapply H3. lia.
    destruct (d i); firstorder.
Qed.

(** * Church's thesis in type theory *)

Class model_of_computation :=
  {
    T : nat -> nat -> nat -> option nat ;
    T_mono : forall c x, monotonic (T c x) ;
    computes c f := forall x, exists n, T c x n = Some (f x)
  }.

Hint Resolve T_mono : core.

Notation "c ∼ f" := (computes c f) (at level 80).

Section assm_model_of_computation.

  Context {model : model_of_computation}.

  Lemma T_func_in_n c x n1 n2 y1 y2 :
    T c x n1 = Some y1 -> T c x n2 = Some y2 -> y1 = y2.
  Proof.
    eapply monotonic_agnostic, T_mono.
  Qed.

  Lemma computes_ext  c f1 f2 :
    c ∼ f1 -> c ∼ f2 -> forall x, f1 x = f2 x.
  Proof.
    move => H1 H2 x.
    destruct (H1 x) as [n1 Hn1], (H2 x) as [n2 Hn2].
    eauto using T_func_in_n.
  Qed.

End assm_model_of_computation.

Section Cantor.

  Variable A : Type.
  Variable g : A -> (A -> Prop).

  Lemma Cantor : surjection_wrt ext_equiv g -> False.
  Proof.
    move => g_surj.
    pose (h x1 := ~ (g x1 x1)).
    destruct (g_surj h) as [n H].
    firstorder.
  Qed.

End Cantor.

Definition CT `{model_of_computation} := forall f, exists n, n ∼ f.

(* ** Church's thesis for partial functions  *)

Definition CTP `{model_of_computation} `{partiality} := forall f : nat ↛ nat, exists c, forall x y, f x =! y <-> exists n, T c x n = Some y.

Lemma CTP_to_CT `{model_of_computation} `{partiality} :
  CTP -> CT.
Proof.
  move => CTP f.
  destruct (CTP (fun x => ret (f x))) as [n Hn].
  exists n. move => x.
  eapply Hn, ret_hasvalue.
Qed.

Notation "⟨ a , b ⟩" := (embed (a, b)) (at level 0).

Lemma partial_to_total `{Part : partiality} (f : nat ↛ nat) :
  {f' : nat -> nat | forall x a, f x =! a <-> exists n, f' ⟨x, n⟩ = S a }.
Proof.
  exists (fun arg => let (x,n) := unembed arg in match seval (f x) n with Some a => S a | None => 0 end).
  move => x a. split.
  - move => / seval_hasvalue [n H].
    exists n. now rewrite embedP H.
  - move => [n H]. rewrite embedP in H.
    eapply seval_hasvalue. exists n.
    destruct seval; congruence.
Qed.

Instance equiv_part `{partiality} {A} : equiv_on (part A) := {| equiv_rel := @partial.equiv _ A |}.

(** ** Bauer's enumerability axiom EA  *)

Definition EA := ∑ e : nat -> (nat -> option nat), forall f : nat -> option nat, exists c, e c ≡{ran} f.

Definition φ `{model_of_computation} c := fun! ⟨ n, m ⟩ => match T c n m with Some (S x) => Some x | _ => None end.

Lemma CT_to_EA' {M : model_of_computation} :
  CT -> forall f : nat -> option nat, exists c : nat, φ c ≡{ nat -> option nat} f.
Proof.
  intros ct f.
  destruct (ct (fun n => match f n with Some x => S x | None => 0 end)) as [c Hc].
  exists c. intros x. unfold φ.
  split.
  - intros [n Hn]. 
    destruct (unembed n) as (n1, n2).
    destruct (T c n1 n2) as [ [ | ] | ] eqn:E; inv Hn.
    exists n1. destruct (Hc n1).
    pose proof (T_func_in_n _ _ _ _ _ _ E H).
    destruct (f n1); congruence.
  - intros [n Hn].
    destruct (Hc n) as [m Hm].
    exists ⟨n,m⟩. now rewrite embedP Hm Hn.
Qed.

Lemma CT_to_EA {M : model_of_computation} :
  CT -> EA.
Proof.
  intros ct. exists φ. now eapply CT_to_EA'.
Qed.

Definition EA' := ∑ e : nat -> (nat -> Prop), forall p : nat -> Prop, enumerable p <-> exists c, e c ≡{nat -> Prop} p.

Definition W (ax : EA) c x := exists n, proj1_sig ax c n = Some x.

Lemma EA_to_EA'_prf (ax : EA) :
  forall p : nat -> Prop, enumerable p <-> exists c, W ax c ≡{nat -> Prop} p.
Proof.
  destruct ax as [e He].
  move => p.
  rewrite /enumerable /enumerator.
  transitivity (exists c, forall x, p x <-> exists n, e c n = Some x).
  - split.
    + move => [f H].
      destruct (He f) as [c Hc].
      exists c. move => x. rewrite H. cbn in Hc. now rewrite Hc.
    + move => [c H].
      now exists (e c).
 - firstorder.
Qed.

Lemma EA_to_EA' :
  EA -> EA'.
Proof.
  move => H.
  eexists. apply (EA_to_EA'_prf H).
Qed.

(** ** Richman's enumerability of partial functions EPF  *)

Definition EPF `{partiality} := ∑ e : nat -> (nat ↛ nat), forall f : nat ↛ nat, exists n, e n ≡{nat ↛ nat} f.

Definition e `{partiality} `{model_of_computation} := (fun c x => mkpart (fun arg => let (n, m) := unembed arg in match T c ⟨ x, n ⟩ m with Some (S x) => Some x | _ => None end)).

Definition toenum `{partiality} (f : nat ↛ nat) (n : nat) :=
  let (x,n) := unembed n in
  match seval (f x) n with Some y => Some (x,y) | None => None end.

Definition ofenum `{partiality} (g : nat -> option (nat * nat)) (x : nat) :=
  bind (mu (fun n => match g n with Some (x', y) => Nat.eqb x x' | _ => false end))
       (fun n => match g n with Some (_, y) => ret y | _ => undef end).

Lemma toenum_spec {Part : partiality} (f : nat ↛ nat) x y :
  (f x =! y) <-> (exists n, toenum f n = Some (x,y)).
Proof.
  rewrite /toenum. split.
  - move => H.
    eapply seval_hasvalue in H as [n H].
    exists (⟨ x, n ⟩). now rewrite embedP H.
  - move => [n H].
    destruct (unembed n), seval eqn:E; inv H.
    eapply seval_hasvalue. eauto.
Qed.

Lemma ofenum_ter_iff {Part : partiality} g x :
  (ter (ofenum g x)) <-> (exists n y, g n = Some (x, y)).
Proof.
  rewrite /ofenum. split.
  - move => [] y H.
    eapply bind_hasvalue in H as [n [[H1 H2] % mu_hasvalue H3]].
    destruct (g n) as [[x' y']|] eqn:E.
    + eapply ret_hasvalue_inv in H3.
      exists n, y. 
      destruct (PeanoNat.Nat.eqb_spec x x').
      all:congruence.
    + now eapply undef_hasvalue in H3.
  - intros [n (_ & [y H] & Hleast)] % AC_dec_least.
    + exists y.
      rewrite bind_hasvalue.
      exists n. rewrite mu_hasvalue H.
      rewrite NPeano.Nat.eqb_refl.
      repeat split. 2:eapply ret_hasvalue.
      intros. destruct (g m) as [ [x' y'] | ] eqn:E.
      * eapply NPeano.Nat.eqb_neq.
        intros ->.
        enough (n <= m) by lia. eapply Hleast.
        lia. eauto.
      * reflexivity.
    + intros n.
      destruct (g n) as [ [x' ] | ]; try firstorder congruence.
      destruct (nat_eq_dec x x'); subst; eauto; firstorder congruence.
Qed.

Lemma EPF_to_CT `{partiality} :
  EPF -> ∑ m : model_of_computation, CT.
Proof.
  move => [e EPF].
  unshelve eexists.
  - unshelve econstructor.
    + exact (fun c x n => seval (e c x) n).
    + cbn. move => c x y n1 Hn1 n2 len.
      eapply seval_mono; eauto.
  - move => f.
    destruct (EPF (fun n => ret (f n))) as [c Hc].
    exists c. move => x.
    cbn. specialize (Hc x (f x)).
    eapply seval_hasvalue, Hc, ret_hasvalue.
Qed.

Theorem EPF_to_EA {Part : partiality} :
  EPF -> EA.
Proof.
  move => [e EPF].
  exists (fun c n => match toenum (e c) n with Some (x,y) => Some x | _ => None end).
  move => f. pose (f' := (fun n => match f n with Some x => Some (x,x) | _ => None end)).
  destruct (EPF (ofenum f')) as [c Hc].
  exists c. move => x.
  transitivity (exists y, e c x =! y). {
    split.
    - move => [n H].
      destruct toenum as [[m1 y]|] eqn:E; inv H.
      exists y. eapply toenum_spec. eauto.
    - move => [y Hy].
      eapply toenum_spec in Hy as [n Hn].
      exists n. now rewrite Hn.
  }
  transitivity (exists y, ofenum f' x =! y).
  - split; move => [y Hy]; exists y; now eapply Hc.
  - transitivity (ter (ofenum f' x)). reflexivity.
    rewrite ofenum_ter_iff /f'.
    split.
    + move => [n [y H]]. exists n. destruct (f n); congruence.
    + move => [n H]. exists n, x.
      now rewrite H.
Qed.

Lemma ofenum_spec {Part : partiality} (g : nat -> option (nat * nat)) x y :
  ofenum g x =! y -> (exists n, g n = Some (x,y)).
Proof.
  rewrite /ofenum.
  move => H. eapply bind_hasvalue in H as [n [[H1 _] % mu_hasvalue H2]].
  destruct (g n) as [[x' y']|] eqn:E.
  + eapply ret_hasvalue_inv in H2. subst.
    eapply EqNat.beq_nat_true in H1 as ->. eauto.
  + now eapply undef_hasvalue in H2.
Qed.

Lemma ofenum_ter {Part : partiality} (g : nat -> option (nat * nat)) n x y :
  g n = Some (x,y) -> ter (ofenum g x).
Proof.
  move => H. eapply ofenum_ter_iff. eauto.
Qed.

Theorem EA_to_EPF {Part : partiality} :
  EA -> EPF.
Proof.
  move => [e EA].
  exists (fun c => ofenum (fun n => match e c n with Some n => Some (unembed n) | None => None end)).
  move => f.
  destruct (EA (fun n => match toenum f n with Some p => Some (embed p) | None => None end)) as [c Hc].
  exists c. move => x y.
  split.
  - move => / ofenum_spec [] n H.
    destruct (e c n) as [xy|] eqn:E ; inv H.
    assert (exists n, e c n = Some xy) as [n' Hn'] % Hc by eauto.
    destruct (toenum) as [xy'|] eqn:E2; inv Hn'.
    rewrite embedP in H1. destruct xy'. inv H1.
    eapply toenum_spec. eauto.
  - move / toenum_spec => [n Hn].
    destruct (Hc (embed (x,y))) as [_ [m Hm]].
    exists n. now rewrite Hn.
    
    pose proof (ofenum_ter ((fun n0 : nat => match e c n0 with
                                        | Some n1 => Some (unembed n1)
                                        | None => None
                                        end)) m x y).
    cbn in H. rewrite Hm embedP in H. specialize (H eq_refl).
    destruct H as [y' H].
    enough (y = y') by (now subst).
    eapply ofenum_spec in H as [n' H].
    destruct (e c n') eqn:E; inv H.
    eapply (f_equal embed) in H1. rewrite unembedP in H1.
    subst.
    assert (H : exists m, e c m = Some ⟨ x, y ⟩) by eauto.
    eapply Hc in H as [n'' H'].
    assert (H : exists m, e c m = Some ⟨ x, y' ⟩) by eauto.
    eapply Hc in H as [n''' H''].
    destruct (toenum f n'') eqn:E1; try congruence.
    destruct (toenum f n''') eqn:E2; try congruence.
    eapply option.Some_inj, (f_equal unembed) in H'.
    eapply option.Some_inj, (f_equal unembed) in H''.
    rewrite !embedP in H', H''. subst.
    eapply hasvalue_det; eapply toenum_spec; eauto.
Qed.

(* deprecated *)
Lemma CT_to_EPF' `{partiality} `{model_of_computation} :
  CT -> forall f : nat ↛ nat, exists n : nat, e n ≡{ nat ↛ nat} f.
Proof.
  move => CT f. destruct (partial_to_total f) as [f' Hf'].
  destruct (CT f') as [c Hc].
  exists c. move => x y.

  transitivity (exists n m, T c ⟨ x, n ⟩ m = Some (S y)). {
    rewrite mkpart_hasvalue.
    split.
    - move => [n Hn]. destruct (unembed n) as [n' m] eqn:E.
      exists n', m.
      destruct T as [ [] | ]; try congruence.
    - move => [n [m HT]]. exists ⟨ n, m ⟩. now rewrite embedP HT.
    - move => n1' n2' x1 x2 H1 H2.
      destruct (unembed n1') as [n1 m1], (unembed n2') as [n2 m2].
      destruct (Hc ⟨x,n1⟩) as [m3 H3], (Hc ⟨x,n2⟩) as [m4 H4].
      destruct (T c ⟨ x, n1 ⟩ m1) eqn:E1; try congruence.
      destruct (T c ⟨ x, n2 ⟩ m2) eqn:E2; try congruence.
      eapply T_func_in_n in E1; eauto. subst n.
      eapply T_func_in_n in E2; eauto. subst n0.
      destruct (f' ⟨ x, n1 ⟩) eqn:E1; try congruence.
      destruct (f' ⟨ x, n2 ⟩) eqn:E2; try congruence.
      inv H1. inv H2.
      assert (f x =! x1) by (eapply Hf'; eauto).
      assert (f x =! x2) by (eapply Hf'; eauto).
      eapply hasvalue_det; eauto.
  }
  
  rewrite Hf'. 

  split.
  - move => [n [m HT]].
    destruct (Hc ⟨ x, n ⟩).
    eapply T_func_in_n in HT. all:eauto.
  - move => [n Hn].
    destruct (Hc ⟨ x, n ⟩).
    rewrite Hn in H1. eauto.
Qed.

Corollary CT_to_EPF `{partiality} `{model_of_computation} :
  CT -> EPF.
Proof.
  move => CT. exists e.
  now eapply CT_to_EPF'.
Qed.  

Section assm_EA'.

  Variable ax : EA'.
  Notation W := (proj1_sig ax).

  Lemma W_self_enumerable : ~ enumerable (fun x => ~ W x x).
  Proof.
    intros He.
    destruct ax as [W HW]. cbn in *.
    eapply HW in He as [c].
    specialize (H c). tauto.
  Qed.

End assm_EA'.

Definition EPF_bool `{partiality} := ∑ e : nat -> (nat ↛ bool), forall f : nat ↛ bool, exists n, e n ≡{nat ↛ bool} f.

Section assm_part.

Context {Part : partiality}.

Let F (g : nat ↛ nat) x := bind (g x) (fun y => if Nat.eqb y 0 then ret true else ret false).
Let G (f : nat ↛ bool) x := bind (f x) (fun y => if y then ret 0 else ret 1).

Lemma EPF_to_EPF_bool  :
  EPF -> EPF_bool.
Proof.
  move => [e H].
  exists (fun n => F (e n)).
  move => f. destruct (H (G f)) as [c Hc].
  exists c. move => x y.
  rewrite /F bind_hasvalue. cbn in Hc. unfold partial.equiv in Hc.
  setoid_rewrite Hc.
  split.
  - move => [a [H1 H2]].
    destruct (PeanoNat.Nat.eqb_spec a 0); subst.
    + eapply ret_hasvalue_inv in H2. subst.
      rewrite /G in H1. eapply bind_hasvalue in H1 as [[] [H1 H2]].
      * eauto.
      * eapply ret_hasvalue_inv in H2; congruence.
    + eapply ret_hasvalue_inv in H2. subst.
      rewrite /G in H1. eapply bind_hasvalue in H1 as [[] [H1 H2]].
      * eapply ret_hasvalue_inv in H2; congruence.
      * eauto.
  - move => H1.
    exists (if y then 0 else 1). split.
    + rewrite /G bind_hasvalue. exists y; split; eauto. destruct y; eapply ret_hasvalue.
    + destruct y; eapply ret_hasvalue.
Qed.

End assm_part.
