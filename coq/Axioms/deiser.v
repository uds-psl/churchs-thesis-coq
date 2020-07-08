Require Import stdpp.list Synthetic.DecidabilityFacts Synthetic.EnumerabilityFacts reductions partial axioms ssreflect Nat principles kleenetree Synthetic.Infinite.
Require Import SyntheticComputability.Axioms.baire_cantor.

Definition to_bitlist (n : nat) : list bool := Nat.iter n (cons true) [].

Lemma bitlist_false a : ~ In false (to_bitlist a).
Proof.
  induction a; cbn; firstorder.
Qed.

(* lists of natural numbers to bitlists, [ n1, ... n2 ] |-> 1^n1 0 ... 1^n2 0 *)
Fixpoint f_s (x : list nat) : list bool :=
  match x with
  | nil => nil
  | a :: x => to_bitlist a ++ [false] ++ f_s x
  end.

Lemma f_s_app x y : f_s (x ++ y) = f_s x ++ f_s y.
Proof.
  induction x; cbn. 
  - reflexivity.
  - rewrite IHx. now rewrite <- app_assoc.
Qed.

(* interpretation of a bitlist as list of natural numbers *)
Fixpoint g_s' (x : list bool) (n : nat) : list nat :=
  match x with
  | nil => nil
  | true :: x' => g_s' x' (S n)
  | false :: x' => n :: g_s' x' 0
  end.

Lemma g_s'_app n x y :
  g_s' (f_s x ++ y) n = match x with nil => g_s' y n | m :: x => n + m :: x ++ g_s' y 0 end.
Proof.
  revert n y. induction x as [ | m]; intros; cbn in *.
  - reflexivity.
  - revert n; induction m; intros; cbn in *.
    + destruct x.
      * do 2 f_equal. lia.
      * rewrite IHx. f_equal. lia.
    + rewrite IHm. f_equal. lia.
Qed.

Definition g_s x := g_s' x 0.

Lemma f_g_s'_inv x : g_s (f_s x) = x.
Proof.
  unfold g_s. setoid_rewrite <- app_nil_r at 2. rewrite g_s'_app.
  destruct x; eauto. cbn. now rewrite app_nil_r.
Qed.

Lemma WKL_to :
  WKL -> forall τ : list nat -> Prop, τ [] -> (forall u1 u2, prefix u1 u2 -> τ u2 -> τ u1) -> (forall k, exists u, τ u /\ length u >= k) -> exists f, forall n, τ (map f (seq 0 n)).
Proof.
  intros wkl τ τ_nil τ_pref τ_inf.
  unshelve epose proof (wkl _ _) as [f Hf]. all: cbn in *.
  - exists (fun u => exists v, prefix u (f_s v) /\ τ v). econstructor.
    + exists [], []. cbn. eauto.
    + intros u1 ? [u2 ->] (v & Hv1 & Hv2).
      exists v. split; eauto.
      eapply prefix_app_l. eassumption.
    + eapply decidable_iff. econstructor.
      intros u. eapply listable_exists_dec. eapply listable_prefix.
  - intros k. destruct (τ_inf k) as (u & Hu & Hl).
    exists (f_s u). split.
    + exists u, 0. cbn. rewrite app_nil_r. eauto.
    + admit.
  - cbn in *.
    

Definition is_even_end (l : list bool) := true.

Definition droplast {X} (l : list X) : list X := [].

Fixpoint F' f m {struct m} :=
  match m with
  | 0 => []
  | S 0 => match f 0 with
          | 0 => [false; false]
          | S n => repeat false n ++ [true]
          end
  | S (S m as Sm) => match f Sm, f m with
              | 0, _   => F' f Sm ++ [false; false]
              | S n, 0 => F' f Sm ++ [true] ++ repeat false (2 * (S n) - 1) ++ [true]
              | S n, _ => if is_even_end (droplast (F' f Sm))
                         then F' f Sm ++ repeat false (2 * n) ++ [true]
                         else F' f Sm ++ repeat false n ++ [true]
              end
  end.

Definition F f m := nth m (F' f (S m)) false.

Lemma F_inj_help f1 f2 :
  F f1 ≡{nat -> bool} F f2 -> forall k, take k (F' f1 k) = take k (F' f2 k).
Admitted.

Lemma F_inj f1 f2 :
  F f1 ≡{_} F f2 -> f1 ≡{_} f2.
Proof.
  intros H n. cbn. induction n.
  - pose proof (F_inj_help _ _ H ).
    specialize (H0 2). cbn in H0.
    destruct (f1 0) eqn:E1, (f2 0) eqn:E2.
    + reflexivity.
    + destruct (f1 1), (f2 1).
      * destruct n; cbn in H0. inv H0.
        destruct n; cbn in H0. inv H0.
        destruct n; cbn in H0. inv H0.
        destruct n; cbn in H0. inv H0.

        destruct n; cbn in H0. inv H0.
        
      cbn in *.
