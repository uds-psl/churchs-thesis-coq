From SyntheticComputability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts.
From SyntheticComputability.Shared Require Import ListAutomation.
Require Import List.
Import ListNotations.

Lemma enumerable_enum {X} {p : X -> Prop} :
  enumerable p <-> list_enumerable p.
Proof.
  split. eapply enumerable_list_enumerable. eapply list_enumerable_enumerable.
Qed.

Hint Extern 4 => match goal with [H : list_enumerator _ ?p |- ?p _ ] => eapply H end : core.

Lemma enumerable_conj X (p q : X -> Prop) :
  discrete X -> enumerable p -> enumerable q -> enumerable (fun x => p x /\ q x).
Proof.
  intros [D] % discrete_iff [Lp] % enumerable_list_enumerable [Lq] % enumerable_list_enumerable.
  eapply list_enumerable_enumerable.
  exists (fun n => [ x | x ∈ cumul Lp n, x el cumul Lq n]).
  intros. split.
  + intros []. eapply (cumul_spec H) in H1 as [m1]. eapply (cumul_spec H0) in H2 as [m2].
    exists (m1 + m2). in_collect x.
    eapply cum_ge'; eauto. lia.
    eapply cum_ge'; eauto. lia.
  + intros [m].
    inv_collect; eauto.
Qed.

Lemma enumerable_disj X (p q : X -> Prop) :
  enumerable p -> enumerable q -> enumerable (fun x => p x \/ q x).
Proof.
  intros [Lp H] % enumerable_enum [Lq H0] % enumerable_enum.
  eapply enumerable_enum.
  exists (fun n => [ x | x ∈ Lp n] ++ [ y | y ∈ Lq n]).
  intros x. split.
  - intros [H1 | H1].
    * eapply H in H1 as [m]. exists m. in_app 1. in_collect x. eauto.
    * eapply H0 in H1 as [m]. exists m. in_app 2. in_collect x. eauto.
  - intros [m]. 
    inv_collect; eauto.
Qed.


