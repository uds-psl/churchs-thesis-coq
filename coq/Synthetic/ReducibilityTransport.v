Require Import DecidabilityFacts SemiDecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts reductions.

Lemma semidecidable_red X Y (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ₘ q -> semi_decidable q -> semi_decidable p.
Proof.
  intros [f Hf] [g Hg].
  exists (fun x n => g (f x) n). firstorder.
Qed.

Lemma enumerable_red X Y (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ₘ q -> enumerable__T X -> discrete Y -> enumerable q -> enumerable p.
Proof.
  intros. eapply semi_decidable_enumerable; eauto using semidecidable_red, enumerable_semi_decidable.
Qed.
