Require Import Coqingbird.Chapter_9.

Definition composer M A := forall x, composes x M (A $ x).

Theorem sage_bird :
  forall compose,
    is_composer compose ->
    forall M,
      mockingbird M ->
      forall A,
        composer M A ->
        exists Θ, forall x, fond x (Θ $ x).
Proof.
  intros.
  exists (compose M A).
  congruence.
Qed.

Theorem mockingbird_composer_is_lark :
  forall M,
    mockingbird M ->
    forall A,
      composer M A <-> lark A.
Proof.
  split; congruence.
Qed.
