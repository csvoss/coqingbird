Require Import Coqingbird.Chapter_9.

Definition bluebird B := forall x y z, B $ x $ y $ z = x $ (y $ z).

Theorem Problem_1 :
  forall B, bluebird B ->
            forall C D, exists E, composes C D E.
Proof.
  intros.
  exists (B $ C $ D).
  congruence.
Qed.

Theorem Problem_2 :
  forall B, bluebird B ->
            forall M, mockingbird M ->
                      forall x, exists Yx, fond x Yx.
Proof.
  (*Yx = M(x.M) = M(BxM)*)
  intros.
  exists (M $ (B $ x $ M)).
  congruence.
Qed.

Theorem Problem_3 :
  forall B, bluebird B -> forall M, mockingbird M ->
            exists E, egocentric E.
Proof.
  (*E = M(M.M) = M(BMM)*)
  intros.
  exists (M $ (B $ M $ M)).
  congruence.
Qed.

Theorem Problem_4 :
  forall B, bluebird B -> forall M, mockingbird M -> forall K, kestrel K ->
            exists HE, hopelessly_egocentric HE.
Proof.
  intros.
  exists (M $ (B $ K $ M)).
  congruence.
Qed.

Definition dove D := forall x y z w, D $ x $ y $ z $ w = x $ y $ (z $ w).

Theorem Problem_5 :
  forall B, bluebird B -> exists D, dove D.
Proof.
  intros.
  exists (B $ B).
  congruence.
Qed.

Definition blackbird B1 := forall x y z w, B1 $ x $ y $ z $ w = x $ (y $ z $ w).

Theorem Problem_6 :
  forall B, bluebird B -> exists B1, blackbird B1.
Proof.
  intros.
  exists (B $ B $ B).
  congruence.
Qed.

Definition eagle E := forall x y z w v, E $ x $ y $ z $ w $ v = x $ y $ (z $ w $ v).

Theorem Problem_7 :
  forall B, bluebird B -> exists E, eagle E.
Proof.
  intros.
  exists (B $ (B $ B $ B)).
  congruence.
Qed.

Definition bunting B2 := forall x y z w v, B2 $ x $ y $ z $ w $ v = x $ (y $ z $ w $ v).

Theorem Problem_8 :
  forall B, bluebird B -> exists B2, bunting B2.
Proof.
  intros.
  exists (B $ B $ (B $ B $ B)).
  congruence.
Qed.

Definition bunting' B2' := forall x y z w v u, B2' $ x $ y $ z $ w $ v $ u = x $ (y $ z $ w $ v $ u).

Theorem generalized_bunting :
  forall B, bluebird B -> exists B2', bunting' B2'.
Proof.
  intros.
  exists (B $ B $ (B $ B $ (B $ B $ B))).
  congruence.
Qed.

Definition dickcissel D1 := forall x y z w v, D1 $ x $ y $ z $ w $ v = x $ y $ z $ (w $ v).

Theorem Problem_9 :
  forall B, bluebird B -> exists D1, dickcissel D1.
Proof.
  intros.
  exists (B $ (B $ B)).
  congruence.
Qed.

Definition becard B3 := forall x y z w, B3 $ x $ y $ z $ w = x $ (y $ (z $ w)).

Theorem Problem_10 :
  forall B, bluebird B -> exists B3, becard B3.
Proof.
  intros.
  exists (B $ (B $ B) $ B).
  congruence.
Qed.

Definition dovekie D2 := forall x y z w v, D2 $ x $ y $ z $ w $ v = x $ (y $ z) $ (w $ v).

Theorem Problem_11 :
  forall B, bluebird B -> exists D2, dovekie D2.
Proof.
  intros.
  exists (B $ (B $ (B $ B)) $ B).
  congruence.
Qed.

Definition bald_eagle Ê := forall x y1 y2 y3 z1 z2 z3, Ê $ x $ y1 $ y2 $ y3 $ z1 $ z2 $ z3 = x $ (y1 $ y2 $ y3) $ (z1 $ z2 $ z3).

Lemma compose0 a b c :
  a = b ->
  a $ c = b $ c.
Proof.
  congruence.
Qed.

Lemma compose1 B a b c d :
  bluebird B ->
  a = B $ b $ c $ d ->
  a = b $ (c $ d).
Proof.
  congruence.
Qed.

Hint Resolve compose0 : compositor.
Hint Resolve compose1 : compositor.

Theorem Problem_12 :
  forall B, bluebird B -> exists Ê, bald_eagle Ê.
Proof.
  unfold bald_eagle.
  eauto 15 with compositor.
Qed.

Definition warbler W := forall x y, W $ x $ y = x $ y $ y.

Theorem Problem_14 :
  forall W I, warbler W -> identity I -> exists M, mockingbird M.
Proof.
  intros.
  exists (W $ I).
  congruence.
Qed.

Theorem Problem_15 :
  forall W K, warbler W -> kestrel K -> exists I, identity I.
Proof.
  intros.
  exists (W $ K).
  congruence.
Qed.

Theorem Problem_13 :
  forall W K, warbler W -> kestrel K -> exists M, mockingbird M.
Proof.
  (*Yes, the proof of this comes after Problems 14 and 15.*)
  intros.
  assert (exists I, identity I).
  eapply Problem_15.
  eassumption.
  eassumption.
  inversion H1.
  eapply Problem_14.
  eassumption.
  eassumption.
Qed.

Definition cardinal C := forall x y z, C $ x $ y $ z = x $ z $ y.

Theorem Problem_16 :
  forall C K, cardinal C -> kestrel K -> exists I, identity I.
Proof.
  intros.
  exists (C $ K $ K).
  congruence.
Qed.

Definition thrush T := forall x y, T $ x $ y = y $ x.


Lemma identity_hint I a b :
  identity I ->
  a = I $ b ->
  a = b.
Proof.
  congruence.
Qed.

Lemma identity_hint2 I a b c :
  identity I ->
  a = I $ b $ c ->
  a = b $ c.
Proof.
  congruence.
Qed.

Lemma kestrel_hint K a b c :
  kestrel K ->
  a = K $ b $ c ->
  a = b.
Proof.
  congruence.
Qed.

Lemma cardinal_hint C a b c d:
  cardinal C ->
  a = C $ b $ c $ d ->
  a = b $ d $ c.
Proof.
  congruence.
Qed.

Lemma apply_hint a b c d :
  a = b ->
  c = d ->
  a $ c = b $ d.
Proof.
  congruence.
Qed.

Hint Resolve identity_hint : bird_hints.
Hint Resolve identity_hint2 : bird_hints.
Hint Resolve kestrel_hint : bird_hints.
Hint Resolve cardinal_hint : bird_hints.
Hint Resolve apply_hint : bird_hints.


Theorem Problem_17 :
  forall C I, cardinal C -> identity I -> exists T, thrush T.
Proof.
  unfold thrush.
  eauto with bird_hints.
Qed.

(*Print Problem_17.*)

Theorem Problem_18 :
  forall T, thrush T -> (forall B, exists B', fond B B') -> exists A, forall x, A $ x = x $ A.
Proof.
  intros.
  destruct H0 with T as [E].
  exists E.
  congruence.
Qed.

Lemma mockingbird_hint M x x' a :
  mockingbird M ->
  a = M $ x ->
  x = x' ->
  a = x' $ x.
Proof.
  congruence.
Qed.

Lemma thrush_hint T x y a :
  thrush T ->
  a = T $ x $ y ->
  a = y $ x.
Proof.
  congruence.
Qed.

Hint Resolve mockingbird_hint : bird_hints.
Hint Resolve thrush_hint : bird_hints.
Hint Resolve compose1 : bird_hints.

Theorem Problem_19 :
  forall B T M, bluebird B -> thrush T -> mockingbird M ->
                exists A, forall x, A $ x = x $ A.
Proof.
  intros.
  exists (M $ (B $ T $ M)).
  congruence.
Qed.



(*end*)
