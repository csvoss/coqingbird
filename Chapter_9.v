(* Authors: Anders Kaseorg, Chelsea Voss. *)

Axiom Bird : Type.
Axiom Call : Bird -> Bird -> Bird.

Notation "A $ B" := (Call A B) (at level 50).

Definition composes A B C : Prop :=
  forall x, C $ x = A $ (B $ x).
Definition is_compose compose := forall A B, composes A B (compose A B).

Definition mockingbird M : Prop :=
  forall x, M $ x = x $ x.

Definition fond A B : Prop := A $ B = B.

Theorem Problem_1 :
  forall compose,
    is_compose compose ->
    forall M,
      mockingbird M ->
      forall A, exists B, fond A B.
Proof.
  intros.
  exists (M $ compose A M).
  congruence.
Qed.
(*YA*)

Definition egocentric x : Prop := x $ x = x.

Theorem Problem_2 : 
  forall compose,
    is_compose compose ->
    forall M,
      mockingbird M ->
      exists e, egocentric e.
Proof.
  intros.
  exists (M $ compose M M).
  congruence.
Qed.

Definition agree A B x : Prop := A $ x = B $ x.

Definition agreeable A : Prop := forall B, exists x, agree A B x.

Theorem Problem_3 :
  forall compose,
    is_compose compose ->
    forall A,
      agreeable A ->
      forall B, exists C, fond B C.
Proof.
  intros.
  destruct H0 with (compose B A) as [D].
  exists (A $ D).
  congruence.
Qed.

Theorem Problem_4 :
  forall compose,
    is_compose compose ->
    forall A B C,
      composes A B C ->
      agreeable C ->
      agreeable A.
Proof.
  intros.
  intro D.
  destruct H1 with (compose D B) as [x].
  exists (B $ x).
  congruence.
Qed.
  
Theorem Problem_5 :
  forall compose,
    is_compose compose ->
    forall A B C,
    exists D,
      forall x,
        D $ x = A $ (B $ (C $ x)).
Proof.
  intros.
  exists (compose A (compose B C)).
  congruence.
Qed.

Definition compatible A B : Prop := exists x y, A $ x = y /\ B $ y = x.

Theorem Problem_6 :
  forall compose,
    is_compose compose ->
    forall M,
      mockingbird M ->
      forall A B, compatible A B.
Proof.
  intros.
  exists (M $ compose (compose B A) M).
  exists (A $ (M $ compose (compose B A) M)).
  split; congruence.
Qed.

Definition happy A : Prop := compatible A A.

Theorem Problem_7 :
  forall A B, fond A B -> happy A.
Proof.
  intros.
  exists B, B.
  split; congruence.
Qed.

Definition normal A := exists B, fond A B.

Theorem Problem_8 :
  forall compose,
    is_compose compose ->
    forall Ha,
      happy Ha ->
      exists N, normal N.
Proof.
  intros.
  exists (compose Ha Ha).
  destruct H0.
  exists x.
  destruct H0.
  destruct H0.
  congruence.
Qed.

Definition fixated A B := forall y, A $ y = B.

Definition hopelessly_egocentric B := fixated B B.

Definition kestrel K := forall x, fixated (K $ x) x.

Theorem Problem_9 : 
  forall compose,
    is_compose compose ->
    forall M,
      mockingbird M ->
      forall K,
        kestrel K ->
        exists B, hopelessly_egocentric B.
Proof.
  intros.
  exists (M $ compose K M).
  congruence.
Qed.

Theorem Problem_10 :
  forall x y, fixated x y -> fond x y.
Proof.
  congruence.
Qed.

Theorem Problem_11 :
  forall K, kestrel K -> egocentric K -> hopelessly_egocentric K.
Proof.
  congruence.
Qed.

Theorem Problem_12 :
  forall K, kestrel K -> forall x, egocentric (K $ x) -> fond K x.
Proof.
  congruence.
Qed.

Theorem Problem_13 :
  forall A, hopelessly_egocentric A -> forall x y, A $ x = A $ y.
Proof.
  congruence.
Qed.

Theorem Problem_14 :
  forall A, hopelessly_egocentric A -> forall x y, A $ x $ y = A.
Proof.
  congruence.
Qed.

Theorem Problem_15 :
  forall A, hopelessly_egocentric A -> forall x, hopelessly_egocentric (A $ x).
Proof.
  congruence.
Qed.

Theorem Problem_16 :
  forall K, kestrel K -> forall x y, K $ x = K $ y -> x = y.
Proof.
  intros.
  replace x with (K $ x $ K); congruence.
Qed.

Theorem Problem_17 :
  forall B x y, fixated B x -> fixated B y -> x = y.
Proof.
  intros.
  replace x with (B $ B); congruence.
Qed.

Theorem Problem_18 :
  forall K, kestrel K -> forall x, fond K (K $ x) -> fond K x.
Proof.
  intros.
  apply Problem_16 with K; congruence.
Qed.

Definition lonely (B : Bird) : Prop := forall x, B = x.

Theorem Problem_19 :
  forall K, kestrel K -> egocentric K -> lonely K.
Proof.
  intros.
  intro.
  apply Problem_16 with K; congruence.
Qed.

Definition identity I := forall x, I $ x = x.

Theorem Problem_20 :
  forall I, identity I -> agreeable I -> forall B, exists x, fond B x.
Proof.
  intros.
  destruct H0 with B.
  exists x.
  congruence.
Qed.

Theorem Problem_21 :
  forall I, identity I -> (forall B, exists x, fond B x) -> agreeable I.
Proof.
  intros.
  intro.
  destruct H0 with B.
  exists x.
  congruence.
Qed.

Theorem Problem_22 :
  forall I, identity I ->
            (forall A B, compatible A B) ->
            (forall C, normal C) /\ agreeable I.
Proof.
  split.
  - intros.
    destruct H0 with C I.
    exists x.
    destruct H1.
    destruct H1.
    congruence.
  - intro B.
    destruct H0 with B I.
    exists x.
    destruct H1.
    destruct H1.
    congruence.
Qed.

Theorem Problem_23 :
  forall I, identity I -> hopelessly_egocentric I -> lonely I.
Proof.
  congruence.
Qed.

Definition lark L := forall x y, (L $ x) $ y = x $ (y $ y).

Theorem Problem_24 :
  forall L, lark L -> forall I, identity I -> exists M, mockingbird M.
Proof.
  intros.
  exists (L $ I).
  congruence.
Qed.

Theorem Problem_25 :
  forall L, lark L -> forall A, exists B, fond A B.
Proof.
  intros.
  exists (L $ A $ (L $ A)).
  congruence.
Qed.

Definition attractive A := forall B, fond B A.

Theorem Problem_26 :
  forall L, lark L -> hopelessly_egocentric L -> attractive L.
Proof.
  intros.
  intro.
  transitivity (L $ L); congruence.
Qed.

Theorem Problem_27 :
  forall L, lark L -> forall K, kestrel K -> fond L K -> exists B, lark B /\ kestrel B.
Proof.
  intros.
  replace L with K in H.
  - exists K; tauto.
  - apply Problem_19; congruence.
Qed.

Theorem Problem_28 :
  forall K, kestrel K -> forall L, lark L -> fond K L -> forall B, fond B L.
Proof.
  intros.
  apply Problem_26; congruence.
Qed.

Theorem Problem_29 :
  forall L, lark L -> exists B, egocentric B.
Proof.
  intros.
  exists (L $ L $ L $ (L $ L $ L) $ (L $ L $ L $ (L $ L $ L))).
  congruence.
Qed.

(*End*)
