(* Все S есть P *)
Definition a (Universum: Type) (S: Universum -> Prop) (P: Universum -> Prop) : Prop := forall x: Universum, (S x -> P x).

(* Некоторые S есть P *)
Definition i (Universum: Type) (S: Universum -> Prop) (P: Universum -> Prop) : Prop := exists x: Universum, (S x /\ P x).

(* Все S не есть P *)
Definition e (Universum: Type) (S: Universum -> Prop) (P: Universum -> Prop) : Prop := forall x: Universum, S x -> not (P x).

(* Некоторые S не есть P *)
Definition o (Universum: Type) (S: Universum -> Prop) (P: Universum -> Prop) : Prop := exists x: Universum, S x /\ not (P x).

Axiom ExclusionMiddle: forall P: Prop, P \/ ~P.

Theorem EquivO (Universum: Type) (S: Universum -> Prop) (P: Universum -> Prop) :
  o Universum S P <-> (exists x: Universum, (S x /\ not (P x))) \/ not(exists x: Universum, S x).
Proof.
  split.
  - unfold o. intros. destruct H. destruct (ExclusionMiddle (S x)).
    -- left. exists x. split.
       --- exact H0.
       --- apply H in H0. exact H0.
    -- right. intro.
Abort.

(* I фигура
M - P
S - M
-----
S - P
*)

Theorem Barbara : forall Universum: Type, forall (S M P: Universum -> Prop), a Universum M P -> a Universum S M -> a Universum S P.
Proof.
  intros Universum S M P H1 H2. unfold a. intros x H3. apply H1. apply H2. apply H3.
Qed.

Theorem Celarent : forall Universum: Type, forall (S M P: Universum -> Prop), e Universum M P -> a Universum S M -> e Universum S P.
Proof.
  intros. unfold e. intros. unfold not. intro. unfold e in H. apply (H x). - apply H0. exact H1.
 - exact H2.
Qed.

Theorem Darii : forall Universum: Type, forall (S M P: Universum -> Prop), a Universum M P -> i Universum S M -> i Universum S P.
Proof.
  intros Universum S M P H1 H2. unfold i. unfold a in H1. unfold i in H2. destruct H2 as [x H2]. destruct H2 as [H21 H22]. exists x. split.
  - exact H21.
  - specialize (H1 x) as H1. apply H1 in H22. exact H22.
Qed.

Theorem Ferio : forall Universum: Type, forall (S M P: Universum -> Prop), e Universum M P -> i Universum S M -> o Universum S P.
Proof.
  intros Universum S M P H1 H2. unfold o. unfold e in H1. unfold i in H2. destruct H2 as [x H2]. destruct H2 as [H21 H22]. exists x.
  specialize (H1 x). apply H1 in H22.
  exact (conj H21 H22).
Qed.

Theorem Barbari : forall Universum: Type, forall (S M P: Universum -> Prop), a Universum M P -> a Universum S M -> (exists x0, S x0) -> i Universum S P.
Proof.
  intros Universum S M P H1 H2 HE. unfold i. destruct HE as [x0 HS]. unfold a in H1. unfold a in H2. exists x0. split.
  - exact HS.
  - specialize (H2 x0). apply H2 in HS. specialize (H1 x0). apply H1 in HS. exact HS.
Qed.

Theorem Celaront : forall Universum: Type, forall (S M P: Universum -> Prop), e Universum M P -> a Universum S M -> (exists x0, S x0) -> o Universum S P.
Proof.
  intros Universum S M P H1 H2 He. unfold o. unfold e in H1. unfold a in H2. destruct He. exists x. specialize (H2 x). specialize (H1 x). apply H2 in H as H3.
  apply H1 in H3. apply (conj H H3).
Qed.

(* II фигура
M - P
S - M
-----
S - P
*)

Theorem Baroko : forall Universum: Type, forall (S M P: Universum -> Prop), a Universum P M -> o Universum S M -> o Universum S P.
Proof.
  intros Universum S M P H1 H2. unfold o. unfold o in H2. destruct H2. exists x. destruct H. unfold a in H1. specialize (H1 x). split.
  - exact H.
  - intro. apply H1 in H2. contradiction.
Qed.

Theorem Cesare : forall Universum: Type, forall (S M P: Universum -> Prop), e Universum P M -> a Universum S M -> e Universum S P.
Proof.
  intros Universum S M P H1 H2. unfold e. intros x H3. unfold a in H2. specialize (H2 x). apply H2 in H3. unfold e in H1. specialize (H1 x). unfold not. intro HP. apply H1 in HP. contradiction.
Qed.

Theorem Camestres : forall Universum: Type, forall (S M P: Universum -> Prop), e Universum P M -> a Universum S M -> e Universum S P.
Proof.
  intros Universum S M P H1 H2. unfold e. intros x H3. unfold a in H2.
  specialize (H2 x). apply H2 in H3. clear H2. unfold e in H1. specialize (H1 x). intro HP. apply H1 in HP. contradiction.
Qed.

Theorem Festino : forall Universum: Type, forall (S M P: Universum -> Prop), e Universum P M -> i Universum S M -> o Universum S P.
Proof.
  intros Universum S M P H1 H2. unfold o. unfold i in H2. destruct H2. destruct H. exists x. unfold e in H1. specialize (H1 x). split.
  - exact H.
  - unfold not. unfold not in H1. intro. exact (H1 H2 H0).
Qed.

Theorem Camestrop : forall Universum: Type, forall (S M P: Universum -> Prop), a Universum P M -> e Universum S M -> (exists x0, S x0) -> o Universum S P.
Proof.
  intros Universum S M P H1 H2 HE. unfold o. destruct HE. exists x. unfold a in H1. unfold e in H2. split ; auto. intro. apply (H2 x H).
  apply H1. apply H0.
Qed.

Theorem Cesaro : forall Universum: Type, forall (S M P: Universum -> Prop), e Universum P M -> a Universum S M -> (exists x0, S x0) -> o Universum S P.
Proof.
  intros Universum S M P H1 H2 HE. unfold o. destruct HE. exists x. unfold e in H1. unfold a in H2. split.
  - exact H.
  - specialize (H1 x). specialize (H2 x). apply H2 in H. intro HP. apply H1 in HP. contradiction.
Qed.

(* III фигура
M - P
S - S
-----
S - P
*)


Theorem Bokardo : forall Universum: Type, forall (S M P: Universum -> Prop), o Universum M P -> a Universum M S -> o Universum S P.
Proof.
  intros Universum S M P H1 H2. unfold o in H1. destruct H1 as [x H1]. unfold o. exists x.
  unfold a in H2. specialize (H2 x). destruct H1 as [H11 H12]. apply H2 in H11. apply (conj H11 H12).
Qed.

Theorem Disamis: forall Universum: Type, forall (S M P: Universum -> Prop), i Universum M P -> a Universum M S -> i Universum S P.
Proof.
  intros Universum S M P H1 H2. unfold i in H1. destruct H1 as [x H1].
  destruct H1 as [H11 H12]. unfold a in H2. unfold i. exists x. specialize (H2 x). apply H2 in H11. split.
  - exact H11.
  - exact H12.
Qed.

Theorem Datisi: forall Universum: Type, forall (S M P: Universum -> Prop), a Universum M P -> i Universum M S -> i Universum S P.
Proof.
  intros Universum S M P H1 H2. unfold i in H2. destruct H2 as [x H2]. destruct H2 as [H21 H22]. unfold a in H1. specialize (H1 x). apply H1 in H21.
  unfold i. exists x. apply (conj H22 H21).
Qed.

Theorem Ferison: forall Universum: Type, forall (S M P: Universum -> Prop), e Universum M P -> i Universum M S -> o Universum S P.
Proof.
  intros Universum S M P H1 H2. unfold e in H1.  unfold i in H2. destruct  H2 as [x H2]. destruct H2 as [H21 H22]. unfold o. exists x. specialize (H1 x).
apply H1 in H21. apply (conj H22 H21).
Qed.

Theorem Darapti: forall Universum: Type, forall (S M P: Universum -> Prop), a Universum M P -> a Universum M S -> (exists x0, M x0) -> i Universum S P.
Proof.
  intros Universum S M P H1 H2 HE. unfold a in H1. unfold a in H2. destruct HE as [x0 H3]. unfold i. exists x0. specialize (H1 x0). specialize (H2 x0). split.
  - apply H2 in H3. exact H3.
  - apply H1 in H3. exact H3.
Qed.

Theorem Felapton: forall Universum: Type, forall (S M P: Universum -> Prop), e Universum M P -> a Universum M S -> (exists x0, M x0) -> o Universum S P.
Proof.
  intros Universum S M P H1 H2 HE. unfold e in H1. unfold a in H2. destruct HE as [x0 H3]. unfold o. exists x0. specialize (H1 x0). specialize (H2 x0). specialize (H1 H3) as H1. specialize (H2 H3) as H2. apply (conj H2 H1).
Qed.

(* IV фигура
P - M
M - S
-----
S - P
*)

Theorem Camenos: forall Universum: Type, forall (S M P: Universum -> Prop), a Universum P M -> e Universum M S -> (exists x0, S x0) -> o Universum S P.
Proof.
  intros Universum S M P H1 H2 HE. unfold e in H2. unfold a in H1. unfold o. destruct HE as [x0 H3]. specialize (H1 x0). specialize (H2 x0). exists x0. split.
  - exact H3.
  - intro. apply H1 in H. apply H2 in H. apply H in H3. exact H3.
Qed.

Theorem Dimaris: forall Universum: Type, forall (S M P: Universum -> Prop), i Universum P M -> a Universum M S -> i Universum S P.
Proof.
  intros Universum S M P H1 H2. unfold i in H1. unfold a in H2. destruct H1 as [x H1]. specialize (H2 x). unfold i. exists x. destruct H1 as [H11 H12]. split.
  - apply H2 in H12. exact H12.
  - exact H11.
Qed.

Theorem Camenes: forall Universum: Type, forall (S M P: Universum -> Prop), a Universum P M -> e Universum M S -> e Universum S P.
Proof.
  intros Universum S M P H1 H2. unfold a in H1. unfold e in H2. unfold e.
  intros. specialize (H1 x). specialize (H2 x). intros H3. apply H1 in H3. apply H2 in H3. contradiction.
Qed.

Theorem Fresison: forall Universum: Type, forall (S M P: Universum -> Prop), e Universum P M -> i Universum M S -> o Universum S P.
Proof.
  intros Universum S M P H1 H2. unfold e in H1. unfold i in H2. unfold o. destruct H2 as [x H2]. specialize (H1 x). exists x. destruct H2 as [H21 H22]. split.
  - exact H22.
  - intro. apply H1 in H. contradiction.
Qed.

Theorem Bramantip: forall Universum: Type, forall (S M P: Universum -> Prop), a Universum P M -> a Universum M S -> (exists x0, P x0) -> i Universum S P.
Proof.
  intros Universum S M P H1 H2 HE. unfold a in H1. unfold a in H2. unfold i. destruct HE as [x0 H3]. exists x0. specialize (H1 x0). specialize (H2 x0). apply H1 in H3 as H4. apply H2 in H4. apply (conj H4 H3).
Qed.

Theorem Fesapo: forall Universum: Type, forall (S M P: Universum -> Prop), e Universum P M -> a Universum M S -> (exists x0, M x0) -> o Universum S P.
Proof.
  intros Universum S M P H1 H2 HE. unfold e in H1. unfold a in H2. unfold o. destruct HE as [x0 H3]. exists x0. specialize (H1 x0). specialize (H2 x0). split.
  - apply H2 in H3. exact H3.
  - intro. apply H1 in H. contradiction.
Qed.
