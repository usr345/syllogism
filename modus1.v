(* Все S есть P *)
Definition a (Universum: Type) (S: Universum -> Prop) (P: Universum -> Prop) : Prop := forall x: Universum, (S x -> P x).

(* Некоторые S есть P *)
Definition i (Universum: Type) (S: Universum -> Prop) (P: Universum -> Prop) : Prop := exists x: Universum, (S x /\ P x).

(* Все S не есть P *)
Definition e (Universum: Type) (S: Universum -> Prop) (P: Universum -> Prop) : Prop := forall x: Universum, S x -> not (P x).

(* Некоторые S не есть P *)
Definition o (Universum: Type) (S: Universum -> Prop) (P: Universum -> Prop) : Prop := exists x: Universum, S x -> not (P x).


Theorem Barbara : forall Universum: Type, forall (S M P: Universum -> Prop), forall x: Universum, a Universum M P -> a Universum S M -> a Universum S P.
Proof.
  intros Universum S M P x H1 H2. unfold a. intros x0 H3. apply H1. apply H2. apply H3.
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
  intros Universum S M P H1 H2. unfold o. unfold e in H1. unfold i in H2. destruct H2 as [x H2]. destruct H2 as [H21 H22]. exists x. intro H3. specialize (H1 x). apply H1 in H22. exact H22.
Qed.

Theorem Barbari : forall Universum: Type, forall (S M P: Universum -> Prop), forall x: Universum, a Universum M P -> a Universum S M -> (exists x0, S x0) -> i Universum S P.
Proof.
  intros Universum S M P x H1 H2 HE. unfold i. destruct HE as [x0 HS]. unfold a in H1. unfold a in H2. exists x0. split.
  - exact HS.
  - specialize (H2 x0). apply H2 in HS. specialize (H1 x0). apply H1 in HS. exact HS.
Qed.

Theorem Celaront : forall Universum: Type, forall (S M P: Universum -> Prop), forall x: Universum, e Universum M P -> a Universum S M -> (exists x0, S x0) -> o Universum S P.
Proof.
  intros Universum S M P x H1 H2 He. unfold o. unfold e in H1. unfold a in H2. destruct He. exists x0. intro H_. clear H_. specialize (H2 x0). apply H2 in H. specialize (H1 x0). apply H1 in H. exact H.
Qed.

(* 2-я фигура *)

Theorem Baroko : forall Universum: Type, forall (S M P: Universum -> Prop), forall x: Universum, a Universum P M -> o Universum S M -> o Universum S P.
Proof.
  intros Universum S M P x H1 H2. unfold o. unfold o in H2. destruct H2. exists x0. intro H2. apply H in H2. unfold a in H1. specialize (H1 x0). unfold not. intro H3. apply H1 in H3. apply H2 in H3. exact H3.
Qed.

Theorem Cesare : forall Universum: Type, forall (S M P: Universum -> Prop), forall x: Universum, e Universum P M -> a Universum S M -> e Universum S P.
Proof.
  intros Universum S M P x H1 H2. unfold e. intros x0 H3. unfold a in H2. specialize (H2 x0). apply H2 in H3. unfold e in H1. specialize (H1 x0). unfold not. intro HP. apply H1 in HP. contradiction.
Qed.

Theorem Camestres : forall Universum: Type, forall (S M P: Universum -> Prop), e Universum P M -> a Universum S M -> e Universum S P.
Proof.
  intros Universum S M P H1 H2. unfold e. intros x H3. unfold a in H2.
  specialize (H2 x). apply H2 in H3. clear H2. unfold e in H1. specialize (H1 x). intro HP. apply H1 in HP. contradiction.
Qed.
