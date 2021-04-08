(******************************************************************************)
(*     Postcondition-Preserving Fusion of Postorder Tree Transformations      *)
(*                                                                            *)
(* pairwise and multiple fusion for binary trees                              *)
(*                                                                            *)
(* Eleanor Davies, 2021 (using Coq 8.13.1)                                    *)
(******************************************************************************)

(* Modules to import *)
Require Import List.   (* for Forall *)
Require Import Basics. (* for compose *)

(* Notation to make lists look nicer *)
Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

(******************************************************************************)
(* Binary Trees and Transformations                                           *)
(******************************************************************************)

(* Arbitrary sets of tree labels *)
Inductive X. (* labels for inner nodes *)
Inductive Y. (* labels for leafs *)

(* Binary tree type *)
Inductive Tree := Leaf : Y -> Tree | Node : X -> Tree -> Tree -> Tree.

(* Get a list of the children of a tree *)
Definition children (t : Tree) : list Tree :=
  match t with
    | Leaf y     => [ ]
    | Node x L R => [L, R]
  end.

(* Apply a tree transformation recursively, with a postorder traversal *)
Fixpoint transform (f : Tree -> Tree) (t : Tree) : Tree :=
  match t with
    | Leaf y     => f (Leaf y)
    | Node x L R => f (Node x (transform f L) (transform f R))
  end.

(* Apply two tree transformations in the same traversal *)
Definition fused (f1 f2 : Tree -> Tree) (t : Tree) : Tree :=
  transform (compose f2 f1) t.

(******************************************************************************)
(* Postconditions                                                             *)
(******************************************************************************)

(* Recursively check a postcondition on a tree *)
Fixpoint check (p : Tree -> Prop) (t : Tree) : Prop :=
  match t with
    | Leaf y     => p (Leaf y)
    | Node x L R => p (Node x L R) /\ check p L /\ check p R
  end.

(* Assert that a tree transformation satisfies its postcondition *)
Definition satisfies (f : Tree -> Tree) (p : Tree -> Prop) : Prop :=
  forall (t : Tree), Forall (check p) (children t) -> check p (f t).

(******************************************************************************)
(* Criteria for Successful Fusion                                             *)
(******************************************************************************)

(* The second tree transformation should preserve the first postcondition *)
Definition FC1 (f2 : Tree -> Tree) (p1 : Tree -> Prop) : Prop :=
  forall (t : Tree), check p1 t -> check p1 (f2 t).

(* Any children introduced by the first tree transformation should maintain *)
(* the second postcondition                                                 *)
Definition FC2 (f1 : Tree -> Tree) (p2 : Tree -> Prop) : Prop :=
  forall (t : Tree), Forall (check p2) (children t)
    -> Forall (check p2) (children (f1 t)).

(* Subject to FC1, the first postcondition will be preserved *)
Lemma L1: forall (f1 f2 : Tree -> Tree) (p1 : Tree -> Prop) (t : Tree),
  satisfies f1 p1 -> FC1 f2 p1 -> check p1 (fused f1 f2 t).
Proof.
  intros.
  induction t; apply H0; apply H; simpl; auto.
Qed.

(* Subject to FC2, the second postcondition will be preserved *)
Lemma L2: forall (f1 f2 : Tree -> Tree) (p2 : Tree -> Prop) (t : Tree),
  satisfies f2 p2 -> FC2 f1 p2 -> check p2 (fused f1 f2 t).
Proof.
  intros.
  induction t; apply H; apply H0; simpl; auto.
Qed.

(* Successful fusion means that subject to our criteria both postconditions *)
(* are fulfilled by the result                                              *)
Theorem successfulFusion:
  forall (f1 f2 : Tree -> Tree) (p1 p2 : Tree -> Prop) (t : Tree),
    satisfies f1 p1 -> satisfies f2 p2 -> FC1 f2 p1 -> FC2 f1 p2
      -> check p1 (fused f1 f2 t) /\ check p2 (fused f1 f2 t).
Proof.
  intros.
  split.
  { apply L1; auto. }
  { apply L2; auto. }
Qed.

(******************************************************************************)
(* Fusing Three or More Transformations                                       *)
(******************************************************************************)

(* Compose a list of tree transformations *)
Fixpoint compose_list (fs : list (Tree -> Tree)) : Tree -> Tree :=
    match fs with
      | [ ]        => fun t : Tree => t
      | cons f fs' => fun t : Tree => compose (compose_list fs') f t
    end.

(* Apply two tree transformations in the same traversal *)
Definition fused_list (fs : list (Tree -> Tree)) (t : Tree) : Tree :=
  transform (compose_list fs) t.

Definition afterFC1 (p : Tree -> Prop) (fs : list (Tree -> Tree)) : Prop :=
    Forall (fun x => FC1 x p) fs.

Definition beforeFC2 (p : Tree -> Prop) (fs : list (Tree -> Tree)) : Prop :=
    Forall (fun x => FC2 x p) fs.

Lemma unrollComposeList : forall
  (xs ys : list (Tree -> Tree)) (t : Tree),
    compose_list (xs ++ ys) t = (compose_list ys) ((compose_list xs) t).
Proof.
  intros until xs.
  induction xs.
  { auto. }
  { intros. simpl. apply IHxs. }
Qed.

Lemma afterFC1Preserves: forall (fs : list (Tree -> Tree))
  (p : Tree -> Prop) (t : Tree),
    check p t -> afterFC1 p fs -> check p (compose_list (rev fs) t).
Proof.
  intros until p.
  induction fs.
  { auto. }
  { intros.
    inversion_clear H0.
    simpl.
    rewrite unrollComposeList.
    apply H1.
    apply IHfs; auto.
  }
Qed.

Lemma lemAfter:
  forall (after : list (Tree -> Tree)) (f : Tree -> Tree) (p : Tree -> Prop),
    afterFC1 p after -> satisfies f p
      -> forall (t : Tree), check p (fused_list (cons f (rev after)) t).
Proof.
  intros until f.
  intro.
  intro.
  induction after.
  { induction t; apply H0; simpl; auto. }
  { induction t.
    { unfold fused_list.
      unfold transform.
      simpl.
      unfold compose.
      rewrite unrollComposeList.
      inversion_clear H.
      apply H1.
      apply IHafter with (t := Leaf y); auto.
    }
    { unfold fused_list.
      unfold transform.
      fold transform.
      simpl.
      unfold compose.
      rewrite unrollComposeList.
      inversion_clear H.
      apply H1.
      apply afterFC1Preserves; auto.
      apply H0.
      simpl.
      auto.
    }
  }
Qed.

Lemma beforeFC2Preserves: forall (fs : list (Tree -> Tree))
  (p : Tree -> Prop) (t : Tree),
    Forall (check p) (children t) -> beforeFC2 p fs 
      -> Forall (check p) (children (compose_list fs t)).
Proof.
  intros until p.
  induction fs.
  { auto. }
  { intros.
    inversion_clear H0.
    simpl.
    unfold compose.
    apply IHfs; auto.
  }
Qed.

Lemma successfulMultiFusion : forall (before : list (Tree -> Tree))
  (f : Tree -> Tree) (after : list (Tree -> Tree))
  (p : Tree -> Prop) (t : Tree),
    beforeFC2 p before -> afterFC1 p after -> satisfies f p
      -> check p (fused_list (before ++ [f] ++ (rev after)) t).
Proof.
  intros until after.
  induction before.
  { intros. apply lemAfter; auto. }
  { intros.
    unfold fused_list.
    induction t.
    { unfold transform.
      rewrite 2 unrollComposeList.
      simpl.
      unfold compose.
      inversion_clear H.
      apply afterFC1Preserves; auto.
      apply H1.
      apply beforeFC2Preserves; auto.
      apply H2.
      simpl.
      auto.
    }
    { unfold transform.
      fold transform.
      rewrite 2 unrollComposeList.
      simpl.
      unfold compose.
      inversion_clear H.
      apply afterFC1Preserves; auto.
      apply H1.
      apply beforeFC2Preserves; auto.
      apply H2.
      simpl.
      auto.
    }
  }
Qed.

(******************************************************************************)
(* Simple Tree Evaluation                                                     *)
(******************************************************************************)

Inductive Value.

Axiom leafVal : Y -> Value.
Axiom nodeVal : X -> Value -> Value -> Value.

Fixpoint eval (t : Tree) : Value :=
  match t with
    | Leaf y     => leafVal y
    | Node x L R => nodeVal x (eval L) (eval R)
  end.

Definition preservesEval (f : Tree -> Tree) : Prop :=
  forall (t : Tree), eval (f t) = eval t.

Theorem preservesPreservesEval :
  forall (f1 f2 : Tree -> Tree) (t : Tree),
    preservesEval f1 -> preservesEval f2
      -> eval t = eval (fused f1 f2 t).
Proof.
  intros.
  induction t.
  { unfold fused. unfold compose. simpl.
    rewrite H0. rewrite H. auto.
  }
  { unfold fused. unfold compose. simpl.
    rewrite H0. rewrite H.
    rewrite IHt1. rewrite IHt2. auto.
  }
Qed.
