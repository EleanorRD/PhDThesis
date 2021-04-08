(******************************************************************************)
(*     Postcondition-Preserving Fusion of Graph Transformations               *)
(*                                                                            *)
(* pairwise fusion for inductive graphs                                       *)
(*                                                                            *)
(* Eleanor Davies, 2021 (using Coq 8.13.1)                                    *)
(******************************************************************************)

(* Modules to import *)
Require Import Basics. (* for compose *)

(* Notation to make lists look nicer *)
Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

(******************************************************************************)
(* Inductive Graphs and Transformations                                       *)
(******************************************************************************)

(* Arbitrary set of node labels *)
Inductive X. (* labels for nodes *)

(* Inductive graph type *)
Definition Id := nat.
Definition Ctxt := ((list Id) * Id * X * (list ID))%type.
Inductive Graph := Empty | Amp : Ctxt -> Graph -> Graph.

(* Apply a graph transformation recursively *)
Fixpoint transform (f : Graph -> Graph) (g : Graph) : Graph :=
  match g with
    | Empty       => f Empty
    | Amp ctxt g' => f (Amp ctxt (transform f g'))
  end.

(* Apply two graph transformations in the same traversal *)
Definition fused (f1 f2 : Graph -> Graph) (g : Graph) : Graph :=
  transform (compose f2 f1) g.

(******************************************************************************)
(* Postconditions                                                             *)
(******************************************************************************)

(* Recursively check a postcondition on a graph *)
Fixpoint check (p : Graph -> Prop) (g : Graph) : Prop :=
  match g with
    | Empty       => p Empty
    | Amp ctxt g' => p (Amp ctxt g') /\ check p g'
  end.

Definition subgraph (g : Graph) : option Graph :=
  match g with
    | Empty    => None
    | Amp _ g' => Some g'
  end.

Definition ifexists (p : Graph -> Prop) (g : option Graph) : Prop :=
  match g with
    | None    => True
    | Some g' => p g'
  end.

(* Assert that a graph transformation satisfies its postcondition *)
Definition satisfies (f : Graph -> Graph) (p : Graph -> Prop) : Prop :=
  forall (g : Graph), ifexists (check p) (subgraph g) -> check p (f g).

(******************************************************************************)
(* Criteria for Successful Fusion                                             *)
(******************************************************************************)

(* The second graph transformation should preserve the first postcondition *)
Definition FC1 (f2 : Graph -> Graph) (p1 : Graph -> Prop) : Prop :=
  forall (g : Graph), check p1 g -> check p1 (f2 g).

(* Any children introduced by the first graph transformation should maintain *)
(* the second postcondition                                                  *)
Definition FC2 (f1 : Graph -> Graph) (p2 : Graph -> Prop) : Prop :=
  forall (g : Graph), ifexists (check p2) (subgraph g)
    -> ifexists (check p2) (subgraph (f1 g)).

(* Subject to FC1, the first postcondition will be preserved *)
Lemma L1: forall (f1 f2 : Graph -> Graph) (p1 : Graph -> Prop) (g : Graph),
  satisfies f1 p1 -> FC1 f2 p1 -> check p1 (fused f1 f2 g).
Proof.
  intros.
  induction g; apply H0; apply H; simpl; auto.
Qed.

(* Subject to FC2, the second postcondition will be preserved *)
Lemma L2: forall (f1 f2 : Graph -> Graph) (p2 : Graph -> Prop) (g : Graph),
  satisfies f2 p2 -> FC2 f1 p2 -> check p2 (fused f1 f2 g).
Proof.
  intros.
  induction g; apply H; apply H0; simpl; auto.
Qed.

(* Successful fusion means that subject to our criteria both postconditions *)
(* are fulfilled by the result                                              *)
Theorem successfulFusion:
  forall (f1 f2 : Graph -> Graph) (p1 p2 : Graph -> Prop) (g : Graph),
    satisfies f1 p1 -> satisfies f2 p2 -> FC1 f2 p1 -> FC2 f1 p2
      -> check p1 (fused f1 f2 g) /\ check p2 (fused f1 f2 g).
Proof.
  intros.
  split.
  { apply L1; auto. }
  { apply L2; auto. }
Qed.

