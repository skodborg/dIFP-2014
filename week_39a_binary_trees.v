(* week_39a_binary_trees.v *)
(* dIFP 2014-2015, Q1, Week 38 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* ********** *)

Require Import Arith Bool unfold_tactic.

(* ********** *)

(* Definerer en datatype (svarer til SML) med to constructors, Leaf og Node som hver tager hhv.
en nat og et objekt af typen binary_tree_nat som vi definerer (altså rekursiv!) *)
Inductive binary_tree_nat : Type :=
  | Leaf : nat -> binary_tree_nat
  | Node : binary_tree_nat -> binary_tree_nat -> binary_tree_nat.

Definition bt_0 :=
  Leaf 42.

Definition bt_1 :=
  Node (Leaf 10)
       (Leaf 20).

Definition bt_2 :=
  Node (Node (Leaf 10)
             (Leaf 20))
       (Leaf 30).
Print bt_2.
(*
Print bt_2.
bt_2 = Node (Node (Leaf 10) (Leaf 20)) (Leaf 30)
     : binary_tree_nat
*)

(* ********** *)

(* A unit test: *)

Notation "A =n= B" := (beq_nat A B) (at level 70, right associativity).

Definition unit_test_for_number_of_leaves (candidate : binary_tree_nat -> nat) :=
  (candidate bt_0 =n= 1)
  &&
  (candidate bt_1 =n= 2)
  &&
  (candidate bt_2 =n= 3)
  &&
  (candidate (Node bt_1 bt_2) =n= 5)
  .

Definition specification_of_number_of_leaves (number_of_leaves : binary_tree_nat -> nat) :=
  (forall n : nat,
     number_of_leaves (Leaf n) = 1)
  /\
  (forall t1 t2 : binary_tree_nat,
     number_of_leaves (Node t1 t2) = (number_of_leaves t1) + (number_of_leaves t2)).

Theorem there_is_only_one_number_of_leaves :
  forall f g : binary_tree_nat -> nat,
    specification_of_number_of_leaves f ->
    specification_of_number_of_leaves g ->
    forall t : binary_tree_nat,
      f t = g t.
Proof.
  intros f g.
  unfold specification_of_number_of_leaves.
  intros [Hf_leaf Hf_node] [Hg_leaf Hg_node].
  intro t.
  (* induktion i t. t er af en Inductive type, binary_tree_nat. Udsagnet skal bevises sand i base case, når
     t er en LEAF-konstruktion (svarer til 0 for nat). Nu kan t så antages at være en tilfældig konstruktion
     af typen binary_tree_nat. Man antager nu, at udsagnet gælder for de to tilfældige konstruktioner (IH), og skal
     nu bevise, at samles disse under en NODE-konstruktion, så gælder udsagnet stadig. *)
  (* n til venstre er hvad der sker med Leaf, højre er hvad der sker med trees? *)
  induction t as [n | t1 IHt1 t2 IHt2].

  rewrite -> Hf_leaf.
  rewrite -> Hg_leaf.
  reflexivity.

  rewrite -> Hf_node.
  rewrite -> Hg_node.
  rewrite -> IHt1.
  rewrite -> IHt2.
  reflexivity.
Qed.

(* en funktionsimplementation *)
Fixpoint number_of_leaves_ds (t : binary_tree_nat) : nat :=
  match t with
    | Leaf n =>
      1
    | Node t1 t2 =>
      (number_of_leaves_ds t1) + (number_of_leaves_ds t2)
  end.

(* unfold lemmas til den rekursive funktionsstruktur ovenfor *)
Lemma unfold_number_of_leaves_ds_leaf :
  forall n : nat,
    number_of_leaves_ds (Leaf n) = 1.
Proof.
  unfold_tactic number_of_leaves_ds.
Qed.

Lemma unfold_number_of_leaves_ds_node :
  forall t1 t2 : binary_tree_nat,
    number_of_leaves_ds (Node t1 t2) =
    (number_of_leaves_ds t1) + (number_of_leaves_ds t2).
Proof.
  unfold_tactic number_of_leaves_ds.
Qed.

(* "navngivning, implementation" af funktionen *)
Definition number_of_leaves_v0 (t : binary_tree_nat) : nat :=
  number_of_leaves_ds t.

Compute unit_test_for_number_of_leaves number_of_leaves_v0.
(*
     = true
     : bool
*)

(* Homework:
   write a version number_of_leaves_v1
   that uses an accumulator.
*)
Fixpoint number_of_leaves_acc (t : binary_tree_nat) (a : nat) : nat :=
  match t with
      | Leaf n =>
        (a + 1)
      | Node t1 t2 =>
        number_of_leaves_acc t2 (number_of_leaves_acc t1 a)
  end.

Lemma unfold_number_of_leaves_acc_leaf :
  forall n a : nat,
    number_of_leaves_acc (Leaf n) a = a + 1.
Proof.
  unfold_tactic number_of_leaves_acc.
Qed.

Lemma unfold_number_of_leaves_acc_node :
  forall t1 t2 : binary_tree_nat,
    forall a : nat,
      number_of_leaves_acc (Node t1 t2) a = number_of_leaves_acc t2 (number_of_leaves_acc t1 a).
Proof.  
  unfold_tactic number_of_leaves_acc.
Qed.


Definition number_of_leaves_v1 (a : nat) (t : binary_tree_nat) : nat :=
  number_of_leaves_acc t a.

Compute unit_test_for_number_of_leaves (number_of_leaves_v1 0).

(* ********** *)

(* Exercise:
   do the same as above for computing the number of nodes
   of a binary tree.
*)

Definition unit_test_for_number_of_nodes (candidate : binary_tree_nat -> nat) :=
  (candidate bt_0 =n= 0)
    &&
    (candidate bt_1 =n= 1)
    &&
    (candidate bt_2 =n= 2).



Definition specification_of_number_of_nodes (number_of_nodes : binary_tree_nat -> nat) :=
  (forall n : nat,
     number_of_nodes (Leaf n) = 0)
  /\
  (forall t1 t2 : binary_tree_nat,
     number_of_nodes (Node t1 t2) = number_of_nodes t1 + number_of_nodes t2 + 1).

Theorem there_is_only_one_number_of_nodes :
  forall f g : binary_tree_nat -> nat,
    specification_of_number_of_nodes f ->
    specification_of_number_of_nodes g ->
    forall t : binary_tree_nat,
      f t = g t.
Proof.
  intros f g.
  unfold specification_of_number_of_nodes.
  intros [S_f_leaf S_f_node] [S_g_leaf S_g_node].
  intro t.
  induction t as [n | t1 IHt1 t2 IHt2].

    rewrite S_g_leaf.
    exact (S_f_leaf n).

  rewrite S_f_node.
  rewrite S_g_node.
  rewrite IHt1.
  rewrite IHt2.
  reflexivity.
Qed.

Fixpoint number_of_nodes_ds (t : binary_tree_nat) : nat :=
  match t with
      | Leaf n =>
        0
      | Node t1 t2 =>
        number_of_nodes_ds t1 + number_of_nodes_ds t2 + 1
  end.

Lemma unfold_number_of_nodes_ds_leaf :
  forall n : nat,
    number_of_nodes_ds (Leaf n) = 0.
Proof.
  unfold_tactic number_of_nodes_ds.
Qed.

Lemma unfold_number_of_nodes_ds_node :
  forall t1 t2 : binary_tree_nat,
    number_of_nodes_ds (Node t1 t2) = number_of_nodes_ds t1 + number_of_nodes_ds t2 + 1.
Proof.
  unfold_tactic number_of_nodes_ds.
Qed.

Definition number_of_nodes_v0 (t : binary_tree_nat) : nat :=
  number_of_nodes_ds t.

Compute unit_test_for_number_of_nodes number_of_nodes_v0.

(* MANGLER number_of_nodes_v0_fits_the_specification_of_number_of_nodes *)

Fixpoint number_of_nodes_acc (t : binary_tree_nat) (a : nat) : nat :=
  match t with
      | Leaf n =>
        a
      | Node t1 t2 => number_of_nodes_acc t2 ( S (number_of_nodes_acc t1 a))
  end.

Lemma unfold_number_of_nodes_acc_leaf :
  forall n a : nat,
    number_of_nodes_acc (Leaf n) a = a.
Proof.
  unfold_tactic number_of_nodes_acc.
Qed.

Lemma unfold_number_of_nodes_acc_node :
  forall t1 t2 : binary_tree_nat,
    forall a : nat,
      number_of_nodes_acc (Node t1 t2) a = number_of_nodes_acc t2 ( S (number_of_nodes_acc t1 a)).
Proof.
  unfold_tactic number_of_nodes_acc.
Qed.

Definition number_of_nodes_v1 (a : nat) (t : binary_tree_nat) : nat :=
  number_of_nodes_acc t a.

Compute unit_test_for_number_of_nodes (number_of_nodes_v1 0).

(* ********** *)

(* end of week_39a_binary_trees.v *)