Require Import Arith Bool unfold_tactic.

Lemma plus_1_l :
  forall n : nat,
    1 + n = S n.
Proof.
  intro n.
  rewrite -> plus_Sn_m.
  rewrite -> plus_0_l.
  reflexivity.
Qed.

Notation "A =n= B" := (beq_nat A B) (at level 70, right associativity).

(* ********** *)

(* Data type of binary trees of natural numbers: *)

Inductive binary_tree_nat : Type :=
  | Leaf : nat -> binary_tree_nat
  | Node : binary_tree_nat -> binary_tree_nat -> binary_tree_nat.

(* There is one base case: leaves.
   There is one induction case, with two subtrees.
*)

(* ********** *)

(* Sample of binary trees of natural numbers: *)

Definition bt_0 :=
  Leaf 42.

Definition bt_1 :=
  Node (Leaf 1)
       (Leaf 2).

Definition bt_2 :=
  Node (Node (Leaf 1)
             (Leaf 2))
       (Leaf 3).

(*
Print bt_2.
bt_2 = Node (Node (Leaf 10) (Leaf 20)) (Leaf 30)
     : binary_tree_nat
*)

(* ********** *)

(* How many leaves are there in a given binary tree? *)

(* A unit test: *)

Definition unit_test_for_number_of_leaves (candidate : binary_tree_nat -> nat) :=
  (candidate bt_0 =n= 1)
  &&
  (candidate bt_1 =n= 2)
  &&
  (candidate bt_2 =n= 3)
  &&
  (candidate (Node bt_1 bt_2) =n= 5)
  .

(* ***** *)

(* A specification: *)

Definition specification_of_number_of_leaves (number_of_leaves : binary_tree_nat -> nat) :=
  (forall n : nat,
     number_of_leaves (Leaf n) = 1)
  /\
  (forall t1 t2 : binary_tree_nat,
     number_of_leaves (Node t1 t2) = number_of_leaves t1 + number_of_leaves t2).

(* ***** *)

(* Uniqueness of the specification: *)

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

(* alternatve implementation 1 *)

Fixpoint number_of_leaves_acc' (t : binary_tree_nat) (a : nat) : nat :=
      match t with
        | Leaf n =>
          1 + a
        | Node t1 t2 =>
          (number_of_leaves_acc' t2 (number_of_leaves_acc' t1 a))
      end.
    
Definition number_of_leaves_v1' (t : binary_tree_nat) : nat :=
  number_of_leaves_acc' t 0.

Lemma unfold_number_of_leaves_acc'_Leaf :
  forall n a : nat,
    number_of_leaves_acc' (Leaf n) a = 1 + a.
Proof.
  unfold_tactic number_of_leaves_acc'.
Qed.

Lemma unfold_number_of_leaves_acc'_Node :
  forall (t1 t2 : binary_tree_nat) (a : nat),
    number_of_leaves_acc' (Node t1 t2) a =
    (number_of_leaves_acc' t2 (number_of_leaves_acc' t1 a)).
Proof.
  unfold_tactic number_of_leaves_acc'.
Qed.

Compute unit_test_for_number_of_leaves number_of_leaves_v1'.
(*
     = true
     : bool
*)

Lemma about_number_of_leaves_acc' :
  forall (t : binary_tree_nat)
         (a : nat),
    number_of_leaves_acc' t a = (number_of_leaves_acc' t 0) + a.
Proof.
  intro t.
  induction t as [n | t1 IHt1 t2 IHt2].

  (* Base case: *)
  intro a.
  (* left-hand side: *)
  rewrite -> unfold_number_of_leaves_acc'_Leaf.
  (* right-hand side: *)
  rewrite -> unfold_number_of_leaves_acc'_Leaf.
  rewrite -> plus_0_r.
  reflexivity.

  (* Induction case: *)
  intro a.
  (* left-hand side: *)
  rewrite -> unfold_number_of_leaves_acc'_Node.
  rewrite -> IHt1.
  rewrite -> IHt2.
  (* right-hand side: *)
  rewrite -> unfold_number_of_leaves_acc'_Node.
  rewrite -> (IHt2 (number_of_leaves_acc' t1 0)).
  (* postlude: *)
  apply plus_assoc.
Qed.

Theorem number_of_leaves_v1'_satisfies_the_specification_of_number_of_leaves :
  specification_of_number_of_leaves number_of_leaves_v1'.
Proof.
  unfold specification_of_number_of_leaves.
  unfold number_of_leaves_v1'.
  split.
    intro n.
    rewrite -> unfold_number_of_leaves_acc'_Leaf.
    apply plus_1_l.

  intros t1 t2.
  rewrite -> unfold_number_of_leaves_acc'_Node.
  rewrite -> about_number_of_leaves_acc'.
  apply plus_comm.
Qed.


(* Second alternative implementation *)

Fixpoint number_of_leaves_cps' (ans : Type) (t : binary_tree_nat) (k : nat -> ans) : ans :=
      match t with
        | Leaf n =>
          k 1
        | Node t1 t2 =>
          number_of_leaves_cps'
            ans
            t2
            (fun n2 => number_of_leaves_cps'
                         ans
                         t1
                         (fun n1 => k (n1 + n2)))
      end.
    
Definition number_of_leaves_v3' (t : binary_tree_nat) : nat :=
  number_of_leaves_cps' nat t (fun n => n).

Lemma unfold_number_of_leaves_cps'_Leaf :
  forall (ans : Type)
         (n : nat)
         (k : nat -> ans),
    number_of_leaves_cps' ans (Leaf n) k = k 1.
Proof.
  unfold_tactic number_of_leaves_cps'.
Qed.

Lemma unfold_number_of_leaves_cps'_Node :
  forall (ans : Type)
         (t1 t2 : binary_tree_nat)
         (k : nat -> ans),
           number_of_leaves_cps' ans (Node t1 t2) k =
           number_of_leaves_cps'
             ans
             t2
             (fun n2 => number_of_leaves_cps'
                         ans
                         t1
                         (fun n1 => k (n1 + n2))).
Proof.
  unfold_tactic number_of_leaves_cps'.
Qed.

Compute unit_test_for_number_of_leaves number_of_leaves_v3'.

Lemma about_number_of_leaves_cps' :
  forall (ans : Type)
         (t : binary_tree_nat)
         (k : nat -> ans),
    number_of_leaves_cps' ans t k =
    k (number_of_leaves_cps' nat t (fun n => n)).
Proof.
  intros ans t.
  revert ans.
  induction t as [n | t1 IHt1 t2 IHt2].
    intros ans k.
    rewrite -> unfold_number_of_leaves_cps'_Leaf.
    rewrite -> unfold_number_of_leaves_cps'_Leaf.
    reflexivity.

  intros ans k.
  rewrite -> unfold_number_of_leaves_cps'_Node.
  rewrite -> IHt2.
  rewrite -> IHt1.
  symmetry.
  rewrite -> unfold_number_of_leaves_cps'_Node.
  rewrite -> IHt2.
  rewrite -> IHt1.
  reflexivity.
Qed.


Theorem number_of_leaves_v3'_satisfies_the_specification_of_number_of_leaves_first_attempt :
  specification_of_number_of_leaves number_of_leaves_v3'.
Proof.
  unfold specification_of_number_of_leaves.
  unfold number_of_leaves_v3'.
  split.
    intro n.
    rewrite -> unfold_number_of_leaves_cps'_Leaf.
    reflexivity.

  intros t1 t2.
  rewrite -> unfold_number_of_leaves_cps'_Node.
  rewrite -> about_number_of_leaves_cps'.
  rewrite -> about_number_of_leaves_cps'.
  reflexivity.
Qed.


(* compute the product *)

Definition unit_test_for_product_of_leaves (candidate : binary_tree_nat -> nat) :=
  (candidate bt_0 =n= 42)
  &&
  (candidate bt_1 =n= 2)
  &&
  (candidate bt_2 =n= 6)
  &&
  (candidate (Node bt_1 bt_2) =n= 12)
  &&
  (candidate (Node (Node bt_1 bt_2) (Leaf 0)) =n= 0)
  .

Definition specification_of_product_of_leaves (product_of_leaves : binary_tree_nat -> nat) :=
  (forall n : nat,
     product_of_leaves (Leaf n) = n)
  /\
  (forall t1 t2 : binary_tree_nat,
     product_of_leaves (Node t1 t2) = product_of_leaves t1 * product_of_leaves t2).

Theorem there_is_only_one_product_of_leaves :
  forall f g : binary_tree_nat -> nat,
    specification_of_product_of_leaves f ->
    specification_of_product_of_leaves g ->
    forall t : binary_tree_nat,
      f t = g t.
Proof.
  intros f g.
  unfold specification_of_product_of_leaves.
  intros [Hf_leaf Hf_node] [Hg_leaf Hg_node].
  intro t.
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

(* naively *)

Fixpoint product_of_leaves_ds (t : binary_tree_nat) : nat :=
  match t with
    | Leaf n =>
      n
    | Node t1 t2 =>
      (product_of_leaves_ds t1) * (product_of_leaves_ds t2)
  end.

Lemma unfold_product_of_leaves_ds_Leaf :
  forall n : nat,
    product_of_leaves_ds (Leaf n) = n.
Proof.
  unfold_tactic product_of_leaves_ds.
Qed.

Lemma unfold_product_of_leaves_ds_Node :
  forall t1 t2 : binary_tree_nat,
    product_of_leaves_ds (Node t1 t2) =
    (product_of_leaves_ds t1) * (product_of_leaves_ds t2).
Proof.
  unfold_tactic product_of_leaves_ds.
Qed.

Definition product_of_leaves_v0 (t : binary_tree_nat) : nat :=
  product_of_leaves_ds t.

Compute unit_test_for_product_of_leaves product_of_leaves_v0.

Theorem product_of_leaves_v0_satisfies_the_specification_of_product_of_leaves :
  specification_of_product_of_leaves product_of_leaves_v0.
Proof.
  unfold specification_of_product_of_leaves.
  unfold product_of_leaves_v0.
  split.
    exact unfold_product_of_leaves_ds_Leaf.

  exact unfold_product_of_leaves_ds_Node.
Qed.

(* 0 is absorbant *)

Fixpoint product_of_leaves'_ds (t : binary_tree_nat) : nat :=
  match t with
    | Leaf n =>
      n
    | Node t1 t2 => match t1, t2 with
                      | (Leaf 0), _ => 0
                      | _, (Leaf 0) => 0
                      | _, _ => (product_of_leaves'_ds t1) * (product_of_leaves'_ds t2)
                    end
  end.

Lemma unfold_product_of_leaves'_ds_Leaf :
  forall n : nat,
    product_of_leaves'_ds (Leaf n) = n.
Proof.
  unfold_tactic product_of_leaves'_ds.
Qed.

Lemma unfold_product_of_leaves'_ds_Node :
  forall t1 t2 : binary_tree_nat,
    product_of_leaves'_ds (Node t1 t2) =
    match t1, t2 with
                      | (Leaf 0), _ => 0
                      | _, (Leaf 0) => 0
                      | _, _ => (product_of_leaves'_ds t1) * (product_of_leaves'_ds t2)
                    end.
Proof.
  unfold_tactic product_of_leaves'_ds.
Qed.

Definition product_of_leaves_v1 (t : binary_tree_nat) : nat :=
  product_of_leaves'_ds t.

Compute unit_test_for_product_of_leaves product_of_leaves_v1.

Theorem product_of_leaves_v1_satisfies_the_specification_of_product_of_leaves :
  specification_of_product_of_leaves product_of_leaves_v1.
Proof.
  unfold specification_of_product_of_leaves.
  unfold product_of_leaves_v1.
  split.
    exact unfold_product_of_leaves'_ds_Leaf.

  intro t1.
  induction t1 as [ n | t1 IHt1 t2 IHt2 ].
    intro t2.
    rewrite unfold_product_of_leaves'_ds_Node.
    induction n as [ | n IHn].
      rewrite unfold_product_of_leaves'_ds_Leaf.
      rewrite mult_0_l.
      reflexivity.
    induction t2 as [ n' | t1' IHt1' t2' IHt2' ].
      induction n' as [ | n' IHn' ].
        rewrite ->2 unfold_product_of_leaves'_ds_Leaf.
        rewrite mult_0_r.
        reflexivity.
      reflexivity.
    reflexivity.
  intro t0.
  rewrite unfold_product_of_leaves'_ds_Node.
  case t0 as [ | n'] eqn:Ht0.
  induction n as [ | n IHn].
   rewrite unfold_product_of_leaves'_ds_Leaf.
   rewrite mult_0_r.
   reflexivity.
 reflexivity.
 reflexivity.
Qed.


Proposition product_of_leaves_v0_equals_product_of_leaves_v1 :
  forall t : binary_tree_nat,
    product_of_leaves_v0 t = product_of_leaves_v1 t.
Proof.
  exact (there_is_only_one_product_of_leaves product_of_leaves_v0
                                             product_of_leaves_v1
                                             product_of_leaves_v0_satisfies_the_specification_of_product_of_leaves
                                             product_of_leaves_v1_satisfies_the_specification_of_product_of_leaves
        ).
Qed.


(* from week_39_binary_trees.v *)
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
     number_of_nodes (Node t1 t2) = S (number_of_nodes t1 + number_of_nodes t2)).

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
        S (number_of_nodes_ds t1 + number_of_nodes_ds t2)
  end.

Lemma unfold_number_of_nodes_ds_leaf :
  forall n : nat,
    number_of_nodes_ds (Leaf n) = 0.
Proof.
  unfold_tactic number_of_nodes_ds.
Qed.

Lemma unfold_number_of_nodes_ds_node :
  forall t1 t2 : binary_tree_nat,
    number_of_nodes_ds (Node t1 t2) = S (number_of_nodes_ds t1 + number_of_nodes_ds t2).
Proof.
  unfold_tactic number_of_nodes_ds.
Qed.

Definition number_of_nodes_v0 (t : binary_tree_nat) : nat :=
  number_of_nodes_ds t.

Compute unit_test_for_number_of_nodes number_of_nodes_v0.

Proposition number_of_nodes_v0_satisfies_the_specification_of_number_of_nodes :
  specification_of_number_of_nodes number_of_nodes_v0.
Proof.
  unfold specification_of_number_of_nodes.
  split.
    unfold number_of_nodes_v0.
    exact unfold_number_of_nodes_ds_leaf.
  unfold number_of_nodes_v0.
  exact unfold_number_of_nodes_ds_node.
Qed.

(* ******** *)

Definition specification_of_mystery_function (f : nat -> nat) :=
  forall t : binary_tree_nat,
    f (number_of_nodes_v0 t) = number_of_leaves_v1' t.


Notation "A === B" := (beq_nat A B) (at level 70, right associativity).

Definition unit_tests_for_mystery_function (f : nat -> nat) :=
  (f (number_of_nodes_v0 bt_0) === (number_of_leaves_v1' bt_0))
  &&
  (f (number_of_nodes_v0 bt_1) === (number_of_leaves_v1' bt_1))
  &&
  (f (number_of_nodes_v0 bt_2) === (number_of_leaves_v1' bt_2))
  &&
  (f (number_of_nodes_v0 (Node bt_1 bt_2)) === (number_of_leaves_v1' (Node bt_1 bt_2))).

Definition mystery_function : nat -> nat :=
  S.

Compute unit_tests_for_mystery_function mystery_function.


Proposition mystery_function_satisfies_specification_of_mystery_function :
  specification_of_mystery_function mystery_function.
Proof.
  unfold specification_of_mystery_function.
  intro t.
  unfold mystery_function.
  unfold number_of_nodes_v0.
  unfold number_of_leaves_v1'.
  induction t as [ n | t1 IHt1 t2 IHt2 ].
    rewrite unfold_number_of_nodes_ds_leaf.
    rewrite unfold_number_of_leaves_acc'_Leaf.
    ring.
  rewrite unfold_number_of_nodes_ds_node.
  rewrite (plus_n_Sm (number_of_nodes_ds t1) (number_of_nodes_ds t2)).
  rewrite <- plus_1_l.
  rewrite unfold_number_of_leaves_acc'_Node.
  rewrite (about_number_of_leaves_acc' t2 (number_of_leaves_acc' t1 0)).
  rewrite <- IHt1.
  rewrite <- IHt2.
  ring.
Qed.



Theorem there_is_only_one_specification_of_mystery_function :
  forall f g : nat -> nat,
    specification_of_mystery_function f ->
    specification_of_mystery_function g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_mystery_function.
  unfold number_of_nodes_v0.
  
  intro S_g.
  intro n.
  induction n as [ | n IHn ].
Abort.