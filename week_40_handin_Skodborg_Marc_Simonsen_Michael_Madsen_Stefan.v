Require Import Arith Bool unfold_tactic List.

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

Lemma function_pluss_equals_function_plus_function :
  forall f : nat -> nat,
  forall a b : nat,
    f(a+b) = f(a) + f(b).
Proof.
Admitted.

Theorem there_is_only_one_mystery_function :
  forall f g :  nat -> nat,
    specification_of_mystery_function f ->
    specification_of_mystery_function g ->
    forall t : binary_tree_nat,
      f (number_of_nodes_v0 t) = g (number_of_nodes_v0 t) .
Proof.
  intros f g .
  unfold specification_of_mystery_function.
  unfold number_of_nodes_v0.
  unfold number_of_leaves_v1'.
  induction t as [ n | ].
    rewrite H.
    rewrite H0.
    rewrite unfold_number_of_leaves_acc'_Leaf.
    ring.

    rewrite unfold_number_of_nodes_ds_node.
    
    
    

(* Flatten  *)

(* Sample of binary trees of natural numbers: *)

Fixpoint equal_list_nat (xs ys : list nat) :=
  match xs with
    | nil =>
      match ys with
        | nil => true
        | y :: ys' => false
      end
    | x :: xs' =>
      match ys with
        | nil => false
        | y :: ys' => (beq_nat x y) && (equal_list_nat xs' ys')
      end
  end.

Definition unit_test_for_flatten (candidate : binary_tree_nat -> list nat) :=
  (equal_list_nat (candidate bt_0) (42 :: nil))
  &&
  (equal_list_nat (candidate bt_1) (1 :: 2 :: nil))
  &&
  (equal_list_nat (candidate bt_2) (1 :: 2 :: 3 :: nil))
  &&
  (equal_list_nat (candidate (Node bt_1 bt_2)) (1 :: 2 :: 1 :: 2 :: 3 :: nil)).

(* ********** *)

Definition specification_of_flatten (flatten : binary_tree_nat -> list nat) :=
  (forall n : nat,
     flatten (Leaf n) = n :: nil)
  /\
  (forall t1 t2 : binary_tree_nat,
     flatten (Node t1 t2) = (flatten t1) ++ (flatten t2)).

Theorem there_is_only_one_flatten :
  forall flatten1 flatten2 : binary_tree_nat -> list nat,
    specification_of_flatten flatten1 ->
    specification_of_flatten flatten2 ->
    forall t : binary_tree_nat,
      flatten1 t = flatten2 t.
Proof.
  intros flatten1 flatten2.
  unfold specification_of_flatten.
  intros [H1_leaf H1_node] [H2_leaf H2_node].
  intro t.
  induction t as [n | t1 IHt1 t2 IHt2].

  rewrite -> H2_leaf.
  apply H1_leaf.

  rewrite -> H1_node.
  rewrite -> H2_node.
  rewrite -> IHt1.
  rewrite -> IHt2.
  reflexivity.
Qed.

(* ********** *)

(* Version with append: *)

Fixpoint flatten_ds (t : binary_tree_nat) : list nat :=
  match t with
    | Leaf n => n :: nil
    | Node t1 t2 => (flatten_ds t1) ++ (flatten_ds t2)
  end.

(* recursive definition, therefore: unfold lemmas! *)
Lemma unfold_flatten_leaf :
  forall n : nat,
    flatten_ds (Leaf n) = n :: nil.
Proof.  
  unfold_tactic flatten_ds.
Qed.

Lemma unfold_flatten_node :
  forall t1 t2 : binary_tree_nat,
    flatten_ds (Node t1 t2) = (flatten_ds t1) ++ (flatten_ds t2).
Proof.  
  unfold_tactic flatten_ds.
Qed.


Definition flatten_v0 (t : binary_tree_nat) : list nat :=
  flatten_ds t.

Compute unit_test_for_flatten flatten_v0.
(*
= true
: bool
*)

Proposition flatten_v0_satisfies_specification_of_flatten :
  specification_of_flatten flatten_v0.
Proof.
  unfold specification_of_flatten.
  split.
    exact unfold_flatten_leaf.
  exact unfold_flatten_node.
Qed.

(* swap *)

Definition specification_of_swap (swap : binary_tree_nat -> binary_tree_nat) :=
  (forall n : nat,
     swap (Leaf n) = Leaf n)
  /\
  (forall t1 t2 : binary_tree_nat,
     swap (Node t1 t2) = Node (swap t2) (swap t1)).

Theorem there_is_only_one_swap :
  forall swap1 swap2 : binary_tree_nat -> binary_tree_nat,
    specification_of_swap swap1 ->
    specification_of_swap swap2 ->
    forall t : binary_tree_nat,
      swap1 t = swap2 t.
Proof.
  intros swap1 swap2.
  intros [S_swap1_leaf S_swap1_node] [S_swap2_leaf S_swap2_node].
  intro t.
  induction t as [ n | t1 IHt1 t2 IHt2].
    rewrite S_swap2_leaf.
    exact (S_swap1_leaf n).
  rewrite S_swap2_node.
  rewrite <- IHt1.
  rewrite <- IHt2.
  exact (S_swap1_node t1 t2).
Qed.


Fixpoint swap_ds (t : binary_tree_nat) : binary_tree_nat :=
  match t with
    | Leaf n => Leaf n
    | Node t1 t2 => Node (swap_ds t2) (swap_ds t1)
  end.

Lemma unfold_swap_leaf :
  forall n : nat,
    swap_ds (Leaf n) = (Leaf n).
Proof.
  unfold_tactic swap_ds.
Qed.

Lemma unfold_swap_node :
  forall t1 t2 : binary_tree_nat,
    swap_ds (Node t1 t2) = Node (swap_ds t2) (swap_ds t1).
Proof.
  unfold_tactic swap_ds.
Qed.


Definition swap_v0 (t : binary_tree_nat) : binary_tree_nat :=
  swap_ds t.

Proposition swap_v0_satisfies_specification_of_swap :
  specification_of_swap swap_v0.
Proof.
  unfold specification_of_swap.
  unfold swap_v0.
  split.
    exact unfold_swap_leaf.
  exact unfold_swap_node.
Qed.

(* Prove that composing swap_v0 with itself yields the identity function *)
Proposition double_swap_yields_identity_function :
  forall t : binary_tree_nat,
    swap_v0 (swap_v0 t) = t.
Proof.
  intro t.
  unfold swap_v0.
  induction t as [n | t1 IHt1 t2 IHt2].
    rewrite ->2 unfold_swap_leaf.
    reflexivity.
  rewrite ->2 unfold_swap_node.
  rewrite IHt1.
  rewrite IHt2.
  reflexivity.
Qed.

(* ********** *)

(* What is the result of applying flatten_v0
   to the result of applying swap_v0 to a tree?
*)

(* swap_v0 takes a binary_tree_nat as input, flatten_v0 outputs a binary_tree_nat *)
Definition specification_of_the_mystery_function_1 (f : binary_tree_nat -> list nat) :=
  forall t : binary_tree_nat,
    f t = flatten_v0 (swap_v0 t).

Proposition there_is_only_one_mystery_function_1 :
  forall f g : binary_tree_nat -> list nat,
    specification_of_the_mystery_function_1 f ->
    specification_of_the_mystery_function_1 g ->
    forall t : binary_tree_nat,
      f t = g t.
Proof.
  intros f g.
  unfold specification_of_the_mystery_function_1.
  intros S_f S_g.
  intro t.
  induction t as [ n | t1 IHt1 t2 IHt2].
    rewrite (S_g (Leaf n)).
    exact (S_f (Leaf n)).
  rewrite (S_g (Node t1 t2)).
  exact (S_f (Node t1 t2)).
Qed.

Definition unit_test_for_mystery_function_1 (candidate : binary_tree_nat -> list nat) :=
  (equal_list_nat (candidate bt_0) (flatten_v0 (swap_v0 bt_0)))
  &&
  (equal_list_nat (candidate bt_1) (flatten_v0 (swap_v0 bt_1)))
  &&
  (equal_list_nat (candidate bt_2) (flatten_v0 (swap_v0 bt_2)))
  &&
  (equal_list_nat (candidate (Node bt_1 bt_2)) (flatten_v0 (swap_v0 (Node bt_1 bt_2)))).


(* a guess of the mystery function, NOT RECURSIVE *)
Definition mystery_function_1 (t : binary_tree_nat) : list nat :=
  rev (flatten_v0 t).

Compute unit_test_for_mystery_function_1 mystery_function_1.
(*
= true
: bool
*)

Lemma unfold_rev_bc :
  rev nil = (nil : list nat).
Proof.
  unfold_tactic rev.
Qed.

Lemma unfold_rev_ic :
  forall (x : nat) (l : list nat),
    rev (x :: l) = rev l ++ (x :: nil).
Proof.
  unfold_tactic rev.
Qed.



Proposition reverse_v1_app_distr :
  forall xs ys : list nat,
    rev (xs ++ ys) = rev ys ++ rev xs.
Proof.
  intro xs.
  induction xs as [ | x xs IHxs].
    intro ys.
    rewrite app_nil_l.
    rewrite unfold_rev_bc.
    rewrite app_nil_r.
    reflexivity.
  intro ys.
  rewrite unfold_rev_ic.
  rewrite <- app_comm_cons.
  rewrite unfold_rev_ic.
  rewrite IHxs.
  rewrite app_assoc.
  reflexivity.
Qed.


Proposition mystery_function_1_satisfies_specification_of_the_mystery_function_1 :
  specification_of_the_mystery_function_1 mystery_function_1.
Proof.
  unfold specification_of_the_mystery_function_1.
  unfold mystery_function_1.
  unfold flatten_v0.
  unfold swap_v0.
  intro t.
  induction t as [ n | t1 IHt1 t2 IHt2].
    rewrite unfold_swap_leaf.
    rewrite unfold_flatten_leaf.
    rewrite unfold_rev_ic.
    rewrite unfold_rev_bc.
    rewrite app_nil_l.
    reflexivity.
  rewrite unfold_swap_node.
  rewrite (unfold_flatten_node (swap_ds t2) (swap_ds t1)).
  rewrite <- IHt1.
  rewrite <- IHt2.
  rewrite unfold_flatten_node.
  rewrite reverse_v1_app_distr.
  reflexivity.
Qed.


(* ********** *)
