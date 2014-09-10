(* Group:
Marc Skodborg,          201206073
Stefan Niemann Madsen,  201206043
Michael Simonsen,       201206100
*)

(* week_36c_mul.v *)
(* dIFP 2014-2015, Q1, Week 36 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* ********** *)

Require Import Arith Bool.

Require Import unfold_tactic.

(* ********** *)

Notation "A === B" := (beq_nat A B) (at level 70, right associativity).

Definition unit_tests_for_multiplication (mul : nat -> nat -> nat) :=
  (mul 0 0 === 0)
  &&
  (mul 0 1 === 0)
  &&
  (mul 1 1 === 1)
  &&
  (mul 2 1 === 2)
  &&
  (mul 3 1 === 3)
  &&
  (mul 5 4 === 20).

(* Exercise 0: flesh out the unit tests above with more tests. *)

(* mult is the built-in multiplication in Coq (infix notation: * ): *)
Compute (unit_tests_for_multiplication mult).
(*
     = true
     : bool
*)

(* Exercise 1: why is there a space in the comment just above
   on the right of the infix notation for multiplication?
*)

(* So as to not end the comment *)

(* ********** *)


Require Import "unfold_tactic".
(* The two mandatory unfold lemmas: *)
Lemma unfold_plus_bc :
  forall j : nat,
    0 + j = j.
Proof.
  unfold_tactic plus.
Qed.
Lemma unfold_plus_ic :
  forall i' j : nat,
    (S i') + j = S (i' + j).
Proof.
  unfold_tactic plus.
Qed.


Definition specification_of_multiplication (mul : nat -> nat -> nat) :=
  (forall j : nat,
    mul O j = 0)
  /\
  (forall i' j : nat,
    mul (S i') j = j + (mul i' j)).

(* ********** *)

(* For the following exercise,
   the following lemmas from the Arith library might come handy:
   plus_0_l, plus_0_r, plus_comm, and plus_assoc.
*)

Proposition multiplication_bc_left :
  forall (mul : nat -> nat -> nat),
    specification_of_multiplication mul ->
    forall j : nat,
      mul 0 j = 0.
Proof.
  intros mul S_mul j.
  unfold specification_of_multiplication in S_mul.
  destruct S_mul as [H_mul_bc _].
  apply H_mul_bc.
Qed.

Proposition multiplication_ic_left :
  forall (mul : nat -> nat -> nat),
    specification_of_multiplication mul ->
    forall i' j : nat,
      mul (S i') j = j + (mul i' j).
Proof.
  intros mul S_mul i' j.
  unfold specification_of_multiplication in S_mul.
  destruct S_mul as [_ H_mul_ic].
  apply (H_mul_ic i' j).
Qed.

Proposition multiplication_bc_right :
  forall (mul : nat -> nat -> nat),
    specification_of_multiplication mul ->
    forall i : nat,
      mul i 0 = 0.
Proof.
  intros mul S_mul.
  unfold specification_of_multiplication in S_mul.
  destruct S_mul as [H_mul_bc H_mul_ic].
  intro i.
  induction i as [ | n' IHn'].
    apply H_mul_bc.

  rewrite -> (H_mul_ic n' 0).
  rewrite -> plus_0_l.
  apply IHn'.
Qed.

Proposition multiplication_ic_right :
  forall (mul : nat -> nat -> nat),
    specification_of_multiplication mul ->
    forall i j' : nat,
      mul i (S j') = i + (mul i j').
Proof.
  intros mul S_mul i j'.
  induction i as [ | n' IHn'].
    
    (* Base case *)
    rewrite -> (multiplication_bc_left mul S_mul).
    rewrite -> (multiplication_bc_left mul S_mul).
    apply plus_0_l.

  (* Induction case *)
  
  unfold specification_of_multiplication in S_mul.
  destruct S_mul as [H_mul_bc H_mul_ic].
  rewrite -> (H_mul_ic  n' (S j')).
  rewrite -> IHn'.
  rewrite -> plus_assoc.
  rewrite -> (plus_Snm_nSm j' n').
  rewrite -> (plus_comm j' (S n')).
  rewrite -> H_mul_ic.
  Check plus_assoc.
  rewrite -> (plus_assoc (S n') j' (mul n' j')).
  reflexivity.
Qed. 


Check plus_0_l.

(* Exercise:

   * show that 0 is left-absorbant for multiplication
     (aka mult_0_l in Arith)

   * show that 0 is right-absorbant for multiplication
     (aka mult_0_r in Arith)

   * show that 1 is left-neutral for multiplication
     (aka mult_1_l in Arith)

   * show that 1 is right-neutral for multiplication
     (aka mult_1_r in Arith)

   * show that multiplication is commutative
     (aka mult_comm in Arith)

   * show that the specification of multiplication is unique

   * implement multiplication,
     verify that your implementation passes the unit tests, and
     prove that your implementation satisfies the specification
*)

Check mult_0_l.

Proposition zero_is_left_absorbant_for_multiplication :
  forall (mul : nat -> nat -> nat),
    specification_of_multiplication mul ->
    forall j : nat,
      mul 0 j = 0.
Proof.
  apply multiplication_bc_left. 
Qed.

Check mult_0_r.

Proposition zero_is_right_absorbant_for_multiplication :
  forall (mul : nat -> nat -> nat),
    specification_of_multiplication mul ->
    forall i : nat,
      mul i 0 = 0.

Proof.
  apply multiplication_bc_right.
Qed.

Theorem one_is_left_neutral_for_multiplication :
  forall (mul : nat -> nat -> nat),
    specification_of_multiplication mul ->
    forall n : nat,
      mul 1 n = n.
Proof.
  intros mul S_mul n.
  rewrite -> (multiplication_ic_left mul S_mul 0 n).
  rewrite -> (multiplication_bc_left mul S_mul n).
  rewrite -> (plus_0_r n).
  reflexivity.
Qed.

Theorem one_is_right_neutral_for_multiplication :
  forall (mul : nat -> nat -> nat),
    specification_of_multiplication mul ->
    forall i : nat,
      mul i 1 = i.
Proof.
  intros mul S_mul i.
  induction i as [ | n' IHn'].
    rewrite -> (zero_is_left_absorbant_for_multiplication mul S_mul).
    reflexivity.
  unfold specification_of_multiplication in S_mul.
  destruct S_mul as [H_mul_bc H_mul_ic].
  rewrite -> (H_mul_ic n' 1).
  rewrite -> IHn'.
  rewrite -> (unfold_plus_ic 0 n').
  apply unfold_plus_bc.
Qed.

Theorem multiplication_is_commutative :
  forall (mul : nat -> nat -> nat),
    specification_of_multiplication mul ->
    forall i j : nat,
      mul i j =  mul j i.
Proof.
  intros mul S_mul i j.
  induction i as [ | i' IHi'].
    rewrite -> (multiplication_bc_left mul S_mul j).
    rewrite -> (multiplication_bc_right mul S_mul j).
    reflexivity.

  rewrite -> (multiplication_ic_left mul S_mul i' j).
  rewrite -> (multiplication_ic_right mul S_mul j i').
  rewrite -> IHi'.
  reflexivity.
Qed.


(* show that the specification of multiplication is unique *)

Proposition there_is_only_one_multiplication :
  forall mul1 mul2 : nat -> nat -> nat,
    specification_of_multiplication mul1 ->
    specification_of_multiplication mul2 ->
    forall i j : nat,
      mul1 i j =  mul2 i j.

Proof.
  intros mul1 mul2 S_mul1 S_mul2 i j.
  induction i.

    rewrite -> (multiplication_bc_left mul1 S_mul1 j).
    rewrite -> (multiplication_bc_left mul2 S_mul2 j).
    reflexivity.

  rewrite -> (multiplication_ic_left mul1 S_mul1 i j).
  rewrite -> (multiplication_ic_left mul2 S_mul2 i j).
  rewrite -> IHi.
  reflexivity.
Qed.


(* implement multiplication, verify that your implementation 
   passes the unit tests, and prove that your implementation
   satisfies the specification *)

Fixpoint mul_v1 (i j : nat) : nat :=
  match i with
    |0 => 0
    |S i' => j + (mul_v1 i' j)
  end.

Compute (unit_tests_for_multiplication mul_v1).

Lemma unfold_mul_v1_bc :
  forall j : nat,
    mul_v1 0 j = 0.
Proof.
  unfold_tactic mul_v1.
Qed.

Lemma unfold_mul_v1_ic :
  forall i' j : nat,
    mul_v1 (S i') j = j + (mul_v1 i' j).
Proof.
  unfold_tactic mul_v1.
Qed.


Theorem mult_v1_satisfies_the_specification_of_multiplication :
  specification_of_multiplication mul_v1.
Proof.
  unfold specification_of_multiplication.
  split.

  apply unfold_mul_v1_bc.

  apply unfold_mul_v1_ic.
Qed.

(* ********** *)

(* Exercise for the over-achievers:

   In no particular order,

   * show that multiplication is associative
     (aka mult_assoc in Arith),

   * show that multiplication distributes over addition on the left
     (aka mult_plus_distr_l in Arith), and

   * show that multiplication distributes over addition on the right
     (aka mult_plus_distr_r in Arith).
*)

(* ********** *)

(* Exercise for the over-achievers with time on their hands:
   repeat the exercises above with our own implementation
   of the addition function.
   (You will first need to compile week_36b_add.v with coqc.) 
*)

(*
Require Import week_36b_add.

Definition specification_of_multiplication' (mul : nat -> nat -> nat) :=
  (forall j : nat,
    mul O j = 0)
  /\
  (forall add : nat -> nat -> nat,
     specification_of_addition add ->
     forall i' j : nat,
       mul (S i') j = add j (mul i' j)).
*)

(* ********** *)

(* end of week_36c_mul.v *)
