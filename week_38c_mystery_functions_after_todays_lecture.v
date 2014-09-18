(* week_38c_mystery_functions_after_todays_lecture.v *)
(* dIFP 2014-2015, Q1, Week 38 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* Working file as edited during the lecture. *)

(* ********** *)

Require Import Arith Bool.

Notation "A =n= B" := (beq_nat A B) (at level 70, right associativity).

Notation "A =b= B" := (eqb A B) (at level 70, right associativity).

(* ********** *)

(* Are the following specifications unique?
   What are then the corresponding functions?

   Spend the rest of your dIFP weekly time
   to answer these questions
   for the specifications below.
   (At least 7 specifications would be nice.)
*)

(* ********** *)

Definition specification_of_the_mystery_function_0 (f : nat -> nat) :=
  (f 0 = 1)
  /\
  (forall i j : nat,
    f (S (i + j)) = f i + f j).

(* ***** *)

Proposition there_is_only_one_mystery_function_0 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_0 f ->
    specification_of_the_mystery_function_0 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g [Sf_bc Sf_ic] [Sg_bc Sg_ic] n.
  induction n as [ | n' IHn'].
    rewrite -> Sg_bc.
    apply Sf_bc.
    rewrite -> (plus_n_O n').
    rewrite -> Sf_ic.
    rewrite -> Sg_ic.
    rewrite -> Sf_bc.
    rewrite -> Sg_bc.
    rewrite -> IHn'.
    reflexivity.
Qed.
(* Replace "Abort." with a proof. *)

(* ***** *)

(* Flesh out the following unit test
   as you tabulate mystery_function_0:
*)
Definition unit_test_for_the_mystery_function_0 (f : nat -> nat) :=
(*
   The following equality is in the specification:
*)
  (f 0 =n= 1)
(*
   f 1
   = (* because S (i + j) = 1 if i = 0 and j = 0 *)
   f (S (0 + 0))    
   = (* by definition of mystery_function_0 *)
   f 0 + f 0
   = (* by definition of mystery_function_0 *)
   1 + 1
   =
   2
*)
  &&
  (f 1 =n= 2)
(*
   Similarly,
   f 2
   =
   f (S (0 + 1))
   =
   f 0 + f 1
   =
   1 + 2
   =
   3
*)
  &&
  (f 2 =n= 3)
(*
   We therefore conjecture that the mystery function
   is the successor function,
   i.e., the function that adds 1 to its argument.
*)
  .

Compute unit_test_for_the_mystery_function_0 S.
Check S.
(* ***** *)

Theorem and_the_mystery_function_0_is_dot_dot_dot :
  specification_of_the_mystery_function_0 S.
Proof.
  unfold specification_of_the_mystery_function_0.
  split.

  reflexivity.

  intros i j.
  ring.
Qed.  

(* ********** *)

Definition specification_of_the_mystery_function_1 (f : nat -> nat) :=
  (f 0 = 0)
  /\
  (forall i j : nat,
    f (i + S j) = f i + S (f j)).

(* ***** *)

Proposition there_is_only_one_mystery_function_1 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_1 f ->
    specification_of_the_mystery_function_1 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g [Sf_bc Sf_ic] [Sg_bc Sg_ic] n.
  induction n as [ | n' IHn'].
    rewrite -> Sg_bc.
    apply Sf_bc.
  Search (0 + _ = _).
  rewrite <- (plus_O_n (S n')).
  rewrite -> Sf_ic.
  rewrite -> Sg_ic.
  rewrite -> Sf_bc.
  rewrite -> Sg_bc.
  rewrite -> IHn'.
  reflexivity.
Qed.
(* Replace "Abort." with a proof. *)

(* ***** *)

(* Flesh out the following unit test
   as you tabulate mystery_function_1:
*)
Definition unit_test_for_the_mystery_function_1 (f : nat -> nat) :=
(*
   The following equality is in the specification:
*)
  (f 0 =n= 0)
(*
   f 1
   = ...
*)

  &&
  (f 1 =n= 1)
  &&
  (f 2 =n= 2)
  &&
  (f 3 =n= 3)
  &&
  (f 4 =n= 4).

Definition mystery_function_1 n : nat :=
  n.

Compute unit_test_for_the_mystery_function_1 (mystery_function_1 ).


(* ***** *)


Theorem and_the_mystery_function_1_is_dot_dot_dot :
  specification_of_the_mystery_function_1 mystery_function_1.
Proof.
  unfold specification_of_the_mystery_function_1.
  unfold mystery_function_1.
  split.
    reflexivity.

  reflexivity.
Qed.  


(* ********** *)

Definition specification_of_the_mystery_function_2 (f : nat -> nat) :=
  (f 0 = 0)
  /\
  (forall i j : nat,
    f (S (i + j)) = S (f i) + S (f j)).

Proposition there_is_only_one_mystery_function_2 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_2 f ->
    specification_of_the_mystery_function_2 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g [Sf_bc Sf_ic] [Sg_bc Sg_ic] n.
  induction n as [ | n' IHn'].
    rewrite -> Sg_bc.
    apply Sf_bc.

  rewrite <- (plus_O_n n').
  rewrite -> Sf_ic.
  rewrite -> Sg_ic.
  rewrite -> Sf_bc.
  rewrite -> Sg_bc.
  rewrite -> IHn'.
  reflexivity.
Qed.

Definition unit_test_for_the_mystery_function_2 (f : nat -> nat) :=
  (f 0 =n= 0)
  &&
  (f 1 =n= 2)
  &&
  (f 2 =n= 4)
  &&
  (f 3 =n= 6)
  &&
  (f 4 =n= 8).

Definition mystery_function_2 n : nat :=
  2*n.

Compute unit_test_for_the_mystery_function_2 mystery_function_2.

Theorem and_the_mystery_function_2_is_dot_dot_dot :
  specification_of_the_mystery_function_2 mystery_function_2.
Proof.
  unfold specification_of_the_mystery_function_2.
  unfold mystery_function_2.
  split.
    apply plus_0_l.

  intros i j.
  ring.
Qed.

  
(* ********** *)

Definition specification_of_the_mystery_function_3 (f : nat -> nat) :=
  (f 0 = 1)
  /\
  (forall i j : nat,
    f (S (i + j)) = S (f i) + S (f j)).


Proposition there_is_only_one_mystery_function_3 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_3 f ->
    specification_of_the_mystery_function_3 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g [Sf_bc Sf_ic] [Sg_bc Sg_ic] n.
  induction n as [ | n' IHn'].
    rewrite -> Sg_bc.
    apply Sf_bc.
    
  rewrite <- (plus_O_n n').
  rewrite -> Sf_ic.
  rewrite -> Sg_ic.
  rewrite -> Sf_bc.
  rewrite -> Sg_bc.
  rewrite -> IHn'.
  reflexivity.
Qed.

Definition unit_test_for_the_mystery_function_3 (f : nat -> nat) :=
  (f 0 =n= 1)
  &&
  (f 1 =n= 4)
  &&
  (f 2 =n= 7)
  &&
  (f 3 =n= 10)
  &&
  (f 4 =n= 13).

Definition mystery_function_3 (n : nat) : nat :=
  3*n+1.
  
Compute unit_test_for_the_mystery_function_3 mystery_function_3.

Theorem and_the_mystery_function_3_is_dot_dot_dot :
  specification_of_the_mystery_function_3 mystery_function_3.
Proof.
  unfold specification_of_the_mystery_function_3.
  unfold mystery_function_3.
  split.
    rewrite -> plus_0_l.
    reflexivity.

  intros i j.
  ring.
Qed.


(* ********** *)

Definition specification_of_the_mystery_function_4 (f : nat -> nat) :=
  (f 0 = 0)
  /\
  (forall i j : nat,
    f (i + j) = f i + f j).

Proposition there_is_only_one_mystery_function_4 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_4 f ->
    specification_of_the_mystery_function_4 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g [Sf_bc Sf_ic] [Sg_bc Sg_ic] n.
  induction n as [ | n' IHn'].
    rewrite -> Sg_bc.
    apply Sf_bc.
    
  Require Import week_37a_sum.
  rewrite <- (plus_1_l n').
  rewrite -> Sf_ic.
  rewrite -> Sg_ic.
  rewrite -> IHn'.
  
Abort.


(* ********** *)

Definition specification_of_the_mystery_function_5 (f : nat -> nat) :=
  (f 0 = 0)
  /\
  (forall i : nat,
    f (S i) = S (2 * i + f i)).


Proposition there_is_only_one_mystery_function_5 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_5 f ->
    specification_of_the_mystery_function_5 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g [Sf_bc Sf_ic] [Sg_bc Sg_ic] n.
  induction n as [ | n' IHn'].
    rewrite -> Sg_bc.
    apply Sf_bc.
    
  rewrite -> Sf_ic.
  rewrite -> Sg_ic.
  rewrite -> IHn'.
  reflexivity.
Qed.

Definition unit_test_for_the_mystery_function_5 (f : nat -> nat) :=
  (f 0 =n= 0)
  &&
  (f 1 =n= 1)
  &&
  (f 2 =n= 4)
  &&
  (f 3 =n= 9)
  &&
  (f 4 =n= 16).

Definition mystery_function_5 (n : nat) : nat :=
  n*n.
  
Compute unit_test_for_the_mystery_function_5 mystery_function_5.

Theorem and_the_mystery_function_5_is_dot_dot_dot :
  specification_of_the_mystery_function_5 mystery_function_5.
Proof.
  unfold specification_of_the_mystery_function_5.
  unfold mystery_function_5.
  split.
    reflexivity.

  intros i.
  ring.
Qed.

(* ********** *)

Definition specification_of_the_mystery_function_6 (f : nat -> nat) :=
  (forall i j : nat,
    f (i + j) = f i + 2 * i * j + f j).

Proposition there_is_only_one_mystery_function_6 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_6 f ->
    specification_of_the_mystery_function_6 g ->
    forall n : nat,
      f n = g n.
Proof.
Abort.


(* ********** *)

Definition specification_of_the_mystery_function_7 (f : nat -> nat) :=
  (f 0 = 1)
  /\
  (forall i j : nat,
    f (S (i + j)) = 2 * f i * f j).

Proposition there_is_only_one_mystery_function_7 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_7 f ->
    specification_of_the_mystery_function_7 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g [Sf_bc Sf_ic] [Sg_bc Sg_ic] n.
  induction n as [ | n' IHn'].
    rewrite -> Sg_bc.
    apply Sf_bc.
    
  rewrite <- (plus_O_n n').
  rewrite -> Sf_ic.
  rewrite -> Sg_ic.
  rewrite -> Sf_bc.
  rewrite -> Sg_bc.
  rewrite -> IHn'.
  reflexivity.
Qed.

Definition unit_test_for_the_mystery_function_7 (f : nat -> nat) :=
  (f 0 =n= 1)
  &&
  (f 1 =n= 2)
  &&
  (f 2 =n= 4)
  &&
  (f 3 =n= 8)
  &&
  (f 4 =n= 16).

Require Import week_38a_recap_after_todays_lecture.

Definition mystery_function_7 (n : nat) : nat :=
  power_ds 2 n.
  
Compute unit_test_for_the_mystery_function_7 mystery_function_7.

Theorem and_the_mystery_function_7_is_dot_dot_dot :
  specification_of_the_mystery_function_7 mystery_function_7.
Proof.
  unfold specification_of_the_mystery_function_7.
  unfold mystery_function_7.
  split.
    unfold power_ds.
    reflexivity.

  intros i j.
  rewrite -> (unfold_power_ds_ic 2 (i + j)).

  rewrite -> about_power_exponent_plus.
    ring.
    
  unfold specification_of_power.
  split.
    apply unfold_power_ds_bc.
    
  apply unfold_power_ds_ic.
Qed.

(* ********** *)

Definition specification_of_the_mystery_function_8 (f : nat -> nat) :=
  (f 0 = 2)
  /\
  (forall i j : nat,
    f (S (i + j)) = f i * f j).


Proposition there_is_only_one_mystery_function_8 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_8 f ->
    specification_of_the_mystery_function_8 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g [Sf_bc Sf_ic] [Sg_bc Sg_ic] n.
  induction n as [ | n' IHn'].
    rewrite -> Sg_bc.
    apply Sf_bc.
    
  rewrite <- (plus_O_n n').
  rewrite -> Sf_ic.
  rewrite -> Sg_ic.
  rewrite -> Sf_bc.
  rewrite -> Sg_bc.
  rewrite -> IHn'.
  reflexivity.
Qed.

Definition unit_test_for_the_mystery_function_8 (f : nat -> nat) :=
  (f 0 =n= 2)
  &&
  (f 1 =n= 4)
  &&
  (f 2 =n= 8)
  &&
  (f 3 =n= 16)
  &&
  (f 4 =n= 32).

Definition mystery_function_8 (n : nat) : nat :=
  ( (n-1))*2.
  
Compute unit_test_for_the_mystery_function_8 mystery_function_8.

Theorem and_the_mystery_function_8_is_dot_dot_dot :
  specification_of_the_mystery_function_8 mystery_function_8.
Proof.
Abort.

(* ********** *)

Definition specification_of_the_mystery_function_9 (f : nat -> nat) :=
  (f 0 = 0)
  /\
  (f 1 = 1)
  /\
  (f 2 = 1)
  /\
  (forall p q : nat,
    f (S (p + q)) = f (S p) * f (S q) + f p * f q).

Proposition there_is_only_one_mystery_function_9 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_9 f ->
    specification_of_the_mystery_function_9 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g [Sf_bc_0 [Sf_bc_1 [Sf_bc_2 Sf_ic]]] [Sg_bc_0 [Sg_bc_1 [Sg_bc_2 Sg_ic]]] n.
  induction n as [ | n' IHn'].
    rewrite -> Sg_bc_0.
    apply Sf_bc_0.
    
      rewrite <- (plus_O_n x).
      rewrite -> Sf_ic.
      rewrite -> Sg_ic.
      rewrite -> Sf_bc_0.
      rewrite -> Sg_bc_0.
      rewrite -> Sf_bc_1.
      rewrite -> Sg_bc_1.
Qed.

Definition unit_test_for_the_mystery_function_9 (f : nat -> nat) :=
  (f 0 =n= 0)
  &&
  (f 1 =n= 1)
  &&
  (f 2 =n= 1)
  &&
  (f 3 =n= 2)
  &&
  (f 4 =n= 3)
  &&
  (f 5 =n= 5).

Compute unit_test_for_the_mystery_function_9 fib_v0.

Theorem and_the_mystery_function_9_is_dot_dot_dot :
  specification_of_the_mystery_function_9 fib_v0.
Proof.
  unfold specification_of_the_mystery_function_9.
  unfold fib_v0.
  split.
    apply unfold_fib_ds_base_case_0.

  split.
    apply unfold_fib_ds_base_case_1.

  split.
    apply unfold_fib_ds_induction_case.

  intros p q.
Abort.

(* ********** *)

Definition specification_of_the_mystery_function_10 (f : nat -> bool) :=
  (f 0 = true)
  /\
  (f 1 = false)
  /\
  (forall i j : nat,
     f (i + j) = eqb (f i) (f j)).

(* ********** *)

(* end of week_38c_mystery_functions_after_todays_lecture.v *)
