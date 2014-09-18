(* week_38b_induction_after_todays_lecture.v *)
(* dIFP 2014-2015, Q1, Week 38 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* Working file as edited during the lecture. *)

(* ********** *)

Require Import Arith.

(* ********** *)

Check nat_ind.
(*
nat_ind : forall P : nat -> Prop,
            P 0 ->
            (forall n : nat,
               P n -> P (S n)) ->
            forall n : nat,
              P n
*)

(* ********** *)

(* An induction principle with two steps
   instead of one:
*)

Lemma nat_ind2 :
  forall P : nat -> Prop,
    P 0 ->
    P 1 ->
    (forall i : nat,
      P i -> P (S i) -> P (S (S i))) ->
    forall n : nat,
      P n.
Proof.
  intros P H_P0 H_P1 H_PSS n.
  assert (consecutive :
    forall x : nat,
      P x /\ P (S x)).
    intro x.
    induction x as [ | x' [IHx' IHSx']].

    split.
      exact H_P0.
    exact H_P1.

    split.
      exact IHSx'.
    exact (H_PSS x' IHx' IHSx').

  destruct (consecutive n) as [ly _].
  exact ly.
Qed.

(* ********** *)

(* Let us revisit evenp: *)

Definition specification_of_evenp (evenp : nat -> bool) :=
  (evenp 0 = true)
  /\
  (evenp 1 = false)
  /\
  (forall n'' : nat,
     evenp (S (S n'')) = evenp n'').

(* Uniqueness of the specification: *)

Proposition there_is_only_one_evenp :
  forall f g : nat -> bool,
    specification_of_evenp f ->
    specification_of_evenp g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_evenp.
  intros [Hf_0 [Hf_1 Hf_ij]] [Hg_0 [Hg_1 Hg_ij]] n.
(* We could write
     apply (nat_ind2 ... ... ... ... n).
   but that would be notationally daunting.
*)
  induction n as [ | | n' IH_n' IH_Sn'] using nat_ind2.  

  rewrite -> Hf_0.
  rewrite -> Hg_0.
  reflexivity.

  rewrite -> Hf_1.
  rewrite -> Hg_1.
  reflexivity.

  rewrite -> Hf_ij.
  rewrite -> Hg_ij.
  exact IH_n'.
Qed.

(* ********** *)

(* Let us revisit fibonacci: *)

Definition specification_of_the_fibonacci_function (fib : nat -> nat) :=
  fib 0 = 0
  /\
  fib 1 = 1
  /\
  forall n'' : nat,
    fib (S (S n'')) = fib (S n'') + fib n''.

Theorem there_is_only_one_fibonacci_function :
  forall fib1 fib2 : nat -> nat,
    specification_of_the_fibonacci_function fib1 ->
    specification_of_the_fibonacci_function fib2 ->
    forall n : nat,
      fib1 n = fib2 n.
Proof.
  intros fib1 fib2.
  unfold specification_of_the_fibonacci_function.
  intros [H_fib1_bc0 [H_fib1_bc1 H_fib1_ic]]
         [H_fib2_bc0 [H_fib2_bc1 H_fib2_ic]].
  intro n.
  induction n as [ | | n' IH_n' IH_Sn'] using nat_ind2.
  
  	rewrite -> H_fib2_bc0.
        exact H_fib1_bc0.

        rewrite -> H_fib2_bc1.
        exact H_fib1_bc1.

        rewrite -> H_fib1_ic.
        rewrite -> H_fib2_ic.        
        rewrite -> IH_n'.
        rewrite -> IH_Sn'.
        reflexivity.
Qed.
(* Replace "Abort." with a proof. *)

(* ********** *)

(* Let us revisit nat_ind: *)

Lemma nat_ind1 :
  forall P : nat -> Prop,
    P 0 ->
    (forall i : nat,
      P i -> P (S i)) ->
    forall n : nat,
      P n.
Proof.
  intros P H_bc H_ic n.
  induction n as [ | | n'' IH_n'' IH_Sn''] using nat_ind2.

  exact H_bc.

  exact (H_ic 0 H_bc).

  apply (H_ic (S n'') IH_Sn'').

  Restart.
  (* Replace "Restart." with a proof. *)

  intros P H_bc H_ic n.
  induction n as [ | n' IHn'].

  exact H_bc.

  exact (H_ic n' IHn').
Qed.

(* ********** *)

(* Exercises:

   (1) define nat_ind3 and *)

Lemma nat_ind3 :
  forall P : nat -> Prop,
    P 0 ->
    P 1 ->
    P 2 ->
    (forall i : nat,
      P i -> P (S i) -> P (S (S i)) -> P (S (S (S i)))) ->
    forall n : nat,
      P n.
Proof.
(* (a) prove by induction *)
  intros P H_P0 H_P1 H_P2 H_PSSS n.
  assert (consecutive :
            forall x : nat,
              P x /\ P (S x) /\ P (S (S x))).
	intro x.
        induction x as [ | x' [IHx' [IHSx' IHSSx']]].
        
        split.
        exact H_P0.
        
        split.
          exact H_P1.
        exact H_P2.
        
        split.
        exact IHSx'.
        
        split.
          exact IHSSx'.
        exact (H_PSSS x' IHx' IHSx' IHSSx').

      destruct (consecutive n) as [ly _].
      exact ly.

      Restart.

(* (b) prove by using nat_ind1 *)
  intros P H_P0 H_P1 H_P2 H_PSSS n.
  assert (consecutive :
            forall x : nat,
              P x /\ P (S x) /\ P (S (S x))).
  	intro x.
        induction x as [ | x' [IHx' [IHSx' IHSSx']]] using nat_ind1.
        
        split.
        exact H_P0.
        
        split.
          exact H_P1.
        exact H_P2.

        split.
        exact IHSx'.

        split.
         exact IHSSx'.
        exact (H_PSSS x' IHx' IHSx' IHSSx').
        
        destruct (consecutive n) as [ly _].
      exact ly.
      
      Restart.

(* (c) prove by using nat_ind2 *)
  intros P H_P0 H_P1 H_P2 H_PSSS n.
  assert (consecutive :
            forall x : nat,
              P x /\ P (S x)).
  	intro x.
        induction x as [ | | x' [IHx' IHSx' ]] using nat_ind2.
        
        split.
          exact H_P0.
        exact H_P1.
        
        split.
          exact H_P1.
        exact H_P2.
        
        destruct IHx as [IHx_bc IHx_ic].
        split.
         exact IHx_ic.
        exact (H_PSSS x' IHx' IHSx' IHx_ic).

        destruct (consecutive n) as [ly _].
        exact ly.
Qed.

(* 2.a prove nat_ind1 using nat_ind3 *)
Lemma nat_ind1_prove_by_using_nat_ind_3 :
  forall P : nat -> Prop,
    P 0 ->
    (forall i : nat,
      P i -> P (S i)) ->
    forall n : nat,
      P n.
Proof.
  intros P H_bc H_ic n.
  induction n as [ | | | n' IH_n' IH_Sn' IH_SSn'] using nat_ind3.
  exact H_bc.
  exact (H_ic 0 H_bc).
  exact (H_ic 1 (H_ic 0 H_bc)).
  
  exact (H_ic (S (S n')) IH_SSn').
Qed.


  
(*
        2.(b) prove nat_ind2
*)
Lemma nat_ind2_prove_by_using_nat_ind_3 :
  forall P : nat -> Prop,
    P 0 ->
    P 1 ->
    (forall i : nat,
      P i -> P (S i) -> P (S (S i))) ->
    forall n : nat,
      P n.
Proof.
  intros P H_P0 H_P1 H_PSS n.
  induction n as [ | | | n' IH_n' IH_Sn' IH_SSn'] using nat_ind3.
  
  exact H_P0.
  exact H_P1.
  exact (H_PSS 0 H_P0 H_P1).

  exact (H_PSS (S n') IH_Sn' IH_SSn').
Qed.
(* ********** *)

(* end of week_38b_induction_after_todays_lecture.v *)
