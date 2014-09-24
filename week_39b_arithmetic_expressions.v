(* week_39b_arithmetic_expressions.v *)
(* dIFP 2014-2015, Q1, Week 38 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* Working version, make sure to download
   the updated version after class.
*)

(* ********** *)

<<<<<<< HEAD
Require Import Arith Bool unfold_tactic List.
=======
Require Import Arith Bool unfold_tactic.
>>>>>>> FETCH_HEAD

(* ********** *)

(* Source syntax: *)

Inductive arithmetic_expression : Type :=
  | Lit : nat -> arithmetic_expression
  | Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
  | Times : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

(* Exercise 0:
   Write samples of arithmetic expressions.
*)

<<<<<<< HEAD
Definition ae_0 :=
  Lit 42.

Definition ae_1 :=
  Plus (Lit 10)
       (Lit 20).

Definition ae_2 :=
  Times (Plus (Lit 10)
             (Lit 20))
       (Lit 3).

=======
>>>>>>> FETCH_HEAD
(* ********** *)

Definition specification_of_interpret (interpret : arithmetic_expression -> nat) :=
  (forall n : nat,
     interpret (Lit n) = n)
  /\
  (forall ae1 ae2 : arithmetic_expression,
     interpret (Plus ae1 ae2) = (interpret ae1) + (interpret ae2))
  /\
  (forall ae1 ae2 : arithmetic_expression,
     interpret (Times ae1 ae2) = (interpret ae1) * (interpret ae2)).

(* Exercise 1:
   Write unit tests.
*)

<<<<<<< HEAD
Notation "A =n= B" := (beq_nat A B) (at level 70, right associativity).

Definition unit_tests_for_arithmetic_expressions (candidate : arithmetic_expression -> nat) :=
  (candidate ae_0 =n= 42)
    &&
    (candidate ae_1 =n= 30)
    &&
    (candidate ae_2 =n= 90).

=======
>>>>>>> FETCH_HEAD
(* Exercise 2:
   Define an interpreter as a function
   that satisfies the specification above
   and verify that it passes the unit tests.
*)

<<<<<<< HEAD
Fixpoint interpreter (e : arithmetic_expression) : nat :=
  match e with
    | Lit n => n
    | Plus e1 e2 => (interpreter e1) + (interpreter e2)
    | Times e1 e2 => (interpreter e1) * (interpreter e2)
  end.

Lemma unfold_interpreter_lit :
  forall n : nat,
    interpreter (Lit n) = n.
Proof.
  unfold_tactic interpreter.
Qed.

Lemma unfold_interpreter_plus :
  forall e1 e2 : arithmetic_expression,
    interpreter (Plus e1 e2) = (interpreter e1) + (interpreter e2).
Proof.
  unfold_tactic interpreter.
Qed.

Lemma unfold_interpreter_times :
  forall e1 e2 : arithmetic_expression,
    interpreter (Times e1 e2) = (interpreter e1) * (interpreter e2).
Proof.
  unfold_tactic interpreter.
Qed.


Definition interpreter_v0 (e : arithmetic_expression) : nat :=
  interpreter e.

Compute unit_tests_for_arithmetic_expressions interpreter_v0.


Proposition interpreter_satisfies_the_specification_of_interpret :
  specification_of_interpret interpreter_v0.           
Proof.
  unfold specification_of_interpret.
  unfold interpreter_v0.
  split.

    exact unfold_interpreter_lit.

  split.

    exact unfold_interpreter_plus.

  exact unfold_interpreter_times.
Qed.

=======
>>>>>>> FETCH_HEAD
(* Byte-code instructions: *)

Inductive byte_code_instruction : Type :=
  | PUSH : nat -> byte_code_instruction
  | ADD : byte_code_instruction
  | MUL : byte_code_instruction.

(* ********** *)

(* Byte-code programs: *)

Definition byte_code_program := list byte_code_instruction.

(* Data stack: *)

Definition data_stack := list nat.

(* ********** *)

(* Exercise 3:
   specify a function
     execute_byte_code_instruction : instr -> data_stack -> data_stack
   that executes a byte-code instruction, given a data stack
   and returns this stack after the instruction is executed.

<<<<<<< HEAD
   * Executing (PUSH n) given s has the effect of pushing n on s.       (cons on list)
=======
   * Executing (PUSH n) given s has the effect of pushing n on s.
>>>>>>> FETCH_HEAD

   * Executing ADD given s has the effect of popping two numbers
     from s and then pushing the result of adding them.

   * Executing MUL given s has the effect of popping two numbers
     from s and then pushing the result of multiplying them.

   For now, if the stack underflows, just assume it contains zeroes.
*)

<<<<<<< HEAD
Definition ae_4 :=
  PUSH 4.


Definition specification_of_execute_byte_code_instruction (execute : byte_code_instruction -> data_stack -> data_stack
) :=

  (forall (n : nat) (s : data_stack),
     execute (PUSH n) s = (n :: s))
  /\
  (forall (n1 n2 : nat) (s t : data_stack),
     execute ADD (n1 :: n2 :: t) = execute (PUSH (n1 + n2)) t)
  /\
  (forall (n1 n2 : nat) (s t : data_stack),
     execute MUL (n1 :: n2 :: t) = execute (PUSH (n1 * n2)) t).

(* IKKE FIXPOINT da funktionen ikke er rekursiv (det er en straight-line interpreter, rekursion er ubrugelig) *)
Definition execute_byte_code_instruction (instr : byte_code_instruction) (s : data_stack) : data_stack :=
  match instr with
    | (PUSH n) => (n :: s)
    | ADD =>
      match s with
        | (n1 :: n2 :: t) => ((n1 + n2) :: t)
        | (n1 :: nil) => (n1 :: nil)
        | (nil) => (0 :: nil)
      end
    | MUL =>
      match s with
        | (n1 :: n2 :: t) => ((n1 * n2) :: t)
        | (n1 :: nil) => (0 :: nil)
        | (nil) => (0 :: nil)
      end
  end.

Lemma unfold_execute_byte_code_instruction_push :
  forall (n : nat) (s : data_stack),
    execute_byte_code_instruction (PUSH n) s = (n :: s).
Proof.                                                                                                              
  unfold_tactic execute_byte_code_instruction.
Qed.

Lemma unfold_execute_byte_code_instruction_add :
  forall (n : nat) (s : data_stack),
    execute_byte_code_instruction ADD s = match s with
                                            | (n1 :: n2 :: t) => ((n1 + n2) :: t)
                                            | (n1 :: nil) => (n1 :: nil)
                                            | (nil) => (0 :: nil)
                                          end.
Proof.                                                                                                              
  unfold_tactic execute_byte_code_instruction.
Qed.

Lemma unfold_execute_byte_code_instruction_mul :
  forall (n : nat) (s : data_stack),
    execute_byte_code_instruction MUL s = match s with
                                            | (n1 :: n2 :: t) => ((n1 * n2) :: t)
                                            | (n1 :: nil) => (0 :: nil)
                                            | (nil) => (0 :: nil)
                                          end.
Proof.                                                                                                              
  unfold_tactic execute_byte_code_instruction.
Qed.



Definition execute_byte_code_instruction_v0 (instr : byte_code_instruction) (s : data_stack) : data_stack :=
  execute_byte_code_instruction instr s.



=======
>>>>>>> FETCH_HEAD
(* ********** *)

(* Exercise 4:
   Define a function
     execute_byte_code_program : byte_code_program -> data_stack -> data_stack
   that executes a given byte-code program on a given data stack,
   and returns this stack after the program is executed.
*)

<<<<<<< HEAD
Fixpoint execute_byte_code_program (program : byte_code_program) (s : data_stack) : data_stack :=
  match program with
    | 

=======
>>>>>>> FETCH_HEAD
(* ********** *)

(* Exercise 5:
   Prove that for all programs p1, p2 and data stacks s,
   executing (p1 ++ p2) with s
   gives the same result as
   (1) executing p1 with s, and then
   (2) executing p2 with the resulting stack.
*)

(* ********** *)

Definition specification_of_compile (compile : arithmetic_expression -> byte_code_program) :=
  (forall n : nat,
     compile (Lit n) = PUSH n :: nil)
  /\
  (forall ae1 ae2 : arithmetic_expression,
     compile (Plus ae1 ae2) = (compile ae1) ++ (compile ae2) ++ (ADD :: nil))
  /\
  (forall ae1 ae2 : arithmetic_expression,
     compile (Times ae1 ae2) = (compile ae1) ++ (compile ae2)++ (MUL :: nil)).

(* Exercise 6:
   Define a compiler as a function
   that satisfies the specification above
   and uses list concatenation, i.e., ++.
*)

(* Exercise 7:
   Write a compiler as a function with an accumulator
   that does not use ++ but :: instead,
   and prove it equivalent to the compiler of Exercise 6.
*)

(* ********** *)

(* Exercise 8:
   Prove that interpreting an arithmetic expression gives the same result
   as first compiling it and then executing the compiled program
   over an empty data stack.
<<<<<<< HEAD

   by structural induction in the arithmetic expression???
=======
>>>>>>> FETCH_HEAD
*)

(* ********** *)

(* Exercise 9:
   Write a Magritte-style execution function for a byte-code program
   that does not operate on natural numbers but on syntactic representations
   of natural numbers:

   Definition data_stack := list arithmetic_expression.

   * Executing (PUSH n) given s has the effect of pushing (Lit n) on s.

   * Executing ADD given s has the effect of popping two arithmetic
     expressions from s and then pushing the syntactic representation of
     their addition.

   * Executing MUL given s has the effect of popping two arithmetic
     expressions from s and then pushing the syntactic representation of
     their multiplication.

   Again, for this week's exercise,
   assume there are enough arithmetic expressions on the data stack.
   If that is not the case, just pad it up with syntactic representations
   of zero.

*)

(* Exercise 10:
   Prove that the Magrite-style execution function from Exercise 9
   implements a decompiler that is the left inverse of the compiler
   of Exercise 6.
*)

(* ********** *)

(* end of week_39b_arithmetic_expressions.v *)