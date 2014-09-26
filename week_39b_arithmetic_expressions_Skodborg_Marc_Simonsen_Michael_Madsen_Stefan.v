(* week_39b_arithmetic_expressions.v *)
(* dIFP 2014-2015, Q1, Week 38 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* Working version, make sure to download
   the updated version after class.
*)

(* ********** *)

Require Import Arith Bool unfold_tactic List.

(* ********** *)

(* Source syntax: *)

Inductive arithmetic_expression : Type :=
  | Lit : nat -> arithmetic_expression
  | Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
  | Times : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
  | Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

(* Exercise 0:
   Write samples of arithmetic expressions.
*)

Definition ae_0 :=
  Lit 42.

Definition ae_1 :=
  Plus (Lit 10)
       (Lit 20).

Definition ae_2 :=
  Times (Plus (Lit 10)
             (Lit 20))
       (Lit 3).

Definition ae_3 :=
  Minus (Lit 30)
        (Lit 10).

(* ********** *)

Definition specification_of_interpret (interpret : arithmetic_expression -> nat) :=
  (forall n : nat,
     interpret (Lit n) = n)
  /\
  (forall ae1 ae2 : arithmetic_expression,
     interpret (Plus ae1 ae2) = (interpret ae1) + (interpret ae2))
  /\
  (forall ae1 ae2 : arithmetic_expression,
     interpret (Times ae1 ae2) = (interpret ae1) * (interpret ae2))
  /\
  (forall ae1 ae2 : arithmetic_expression,
     interpret (Minus ae1 ae2) = (interpret ae1) - (interpret ae2)).

(* Exercise 1:
   Write unit tests.
*)

Notation "A =n= B" := (beq_nat A B) (at level 70, right associativity).

Definition unit_tests_for_arithmetic_expressions (candidate : arithmetic_expression -> nat) :=
  (candidate ae_0 =n= 42)
    &&
    (candidate ae_1 =n= 30)
    &&
    (candidate ae_2 =n= 90)
    &&
    (candidate ae_3 =n= 20).

(* Exercise 2:
   Define an interpreter as a function
   that satisfies the specification above
   and verify that it passes the unit tests.
*)

Proposition there_is_only_one_interpret_arithmetic_expression :
  forall interpret1 interpret2 : arithmetic_expression -> nat,
    specification_of_interpret interpret1 ->
    specification_of_interpret interpret2 ->
    forall ae : arithmetic_expression,
      interpret1 ae = interpret2 ae.
Proof.
  intros interpret1 interpret2.
  unfold specification_of_interpret.
  intros [S_interpret1_lit [S_interpret1_plus [S_interpret1_times S_interpret1_minus]]].
  intros [S_interpret2_lit [S_interpret2_plus [S_interpret2_times S_interpret2_minus]]].
  intro ae.
  induction ae as [ | ae1 IHae1 | ae2 IHae2 | ae3 IHae3].
        rewrite -> S_interpret2_lit.
        apply S_interpret1_lit.

      rewrite -> S_interpret2_plus.
      rewrite <- IHae1.
      rewrite <- IHae2.
      apply S_interpret1_plus.

    rewrite -> S_interpret2_times.
    rewrite <- IHae1.
    rewrite <- IHae2.
    apply S_interpret1_times.

  rewrite -> S_interpret2_minus.
  rewrite <- IHae1.
  rewrite <- IHae3.
  apply S_interpret1_minus.
Qed.

Fixpoint interpreter (e : arithmetic_expression) : nat :=
  match e with
    | Lit n => n
    | Plus e1 e2 => (interpreter e1) + (interpreter e2)
    | Times e1 e2 => (interpreter e1) * (interpreter e2)
    | Minus e1 e2 => (interpreter e1) - (interpreter e2)
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

Lemma unfold_interpreter_minus :
  forall e1 e2 : arithmetic_expression,
    interpreter (Minus e1 e2) = (interpreter e1) - (interpreter e2).
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

  split.
    exact unfold_interpreter_times.

  exact unfold_interpreter_minus.
Qed.

(* Byte-code instructions: *)

Inductive byte_code_instruction : Type :=
  | PUSH : nat -> byte_code_instruction
  | ADD : byte_code_instruction
  | MUL : byte_code_instruction
  | SUB : byte_code_instruction.


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

   * Executing (PUSH n) given s has the effect of pushing n on s.       (cons on list)

   * Executing ADD given s has the effect of popping two numbers
     from s and then pushing the result of adding them.

   * Executing MUL given s has the effect of popping two numbers
     from s and then pushing the result of multiplying them.

   For now, if the stack underflows, just assume it contains zeroes.
*)

Definition specification_of_execute_byte_code_instruction (execute : byte_code_instruction -> data_stack -> data_stack) :=

  (forall (n : nat) (s : data_stack),
     execute (PUSH n) s = (n :: s))
  /\
  (forall (n1 n2 : nat) (s : data_stack),
     execute ADD s = match s with
        | (n1 :: n2 :: s) => ((n2 + n1) :: s)
        | (n1 :: nil) => (n1 :: nil)
        | (nil) => (0 :: nil)
      end)
  /\
  (forall (n1 n2 : nat) (s : data_stack),
     execute MUL s = match s with
        | (n1 :: n2 :: s) => ((n2 * n1) :: s)
        | (n1 :: nil) => (0 :: nil)
        | (nil) => (0 :: nil)
      end)
  /\
  (forall (n1 n2 : nat) (s : data_stack),
     execute SUB s = match s with
        | (n1 :: n2 :: s) => ((n2 - n1) :: s)
        | (n1 :: nil) => (0 :: nil)
        | (nil) => (0 :: nil)
      end).

Proposition there_is_only_one_execute_byte_code_instruction :
  forall execute1 execute2 : byte_code_instruction -> data_stack -> data_stack,
    specification_of_execute_byte_code_instruction execute1 ->
    specification_of_execute_byte_code_instruction execute2 ->
    forall (bc : byte_code_instruction) (s : data_stack),
      execute1 bc s = execute2 bc s.
Proof.
  intros execute1 execute2.
  intros [S_execute1_push [S_execute1_add [S_execute1_mul S_execute1_sub]]].
  intros [S_execute2_push [S_execute2_add [S_execute2_mul S_execute2_sub]]].
  intros bc s.
  assert (a := 0).
  induction bc.
        rewrite -> S_execute2_push.
        apply S_execute1_push.

      rewrite -> (S_execute2_add a a).
      apply (S_execute1_add a a).

    rewrite -> (S_execute2_mul a a).
    apply (S_execute1_mul a a).

  rewrite -> (S_execute2_sub a a).
  apply (S_execute1_sub a a).
Qed.

Require Import week_37b_lists_Skodborg_Marc_Simonsen_Michael_Madsen_Stefan.

Definition unit_tests_for_byte_code_instruction (candidate : byte_code_instruction -> data_stack -> data_stack) :=
  (equal_list_nat (candidate (PUSH 5) nil) 
                  (5 :: nil))
  &&
  (equal_list_nat (candidate ADD (2 :: 4 :: nil)) 
                  (6 :: nil))
  &&
  (equal_list_nat (candidate MUL (2 :: 4 :: nil)) 
                  (8 :: nil))
  &&
  (equal_list_nat (candidate SUB (5 :: 20 :: nil)) 
                  (15 :: nil)).

(* IKKE FIXPOINT da funktionen ikke er rekursiv (det er en straight-line interpreter, rekursion er ubrugelig) *)
Definition execute_byte_code_instruction (instr : byte_code_instruction) (s : data_stack) : data_stack :=
  match instr with
    | (PUSH n) => (n :: s)
    | ADD =>
      match s with
        | (n1 :: n2 :: t) => ((n2 + n1) :: t)
        | (n1 :: nil) => (n1 :: nil)
        | (nil) => (0 :: nil)
      end
    | MUL =>
      match s with
        | (n1 :: n2 :: t) => ((n2 * n1) :: t)
        | (n1 :: nil) => (0 :: nil)
        | (nil) => (0 :: nil)
      end
    | SUB =>
      match s with
        | (n1 :: n2 :: t) => ((n2 - n1) :: t)
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
  forall (s : data_stack),
    execute_byte_code_instruction ADD s = match s with
                                            | (n1 :: n2 :: t) => ((n2 + n1) :: t)
                                            | (n1 :: nil) => (n1 :: nil)
                                            | (nil) => (0 :: nil)
                                          end.
Proof.                                                                                                              
  unfold_tactic execute_byte_code_instruction.
Qed.

Lemma unfold_execute_byte_code_instruction_mul :
  forall (s : data_stack),
    execute_byte_code_instruction MUL s = match s with
                                            | (n1 :: n2 :: t) => ((n2 * n1) :: t)
                                            | (n1 :: nil) => (0 :: nil)
                                            | (nil) => (0 :: nil)
                                          end.
Proof.                                                                                                              
  unfold_tactic execute_byte_code_instruction.
Qed.

Lemma unfold_execute_byte_code_instruction_sub :
  forall (s : data_stack),
    execute_byte_code_instruction SUB s = match s with
                                            | (n1 :: n2 :: t) => ((n2 - n1) :: t)
                                            | (n1 :: nil) => (0 :: nil)
                                            | (nil) => (0 :: nil)
                                          end.
Proof.                                                                                                              
  unfold_tactic execute_byte_code_instruction.
Qed.

Definition execute_byte_code_instruction_v0 (instr : byte_code_instruction) (s : data_stack) : data_stack :=
  execute_byte_code_instruction instr s.

Compute unit_tests_for_byte_code_instruction execute_byte_code_instruction_v0.

Proposition execute_byte_code_satisfies_the_specification_of_execute_byte_code_instruction :
  specification_of_execute_byte_code_instruction execute_byte_code_instruction_v0.
Proof.
  unfold specification_of_execute_byte_code_instruction.
  unfold execute_byte_code_instruction_v0.
  split.
    exact unfold_execute_byte_code_instruction_push.

  split.
    intros n1 n2.
    exact unfold_execute_byte_code_instruction_add.

  split.
    intros n1 n2.
    exact unfold_execute_byte_code_instruction_mul.

  intros n1 n2.
  exact unfold_execute_byte_code_instruction_sub.
Qed.

(* ********** *)

(* Exercise 4:
   Define a function
     execute_byte_code_program : byte_code_program -> data_stack -> data_stack
   that executes a given byte-code program on a given data stack,
   and returns this stack after the program is executed.
*)

Definition specification_of_execute_byte_code_program (execute : byte_code_program -> data_stack -> data_stack) :=
  (forall (s : data_stack),
     execute nil s = s)
  /\
  (forall (instr : byte_code_instruction) (prog : byte_code_program) (s : data_stack),
     execute (instr :: prog) s = (execute prog (execute_byte_code_instruction_v0 instr s))).

Definition unit_tests_for_byte_code_program (candidate : byte_code_program -> data_stack -> data_stack) :=
  (equal_list_nat (candidate (PUSH 5 :: PUSH 5 :: nil) nil) 
                  (5 :: 5 :: nil))
  &&
  (equal_list_nat (candidate (PUSH 5 :: PUSH 5 :: ADD :: nil) nil) 
                  (10 :: nil))
  &&
  (equal_list_nat (candidate (PUSH 5 :: PUSH 5 :: MUL :: nil) nil) 
                  (25 :: nil))
  &&
  (equal_list_nat (candidate (PUSH 5 :: PUSH 5 :: PUSH 5 :: MUL :: ADD :: nil) nil) 
                  (30 :: nil))
  &&
  (equal_list_nat (candidate (PUSH 20 :: PUSH 5 :: SUB :: nil) nil)
                  (15 :: nil)).

Proposition there_is_only_one_execute_byte_code_program :
  forall execute1 execute2 : byte_code_program -> data_stack -> data_stack,
    specification_of_execute_byte_code_program execute1 ->
    specification_of_execute_byte_code_program execute2 ->
    forall (p : byte_code_program) (s : data_stack),
      execute1 p s = execute2 p s.
Proof.
  intros execute1 execute2.
  intros [S_execute1_bc S_execute1_ic] [S_execute2_bc S_execute2_ic].
  intros p.
  induction p as [ | p' ps' IHps'].
    intro s.
    rewrite -> S_execute2_bc.
    apply S_execute1_bc.

  intro s.
  rewrite -> S_execute2_ic.
  rewrite <- IHps'.
  apply S_execute1_ic.
Qed.

Fixpoint execute_byte_code_program (prog : byte_code_program) (s : data_stack) : data_stack :=
  match prog with
    | nil => s
    | (h :: t) => (execute_byte_code_program t (execute_byte_code_instruction_v0 h s))
  end.

Lemma unfold_execute_byte_code_program_bc :
  forall s : data_stack,
    execute_byte_code_program nil s = s.
Proof.
  unfold_tactic execute_byte_code_program.
Qed.

Lemma unfold_execute_byte_code_program_ic :
  forall (h : byte_code_instruction) (t : byte_code_program) (s : data_stack),
    execute_byte_code_program (h :: t) s = (execute_byte_code_program t (execute_byte_code_instruction_v0 h s)).
Proof.
  unfold_tactic execute_byte_code_program.
Qed.


Definition execute_byte_code_program_v0 (prog : byte_code_program) (s : data_stack) : data_stack :=
  execute_byte_code_program prog s.

Compute unit_tests_for_byte_code_program execute_byte_code_program_v0.

Proposition execute_byte_code_program_satisfies_the_specification :
  specification_of_execute_byte_code_program execute_byte_code_program_v0.           
Proof.
  unfold specification_of_execute_byte_code_program.
  unfold execute_byte_code_program_v0.
  split.
    exact unfold_execute_byte_code_program_bc.

  exact unfold_execute_byte_code_program_ic.
Qed.

(* ********** *)

(* Exercise 5:
   Prove that for all programs p1, p2 and data stacks s,
   executing (p1 ++ p2) with s
   gives the same result as
   (1) executing p1 with s, and then
   (2) executing p2 with the resulting stack.
*)

Proposition about_execute_byte_code_program :
  forall (execute : byte_code_program -> data_stack -> data_stack),
    specification_of_execute_byte_code_program execute ->
    forall (p1 p2 : byte_code_program) (s : data_stack),
      execute (p1 ++ p2) s = execute p2 (execute p1 s).
Proof.
  intros execute.
  intros [S_execute_bc S_execute_ic].
  intros p1.
  induction p1 as [ | p1' p1s' IHp1s' ].
    intros p2 s.
    rewrite -> S_execute_bc.
    rewrite -> app_nil_l.
    reflexivity.

  intros p2 s.
  rewrite -> S_execute_ic.
  rewrite <- IHp1s'.
  rewrite <- app_comm_cons.
  rewrite -> S_execute_ic.
  reflexivity.
Qed.

(* ********** *)

Definition specification_of_compile (compile : arithmetic_expression -> byte_code_program) :=
  (forall n : nat,
     compile (Lit n) = PUSH n :: nil)
  /\
  (forall ae1 ae2 : arithmetic_expression,
     compile (Plus ae1 ae2) = (compile ae1) ++ (compile ae2) ++ (ADD :: nil))
  /\
  (forall ae1 ae2 : arithmetic_expression,
     compile (Times ae1 ae2) = (compile ae1) ++ (compile ae2)++ (MUL :: nil))
  /\
  (forall ae1 ae2 : arithmetic_expression,
     compile (Minus ae1 ae2) = (compile ae1) ++ (compile ae2)++ (SUB :: nil)).

(* Exercise 6:
   Define a compiler as a function
   that satisfies the specification above
   and uses list concatenation, i.e., ++.
*)

Definition beq_bci (x y : byte_code_instruction) : bool :=
  match x with
    | PUSH n => match y with
                  | PUSH m => (beq_nat n m)
                  | _ => false
                end
    | ADD => match y with
               | ADD => true
               | _ => false
             end
    | MUL => match y with
               | MUL => true
               | _ => false
             end
    | SUB => match y with
               | SUB => true
               | _ => false
             end
  end.

Fixpoint beq_list (T : Type) (beq : T -> T -> bool) (xs ys : list T) : bool :=
  match xs with
    | nil =>
      match ys with
        | nil => true
        | y :: ys' => false
      end
    | x :: xs' =>
      match ys with
        | nil => false
        | y :: ys' => (beq x y) && (beq_list T beq xs' ys')
      end
  end.

Definition beq_bcp (xs ys : byte_code_program) : bool :=
  beq_list byte_code_instruction beq_bci xs ys.

Notation "A =bcp= B" := (beq_bcp A B) (at level 70, right associativity).

Definition unit_tests_for_compile (compile : arithmetic_expression -> byte_code_program) :=
   ((compile (Lit 5)) =bcp= (PUSH 5 :: nil))
   &&
   ((compile ae_0) =bcp= (PUSH 42 :: nil))
   &&
   ((compile ae_1) =bcp= (PUSH 10 :: PUSH 20 :: ADD :: nil))
   &&
   ((compile ae_2) =bcp= (PUSH 10 :: PUSH 20 :: ADD :: PUSH 3 :: MUL :: nil))
   &&
   ((compile ae_3) =bcp= (PUSH 30 :: PUSH 10 :: SUB :: nil)).
   



Proposition there_is_only_one_compile :
  forall compile1 compile2 : arithmetic_expression -> byte_code_program,
    specification_of_compile compile1 ->
    specification_of_compile compile2 ->
    forall (ae : arithmetic_expression),
      compile1 ae = compile2 ae.
Proof.
  intros compile1 compile2.
  unfold specification_of_compile.
  intros [S_compile1_lit [S_compile1_plus [S_compile1_times S_compile1_minus]]].
  intros [S_compile2_lit [S_compile2_plus [S_compile2_times S_compile2_minus]]].
  intro ae.
  induction ae as [ | ae1' IHae1' ae2' IHae2' | ae1'' IHae1'' ae2'' IHae2'' | ae1''' IHae1''' ae2''' IHae2''' ].
        rewrite S_compile2_lit.
        exact (S_compile1_lit n).

      rewrite S_compile2_plus.
      rewrite <- IHae1'.
      rewrite <- IHae2'.
      exact (S_compile1_plus ae1' ae2').

    rewrite S_compile2_times.
    rewrite <- IHae1''.
    rewrite <- IHae2''.
    exact (S_compile1_times ae1'' ae2'').

  rewrite S_compile2_minus.
  rewrite <- IHae1'''.
  rewrite <- IHae2'''.
  exact (S_compile1_minus ae1''' ae2''').
Qed.

Fixpoint compile (ae : arithmetic_expression) : byte_code_program :=
  match ae with
    | Lit n => ((PUSH n) :: nil)
    | Plus ae1 ae2 => (compile ae1) ++ (compile ae2) ++ (ADD :: nil)
    | Times ae1 ae2 => (compile ae1) ++ (compile ae2) ++ (MUL :: nil)
    | Minus ae1 ae2 => (compile ae1) ++ (compile ae2) ++ (SUB :: nil)
  end.

Lemma unfold_compile_lit :
  forall n : nat,
    compile (Lit n) = ((PUSH n) :: nil).
Proof.
  unfold_tactic compile.
Qed.

Lemma unfold_compile_plus :
  forall ae1 ae2 : arithmetic_expression,
    compile (Plus ae1 ae2) = (compile ae1) ++ (compile ae2) ++ (ADD :: nil).
Proof.  
  unfold_tactic compile.
Qed.

Lemma unfold_compile_times :
  forall ae1 ae2 : arithmetic_expression,
    compile (Times ae1 ae2) = (compile ae1) ++ (compile ae2) ++ (MUL :: nil).
Proof.  
  unfold_tactic compile.
Qed.

Lemma unfold_compile_minus : 
  forall ae1 ae2 : arithmetic_expression,
    compile (Minus ae1 ae2) = (compile ae1) ++ (compile ae2) ++ (SUB :: nil).
Proof.  
  unfold_tactic compile.
Qed.

Definition compile_v0 (ae : arithmetic_expression) : byte_code_program :=
  compile ae.

Compute unit_tests_for_compile compile_v0.

Proposition compile_v0_satisfies_the_specification_of_compile :
  specification_of_compile compile_v0.
Proof.
  unfold specification_of_compile.
  unfold compile_v0.
  split.
    exact unfold_compile_lit.

  split.
    exact unfold_compile_plus.

  split.
    exact unfold_compile_times.

  exact unfold_compile_minus.
Qed.

(* Exercise 7:
   Write a compiler as a function with an accumulator
   that does not use ++ but :: instead,
   and prove it equivalent to the compiler of Exercise 6.
*)

Fixpoint compile_acc (ae : arithmetic_expression) (acc : byte_code_program) : byte_code_program :=
  match ae with
    | Lit n => ((PUSH n) :: acc)
    | Plus ae1 ae2 => compile_acc ae1 (compile_acc ae2 (ADD :: acc))
    | Times ae1 ae2 => compile_acc ae1 (compile_acc ae2 (MUL :: acc))
    | Minus ae1 ae2 => compile_acc ae1 (compile_acc ae2 (SUB :: acc))
  end.

Lemma unfold_compile_acc_lit :
  forall (n : nat) (acc : byte_code_program),
    compile_acc (Lit n) acc = ((PUSH n) :: acc).
Proof.
  unfold_tactic compile_acc.
Qed.

Lemma unfold_compile_acc_plus :
  forall (ae1 ae2 : arithmetic_expression) (acc : byte_code_program),
    compile_acc (Plus ae1 ae2) acc = compile_acc ae1 (compile_acc ae2 (ADD :: acc)).
Proof.  
  unfold_tactic compile_acc.
Qed.

Lemma unfold_compile_acc_times :
  forall (ae1 ae2 : arithmetic_expression) (acc :byte_code_program),
    compile_acc (Times ae1 ae2) acc = compile_acc ae1 (compile_acc ae2 (MUL :: acc)).
Proof.  
  unfold_tactic compile_acc.
Qed.

Lemma unfold_compile_acc_minus :
  forall (ae1 ae2 : arithmetic_expression) (acc :byte_code_program),
    compile_acc (Minus ae1 ae2) acc = compile_acc ae1 (compile_acc ae2 (SUB :: acc)).
Proof.  
  unfold_tactic compile_acc.
Qed.

Definition compile_v1 (ae : arithmetic_expression) : byte_code_program :=
  compile_acc ae nil.

Compute unit_tests_for_compile compile_v1.

Proposition about_compile_acc :
    forall (ae : arithmetic_expression) (acc : byte_code_program),
      compile_acc ae acc = (compile_acc ae nil) ++ acc.
Proof.
  intro ae.
  induction ae as [ | ae1' IHae1' ae2' IHae2'' | ae1'' IHae1'' ae2'' IHae2'' | ae1''' IHae1''' ae2''' IHae2''' ].
        intro acc.
        rewrite ->2 unfold_compile_acc_lit.
        rewrite <- app_comm_cons.
        rewrite app_nil_l.
        reflexivity.

      intro acc.
      rewrite ->2 unfold_compile_acc_plus.
      rewrite IHae1'.
      rewrite (IHae1' (compile_acc ae2' (ADD :: nil))).
      rewrite IHae2''.
      rewrite (IHae2'' (ADD :: nil)).
      rewrite <- (app_assoc (compile_acc ae1' nil) (compile_acc ae2' nil ++ ADD :: nil) acc).
      rewrite <- (app_assoc (compile_acc ae2' nil) (ADD :: nil) acc).
      rewrite <- (app_comm_cons nil acc ADD).
      rewrite app_nil_l.
      reflexivity.

    intro acc.
    rewrite ->2 unfold_compile_acc_times.
    rewrite IHae1''.
    rewrite (IHae1'' (compile_acc ae2'' (MUL :: nil))).
    rewrite IHae2''.
    rewrite (IHae2'' (MUL :: nil)).
    rewrite <- (app_assoc (compile_acc ae1'' nil) (compile_acc ae2'' nil ++ MUL :: nil) acc).
    rewrite <- (app_assoc (compile_acc ae2'' nil) (MUL :: nil) acc).
    rewrite <- (app_comm_cons nil acc MUL).
    rewrite app_nil_l.
    reflexivity.

  intro acc.
  rewrite ->2 unfold_compile_acc_minus.
  rewrite IHae1'''.
  rewrite (IHae1''' (compile_acc ae2''' (SUB :: nil))).
  rewrite IHae2'''.
  rewrite (IHae2''' (SUB :: nil)).
  rewrite <- (app_assoc (compile_acc ae1''' nil) (compile_acc ae2''' nil ++ SUB :: nil) acc).
  rewrite <- (app_assoc (compile_acc ae2''' nil) (SUB :: nil) acc).
  rewrite <- (app_comm_cons nil acc SUB).
  rewrite app_nil_l.
  reflexivity.
Qed.

Proposition compile_v1_satisfies_the_specification_of_compile :
  specification_of_compile compile_v1.
Proof.
  unfold specification_of_compile.
  unfold compile_v1.
  split.
    intro n.
    apply unfold_compile_acc_lit.

  split.
    intros ae1 ae2.
    rewrite -> unfold_compile_acc_plus.
    rewrite <- about_compile_acc.
    rewrite <- about_compile_acc.
    reflexivity.

  split.
    intros ae1 ae2.
    rewrite -> unfold_compile_acc_times.
    rewrite <- about_compile_acc.
    rewrite <- about_compile_acc.
    reflexivity.

  intros ae1 ae2.
  rewrite -> unfold_compile_acc_minus.
  rewrite <- about_compile_acc.
  rewrite <- about_compile_acc.
  reflexivity.
Qed.


(* ********** *)

(* Exercise 8:
   Prove that interpreting an arithmetic expression gives the same result
   as first compiling it and then executing the compiled program
   over an empty data stack.

   by structural induction in the arithmetic expression???
*)

(* returning the element in the datastack of execute_byte_code_program, if it only contains a single element *)
Definition run (bcp: byte_code_program) : nat :=
  match (execute_byte_code_program_v0 bcp nil) with
    | x :: nil => x
    | _ => 0
  end.

Lemma interpret_equals_compile_and_execute :
  forall (ae : arithmetic_expression) (s : data_stack),
    execute_byte_code_program (compile_v0 ae) s  = (interpreter_v0 ae ) :: s.
Proof.
  intro ae.
  unfold compile_v0.
  unfold interpreter_v0.
  induction ae as [ | ae1 IHae1 ae2 IHae2 | ae1' IHae1' ae2' IHae2' | ae1'' IHae1'' ae2'' IHae2''].
        intro s.
        rewrite unfold_compile_lit.
        rewrite (unfold_execute_byte_code_program_ic (PUSH n) nil s).
        rewrite unfold_execute_byte_code_program_bc.
        unfold execute_byte_code_instruction_v0.
        rewrite (unfold_execute_byte_code_instruction_push n s).
        rewrite unfold_interpreter_lit.
        reflexivity.

      intro s.
      rewrite (unfold_compile_plus ae1 ae2).
      rewrite (about_execute_byte_code_program 
               execute_byte_code_program 
               execute_byte_code_program_satisfies_the_specification 
               (compile ae1) 
               (compile ae2 ++ ADD :: nil) 
               s).
      rewrite IHae1.
      rewrite (about_execute_byte_code_program 
               execute_byte_code_program 
               execute_byte_code_program_satisfies_the_specification 
               (compile ae2) 
               (ADD :: nil) 
               (interpreter ae1 :: s)).
      rewrite IHae2.
      rewrite (unfold_execute_byte_code_program_ic ADD nil (interpreter ae2 :: interpreter ae1 :: s)).
      rewrite unfold_execute_byte_code_program_bc.
      unfold execute_byte_code_instruction_v0.
      rewrite (unfold_execute_byte_code_instruction_add (interpreter ae2 :: interpreter ae1 :: s)).
      rewrite unfold_interpreter_plus.
      reflexivity.

    rewrite (unfold_compile_times ae1' ae2').
    intro s.
    rewrite (about_execute_byte_code_program 
             execute_byte_code_program 
             execute_byte_code_program_satisfies_the_specification 
             (compile ae1') 
             (compile ae2' ++ MUL :: nil) 
             s).
    rewrite IHae1'.
    rewrite (about_execute_byte_code_program 
             execute_byte_code_program 
             execute_byte_code_program_satisfies_the_specification 
             (compile ae2') 
             (MUL :: nil) 
             (interpreter ae1' :: s)).
    rewrite IHae2'.
    rewrite (unfold_execute_byte_code_program_ic MUL nil (interpreter ae2' :: interpreter ae1' :: s)).
    rewrite unfold_execute_byte_code_program_bc.
    unfold execute_byte_code_instruction_v0.
    rewrite (unfold_execute_byte_code_instruction_mul (interpreter ae2' :: interpreter ae1' :: s)).
    rewrite unfold_interpreter_times.
    reflexivity.

  rewrite (unfold_compile_minus ae1'' ae2'').
  intro s.
  rewrite (about_execute_byte_code_program 
           execute_byte_code_program 
           execute_byte_code_program_satisfies_the_specification 
           (compile ae1'') 
           (compile ae2'' ++ SUB :: nil) 
           s).
  rewrite IHae1''.
  rewrite (about_execute_byte_code_program execute_byte_code_program execute_byte_code_program_satisfies_the_specification (compile ae2'') (SUB :: nil) (interpreter ae1'' :: s)).
  rewrite IHae2''.
  rewrite (unfold_execute_byte_code_program_ic SUB nil (interpreter ae2'' :: interpreter ae1'' :: s)).
  rewrite unfold_execute_byte_code_program_bc.
  unfold execute_byte_code_instruction_v0.
  rewrite (unfold_execute_byte_code_instruction_sub (interpreter ae2'' :: interpreter ae1'' :: s)).
  rewrite unfold_interpreter_minus.
  reflexivity.
Qed.

Theorem interpret_equals_compile_and_run :
  forall (ae : arithmetic_expression),
    run (compile_v0 ae)  = interpreter_v0 ae.
Proof.
  intros ae .
  unfold run.
  rewrite -> (interpret_equals_compile_and_execute ae).
  reflexivity.
Qed.

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

Definition ae_data_stack := list arithmetic_expression.

Definition specification_of_magritte_execute_instr (mag_execute : byte_code_instruction -> ae_data_stack -> ae_data_stack) :=
  (forall (n : nat) (s : ae_data_stack),
     mag_execute (PUSH n) s = ((Lit n) :: s))
  /\
  (forall (ae1 ae2 : arithmetic_expression) (s : ae_data_stack),
     mag_execute ADD s = match s with
                       | (ae1 :: ae2 :: s) => (Plus ae2 ae1 :: s)
                       | (ae1 :: nil) => (Plus (Lit 0) ae1 :: nil)
                       | (nil) => ((Plus (Lit 0) (Lit 0)) :: nil)
                     end)
  /\
  (forall (ae1 ae2 : arithmetic_expression) (s : ae_data_stack),
     mag_execute MUL s = match s with
                       | (ae1 :: ae2 :: s) => (Times ae2 ae1 :: s)
                       | (ae1 :: nil) => (Times (Lit 0) ae1 :: nil)
                       | (nil) => (Times (Lit 0) (Lit 0) :: nil)
                     end)
  /\
  (forall (ae1 ae2 : arithmetic_expression) (s : ae_data_stack),
     mag_execute SUB s = match s with
                       | (ae1 :: ae2 :: s) => (Minus ae2 ae1 :: s)
                       | (ae1 :: nil) => (Minus (Lit 0) ae1 :: s)
                       | (nil) => (Minus (Lit 0) (Lit 0) :: nil)
                     end).

Fixpoint beq_ae (x y : arithmetic_expression) : bool :=
  match x with
    | Lit n => match y with
                  | Lit m => (beq_nat n m)
                  | _ => false
                end
    | Plus ae1 ae2 => match y with
               | Plus ae1' ae2' => (beq_ae ae1 ae1') && (beq_ae ae2 ae2')
               | _ => false
             end
    | Times ae1 ae2 => match y with
               | Times ae1' ae2' => (beq_ae ae1 ae1') && (beq_ae ae2 ae2')
               | _ => false
             end
    | Minus ae1 ae2 => match y with
               | Minus ae1' ae2' => (beq_ae ae1 ae1') && (beq_ae ae2 ae2')
               | _ => false
             end
  end.

Definition beq_aes (xs ys : ae_data_stack) : bool :=
  beq_list arithmetic_expression beq_ae xs ys.

Notation "A =bcp= B" := (beq_aes A B) (at level 70, right associativity).

Definition unit_tests_for_magritte_instr (mag_execute : byte_code_instruction -> ae_data_stack -> ae_data_stack) :=
   ((mag_execute ADD nil) =bcp= (Plus (Lit 0) (Lit 0)) :: nil)
   &&
   ((mag_execute (PUSH 5) nil) =bcp= (Lit 5:: nil))
   &&
   ((mag_execute MUL nil) =bcp= (Times (Lit 0) (Lit 0)) :: nil)
   &&
   ((mag_execute SUB nil) =bcp= (Minus (Lit 0) (Lit 0)) :: nil).

Proposition there_is_only_one_specification_of_magritte_execute_instr :
  forall f g : byte_code_instruction -> ae_data_stack -> ae_data_stack,
    specification_of_magritte_execute_instr f ->
    specification_of_magritte_execute_instr g ->
    forall (instr : byte_code_instruction) (s : ae_data_stack),
      f instr s = g instr s.
Proof.
  intros f g.
  unfold specification_of_magritte_execute_instr.
  intros [S_f_push [S_f_add [S_f_mul S_f_sub]]].
  intros [S_g_push [S_g_add [S_g_mul S_g_sub]]].
  intros instr s.
  assert (a := (Lit 0)).
  induction instr as [ | i1 IHi1 i2 IHi2 | i1' IHi1' i2' IHi2' | i1'' IHi1'' i2'' IHi2'' ].
        rewrite S_g_push.
        exact (S_f_push n s).

      rewrite (S_g_add a a s).
      exact (S_f_add a a s).

    rewrite (S_g_mul a a s).
    exact (S_f_mul a a s).

  rewrite (S_g_sub a a s).
  exact (S_f_sub a a s).
Qed.  

Definition magritte_execute_instr (instr : byte_code_instruction) (s : ae_data_stack) : ae_data_stack :=
  match instr with
    | (PUSH n) => ((Lit n) :: s)
    | ADD => match s with
               | (ae1 :: ae2 :: s) => (Plus ae2 ae1 :: s)
               | (ae1 :: nil) => (Plus (Lit 0) ae1 :: nil)
               | (nil) => ((Plus (Lit 0) (Lit 0)) :: nil)
             end
    | MUL => match s with
               | (ae1 :: ae2 :: s) => (Times ae2 ae1 :: s)
               | (ae1 :: nil) => (Times (Lit 0) ae1 :: nil)
               | (nil) => (Times (Lit 0) (Lit 0) :: nil)
             end
    | SUB => match s with
               | (ae1 :: ae2 :: s) => (Minus ae2 ae1 :: s)
               | (ae1 :: nil) => (Minus (Lit 0) ae1 :: s)
               | (nil) => (Minus (Lit 0) (Lit 0) :: nil)
             end
  end.


Lemma unfold_mag_execute_push :
  forall (n : nat) (s : ae_data_stack),
    magritte_execute_instr (PUSH n) s = ((Lit n) :: s).
Proof.
  unfold_tactic magritte_execute_instr.
Qed.

Lemma unfold_mag_execute_add :
  forall (s : ae_data_stack),
    magritte_execute_instr ADD s = match s with
                                     | (ae1 :: ae2 :: s) => (Plus ae2 ae1 :: s)
                                     | (ae1 :: nil) => (Plus (Lit 0) ae1 :: nil)
                                     | (nil) => ((Plus (Lit 0) (Lit 0)) :: nil)
                                   end.
Proof.
  unfold_tactic magritte_execute_instr.
Qed.

Lemma unfold_mag_execute_mul :
  forall (s : ae_data_stack),
    magritte_execute_instr MUL s = match s with
                                     | (ae1 :: ae2 :: s) => (Times ae2 ae1 :: s)
                                     | (ae1 :: nil) => (Times (Lit 0) ae1 :: nil)
                                     | (nil) => (Times (Lit 0) (Lit 0) :: nil)
                                   end.
Proof.
  unfold_tactic magritte_execute_instr.
Qed.

Lemma unfold_mag_execute_sub :
  forall (s : ae_data_stack),
    magritte_execute_instr SUB s = match s with
                                     | (ae1 :: ae2 :: s) => (Minus ae2 ae1 :: s)
                                     | (ae1 :: nil) => (Minus (Lit 0) ae1 :: s)
                                     | (nil) => (Minus (Lit 0) (Lit 0) :: nil)
                                   end.
Proof.
  unfold_tactic magritte_execute_instr.
Qed.

Definition magritte_execute_instr_v0 (instr : byte_code_instruction) (s : ae_data_stack) : ae_data_stack :=
  magritte_execute_instr instr s.

Compute unit_tests_for_magritte_instr magritte_execute_instr_v0.

Proposition magritte_execute_instr_v0_fits_the_specification_of_magritte_execute_instr :
  specification_of_magritte_execute_instr magritte_execute_instr_v0.
Proof.
  unfold specification_of_magritte_execute_instr.
  split.
    exact unfold_mag_execute_push.
  
  split.
    intros ae1 ae2.
    exact unfold_mag_execute_add.

  split.
    intros ae1 ae2.
    exact unfold_mag_execute_mul.

  intros ae1 ae2.
  exact unfold_mag_execute_sub.
Qed.

  
Definition specification_of_magritte_execute (mag_execute : byte_code_program -> ae_data_stack -> ae_data_stack) :=
  (forall (s : ae_data_stack),
     mag_execute nil s = s)
  /\
  (forall (instr : byte_code_instruction) (prog : byte_code_program) (s : ae_data_stack),
     mag_execute (instr :: prog) s = (mag_execute prog (magritte_execute_instr_v0 instr s))).

Definition unit_tests_for_magritte_execute (mag_execute : byte_code_program -> ae_data_stack -> ae_data_stack) :=
   ((mag_execute (PUSH 5 :: nil) nil) =bcp= (Lit 5 :: nil))
   &&
   ((mag_execute (PUSH 42 :: nil) nil) =bcp= (Lit 42 :: nil))
   &&
   ((mag_execute (PUSH 10 :: PUSH 20 :: ADD :: nil) nil) =bcp= (ae_1 :: nil))
   &&
   ((mag_execute (PUSH 10 :: PUSH 20 :: ADD :: PUSH 3 :: MUL :: nil) nil) =bcp= (ae_2 :: nil))
   &&
   ((mag_execute (PUSH 30 :: PUSH 10 :: SUB :: nil) nil) =bcp= (ae_3 :: nil)).

Proposition there_is_only_one_magritte_execute :
  forall execute1 execute2 : byte_code_program -> ae_data_stack -> ae_data_stack,
    specification_of_magritte_execute execute1 ->
    specification_of_magritte_execute execute2 ->
    forall (p : byte_code_program) (s : ae_data_stack),
      execute1 p s = execute2 p s.
Proof.
  intros execute1 execute2.
  intros [S_execute1_bc S_execute1_ic] [S_execute2_bc S_execute2_ic].
  intros p.
  induction p as [ | p' ps' IHps'].
    intro s.
    rewrite -> S_execute2_bc.
    apply S_execute1_bc.

  intro s.
  rewrite -> S_execute2_ic.
  rewrite <- IHps'.
  apply S_execute1_ic.
Qed.


Fixpoint magritte_execute_prog (prog : byte_code_program) (s : ae_data_stack) : ae_data_stack :=
  match prog with
    | nil => s
    | (h :: t) => (magritte_execute_prog t (magritte_execute_instr_v0 h s))
  end.

Lemma unfold_magritte_execute_prog_bc :
  forall s : ae_data_stack,
    magritte_execute_prog nil s = s.
Proof.
  unfold_tactic magritte_execute_prog.
Qed.

Lemma unfold_magritte_execute_prog_ic :
  forall (h : byte_code_instruction) (t : byte_code_program) (s : ae_data_stack),
    magritte_execute_prog (h :: t) s = (magritte_execute_prog t (magritte_execute_instr_v0 h s)).
Proof.
  unfold_tactic execute_byte_code_program.
Qed.

Definition magritte_execute_prog_v0 (prog : byte_code_program) (s : ae_data_stack) : ae_data_stack :=
  magritte_execute_prog prog s.

Compute unit_tests_for_magritte_execute magritte_execute_prog_v0.

Proposition magritte_execute_prog_v0_satisfies_the_specification :
  specification_of_magritte_execute magritte_execute_prog_v0.
Proof.
  unfold specification_of_magritte_execute.
  unfold magritte_execute_prog_v0.
  split.
    exact unfold_magritte_execute_prog_bc.

  exact unfold_magritte_execute_prog_ic.
Qed.


(* Exercise 10:
   Prove that the Magrite-style execution function from Exercise 9
   implements a decompiler that is the left inverse of the compiler
   of Exercise 6.
*)

Proposition about_magritte_execute :
  forall (mag_exec : byte_code_program -> ae_data_stack -> ae_data_stack),
    specification_of_magritte_execute mag_exec ->
    forall (p1 p2 : byte_code_program) (s : ae_data_stack),
      mag_exec (p1 ++ p2) s = mag_exec p2 (mag_exec p1 s).
Proof.
  intros mag_exec.
  intros [S_execute_bc S_execute_ic].
  intros p1.
  induction p1 as [ | p1' p1s' IHp1s' ].
    intros p2 s.
    rewrite -> S_execute_bc.
    rewrite -> app_nil_l.
    reflexivity.

  intros p2 s.
  rewrite -> S_execute_ic.
  rewrite <- IHp1s'.
  rewrite <- app_comm_cons.
  rewrite -> S_execute_ic.
  reflexivity.
Qed.

Definition run_magritte (bcp : byte_code_program) : arithmetic_expression :=
  match (magritte_execute_prog_v0 bcp nil) with
    | x :: nil => x
    | _ => (Lit 0)
  end.


Theorem magritte_execute_is_left_inverse_of_compile :
  forall (ae : arithmetic_expression) (s : ae_data_stack),
    magritte_execute_prog_v0 (compile ae) s = ae :: s.
Proof.
  intro ae.
  unfold magritte_execute_prog_v0.
  induction ae as [ | ae1 IHae1 ae2 IHae2 | ae1' IHae1' ae2' IHae2' | ae1'' IHae1'' ae2'' IHae2''].
        intro s.
        rewrite unfold_compile_lit.
        unfold run_magritte.
        rewrite unfold_magritte_execute_prog_ic.
        rewrite unfold_magritte_execute_prog_bc.
        unfold magritte_execute_instr_v0.
        rewrite unfold_mag_execute_push.
        reflexivity.

      rewrite (unfold_compile_plus ae1 ae2).
      intro s.
      rewrite (about_magritte_execute magritte_execute_prog
                                      magritte_execute_prog_v0_satisfies_the_specification
                                      (compile ae1)
                                      (compile ae2 ++ ADD :: nil)
                                      s).
      rewrite IHae1.
      rewrite (about_magritte_execute magritte_execute_prog
                                      magritte_execute_prog_v0_satisfies_the_specification
                                      (compile ae2)
                                      (ADD :: nil)
                                      (ae1 :: s)).
      rewrite IHae2.
      rewrite (unfold_magritte_execute_prog_ic ADD nil (ae2 :: ae1 :: s)).
      rewrite unfold_magritte_execute_prog_bc.
      unfold magritte_execute_instr_v0.
      rewrite (unfold_mag_execute_add (ae2 :: ae1 :: s)).
      reflexivity.

    rewrite (unfold_compile_times ae1' ae2').
    intro s.
    rewrite (about_magritte_execute magritte_execute_prog
                                    magritte_execute_prog_v0_satisfies_the_specification
                                    (compile ae1')
                                    (compile ae2' ++ MUL :: nil)
                                    s).
    rewrite IHae1'.
    rewrite (about_magritte_execute magritte_execute_prog
                                    magritte_execute_prog_v0_satisfies_the_specification
                                    (compile ae2')
                                    (MUL :: nil)
                                    (ae1' :: s)).
    rewrite IHae2'.
    rewrite (unfold_magritte_execute_prog_ic MUL nil (ae2' :: ae1' :: s)).
    rewrite unfold_magritte_execute_prog_bc.
    unfold magritte_execute_instr_v0.
    rewrite (unfold_mag_execute_mul (ae2' :: ae1' :: s)).
    reflexivity.

  rewrite (unfold_compile_minus ae1'' ae2'').
  intro s.
  rewrite (about_magritte_execute magritte_execute_prog
                                  magritte_execute_prog_v0_satisfies_the_specification
                                  (compile ae1'')
                                  (compile ae2'' ++ SUB :: nil)
                                  s).
  rewrite IHae1''.
  rewrite (about_magritte_execute magritte_execute_prog
                                  magritte_execute_prog_v0_satisfies_the_specification
                                  (compile ae2'')
                                  (SUB :: nil)
                                  (ae1'' :: s)).
  rewrite IHae2''.
  rewrite (unfold_magritte_execute_prog_ic SUB nil (ae2'' :: ae1'' :: s)).
  rewrite unfold_magritte_execute_prog_bc.
  unfold magritte_execute_instr_v0.
  rewrite (unfold_mag_execute_sub (ae2'' :: ae1'' :: s)).
  reflexivity.
Qed.

(* ********** *)

(* end of week_39b_arithmetic_expressions.v *)
