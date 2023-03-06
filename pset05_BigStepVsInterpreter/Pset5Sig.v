(** * 6.512 Formal Reasoning About Programs, Spring 2023 - Pset 4 *)

Require Coq816.
Require Import Frap.Frap.

Module Type S.
  Inductive arith : Set :=
  | Const (n: nat)
  | Var (x: var)
  | Plus (e1 e2: arith).

  Inductive cmd :=
  | Skip
  | Assign (x: var) (e: arith)
  | Sequence (c1 c2: cmd)
  | If (e: arith) (thn els: cmd)
  | While (e: arith) (body: cmd).

  Definition valuation := fmap var nat.

  Fixpoint interp (e: arith) (v: valuation) (a: nat): Prop :=
    match e with
    | Const n => a = n
    | Var x =>
      match v $? x with
      | None => True (* any a is possible! *)
      | Some n => a = n
      end
    | Plus e1 e2 => exists a1 a2, interp e1 v a1 /\ interp e2 v a2 /\ a = a1 + a2
    end.

  (*[4%]*)
  Parameter values_alias_for_grading: arith -> valuation -> nat -> Prop.

  (*[1%]*)
  Parameter values_example: forall a,
      2 <= a ->
      values_alias_for_grading (Plus (Var "y") (Var "z")) ($0 $+ ("y", 2)) a.

  (*[4%]*)
  Parameter interp_to_values: forall e v a,
      interp e v a -> values_alias_for_grading e v a.

  (*[4%]*)
  Parameter values_to_interp: forall e v a,
      values_alias_for_grading e v a -> interp e v a.

  (*[2%]*)
  Parameter values_to_interp_induction_on_e: forall e v a,
      values_alias_for_grading e v a -> interp e v a.

  (*[7%]*)
  Parameter eval_alias_for_grading: valuation -> cmd -> valuation -> Prop.

  Example the_answer_is_42 :=
    Sequence (Assign "x" (Var "oops"))
             (Sequence (If (Var "x")
                           (Assign "tmp" (Plus (Var "x") (Var "x")))
                           (Assign "tmp" (Const 1)))
                       (If (Var "tmp")
                           (Assign "answer" (Const 42))
                           (Assign "answer" (Const 24)))).

  (*[1%]*)
  Parameter read_last_value: forall x v c n,
      values_alias_for_grading (Var x) (v $+ (x, c)) n -> n = c.

  (*[7%]*)
  Parameter the_answer_is_indeed_42:
    forall v, eval_alias_for_grading $0 the_answer_is_42 v -> v $? "answer" = Some 42.

  Example loop_of_unknown_length :=
    (While (Var "x") (Assign "counter" (Plus (Var "counter") (Const 1)))).

  (*[7%]*)
  Parameter eval_loop_of_unknown_length: forall n initialCounter,
      eval_alias_for_grading ($0 $+ ("counter", initialCounter))
                             loop_of_unknown_length
                             ($0 $+ ("counter", initialCounter + n)).

  (*[4%]*)
  Parameter run: nat -> valuation -> cmd -> valuation -> Prop.

  (*[14%]*)
  Parameter run_to_eval: forall fuel v1 c v2,
      run fuel v1 c v2 ->
      eval_alias_for_grading v1 c v2.

  Definition wrun (v1: valuation) (c: cmd) (v2: valuation): Prop :=
    exists fuel, run fuel v1 c v2.

  (*[17%]*)
  Parameter run_monotone: forall fuel1 fuel2 v1 c v2,
      fuel1 <= fuel2 ->
      run fuel1 v1 c v2 ->
      run fuel2 v1 c v2.

  (*[1%]*)
  Parameter WRunSkip: forall v,
      wrun v Skip v.

  (*[2%]*)
  Parameter WRunAssign: forall v x e a,
      interp e v a ->
      wrun v (Assign x e) (v $+ (x, a)).

  (*[2%]*)
  Parameter WRunSeq: forall v c1 v1 c2 v2,
      wrun v c1 v1 ->
      wrun v1 c2 v2 ->
      wrun v (Sequence c1 c2) v2.

  (* [1%] *)
  Parameter WRunIfTrue_statement: Prop.
  (* [2%] *)
  Parameter WRunIfTrue:  WRunIfTrue_statement.

  (* [1%] *)
  Parameter WRunIfFalse_statement: Prop.
  (* [2%] *)
  Parameter WRunIfFalse:  WRunIfFalse_statement.

  (* [1%] *)
  Parameter WRunWhileTrue_statement: Prop.
  (* [3%] *)
  Parameter WRunWhileTrue:  WRunWhileTrue_statement.

  (* [1%] *)
  Parameter WRunWhileFalse_statement: Prop.
  (* [2%] *)
  Parameter WRunWhileFalse:  WRunWhileFalse_statement.

  (*[10%]*)
  Parameter eval_to_wrun: forall v1 c v2,
      eval_alias_for_grading v1 c v2 ->
      wrun v1 c v2.
End S.
