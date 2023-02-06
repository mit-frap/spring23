(** * 6.512 Formal Reasoning About Programs, Spring 2023 - Pset 1 *)

(* Welcome to the wonderful world of Coq programming! *)

(* This pset dives straight in to building a program-analysis pass and
 * proving it sound in Coq. But before that, you will need to get set up
 * with Coq. *)

(*
 * Start by installing the Coq system by following the isntructions on the Coq
 * website at <https://coq.inria.fr/download>. For this class, you must use 
 * version 8.16 (the latest).
 *
 * You may also install it from your operating system/package manager's
 * repositories (`pacman -S coq`, `brew install coq`, etc.), but note that 
 * Ubuntu's `apt` package manager does not have the most recent version,
 * so Ubuntu users should use the `snap` package by running the command
 * `snap install coq-prover` as per the instructions on the download page.
 *
 * Run `coqc -v` to check that the right version was installed.
 *
 * It will also be *essential* to install a UI for editing Coq proofs!  The most
 * popular Coq IDE in the research world, which the course staff use and
 * recommend, is the venerable Proof General <https://proofgeneral.github.io/>,
 * a package for the Emacs IDE, which can optionally be extended with
 * company-coq <https://github.com/cpitclaudel/company-coq/>.
 *
 * If you're not ready to take the Emacs plunge (but it's worth it! We
 * promise!), then install one of the alternatives listed on the Coq website at
 * <https://coq.inria.fr/user-interfaces.html>.  The one called “CoqIDE” has
 * the least steep learning curve, but Proof General will make you significantly
 * more productive after spending some practice time.
 *
 * We will have special office hours the first week of class,
 * to help everyone get these packages set up.
 *
 * Now, on to the actual assignment, once you have Coq and a UI installed!  This
 * course uses a special Coq library, so we'll start by compiling that:
 *
 * Run `make -C frap lib` in the root directory of your 6.512 git clone.
 *)

Require Coq816.
(* If this import command doesn't work, you have installed an outdated version of
 * Coq. Make sure to follow the instructions at <https://coq.inria.fr/download>
 * and consult the TA if you need help.
 *)

Require Import Frap.
(* If this import command doesn't work, something may be wrong with the copy
 * of the FRAP book source that has been included as a Git submodule.
 * Running `git submodule init' or `git submodule update' in the repository
 * base directory (followed by rerunning `make -C frap lib` here) might help.
 *)

(* Throughout this assignment, if you find yourself running into trouble using
 * Coq or structuring proofs, we recommend reading the tips section found near the
 * end of this file. It's a brief collection of useful tips and tricks that you
 * might find useful--even beyond this pset!
 *
 * If you find yourself stuck specifically on solving a pset problem in terms
 * of defining a construct or formulating/proving a predicate, we've provided
 * a set of hints beneath the tips section at the end of this file. We recommend
 * trying to solve these problems on your own before consulting these hints!
 *)

(* The first part of this assignment involves the [bool] datatype,
 * which has the following definition.
 * <<
     Inductive bool :=
     | true
     | false.
   >>
 * We will define logical negation and conjunction of Boolean values,
 * and we will prove some properties of these definitions.

 * In the second part of this assignment, we will work with a simple language
 * of imperative arithmetic programs that sequentially apply operations
 * to a natural-number-valued state.

 * The file that you are currently reading contains only the *signature* of the
 * programs that we will implement: the module type `S` below defines the
 * interface of the code.

 * Your job is to write a module implementing this interface by fleshing out the
 * skeleton given in the file `Pset1Implementation.v`.  For the last problem, we
 * also ask you to give an informal explanation of the proof in addition to the
 * Coq proof script.
 *
 * Your `Pset1Implementation.v` file is what you upload to the course web site
 * to get credit for doing the assignment.  A line at the end of
 * `Pset1Implementation.v` (`Module Impl := …`) checks that your code conforms
 * to the expected signature.  Make sure that the file that you submit can be
 * compiled and checked: use `Admitted` if you're not sure how to complete a
 * proof.
 *
 * Percentages in square brackets below show the approximate rubric that we will
 * apply.
 *)

(*
 * First, here's the [Prog] datatype that defines abstract syntax trees for this
 * pset's language.
 *)

Inductive Prog :=
  | Done                             (* Don't modify the state. *)
  | AddThen (n : nat) (p : Prog)     (* Add [n] to the state, then run [p]. *)
  | MulThen (n : nat) (p : Prog)     (* Multiply the state by [n], then run [p]. *)
  | DivThen (n : nat) (p : Prog)     (* Divide the state by [n], then run [p]. *)
  | VidThen (n : nat) (p : Prog)     (* Divide [n] by the state, then run [p]. *)
  | SetToThen (n : nat) (p : Prog)   (* Set the state to [n], then run [p]. *)
  .

(* Then, here's the actual signature to implement. *)

Module Type S.

  (* Define [Neg] so that it implements Boolean negation, which flips
   * the truth value of a Boolean value.
   *)
  (*[2%]*) Parameter Neg : bool -> bool.

  (* For instance, the negation of [true] should be [false].
   * This proof should follow from reducing both sides of the equation
   * and observing that they are identical.
   *)
  (*[1%]*) Axiom Neg_true : Neg true = false.

  (* Negation should be involutive, meaning that if we negate
   * any Boolean value twice, we should get the original value back.

   * To prove a fact like this that holds for all Booleans, it suffices
   * to prove the fact for both [true] and [false] by using the
   * [cases] tactic.
   *)
  (*[4%]*) Axiom Neg_involutive : forall b : bool, Neg (Neg b) = b.

  (* Define [And] so that it implements Boolean conjunction. That is,
   * the result value should be [true] exactly when both inputs
   * are [true].
   *)
  (*[3%]*) Parameter And : bool -> bool -> bool.

  (* Here are a couple of examples of how [And] should act on
   * concrete inputs.
   *)
  (*[1%]*) Axiom And_true_true : And true true = true.
  (*[1%]*) Axiom And_false_true : And false true = false.

  (* Prove that [And] is commutative, meaning that switching the order
   * of its arguments doesn't affect the result.
   *)
  (*[4%]*) Axiom And_comm : forall x y : bool, And x y = And y x.

  (* Prove that the conjunction of a Boolean value with [true]
   * doesn't change that value.
   *)
  (*[4%]*) Axiom And_true_r : forall x : bool, And x true = x.


  (* Define [run] such that [run p n] gives the final state
   * that running the program [p] should result in, when the
   * initial state is [n].
   * Use the +, *, and / operators for natural numbers provided
   * by the Coq standard library, and for this part of the
   * exercise, don't worry about division by 0; doing the same
   * thing as division from the standard library does is fine.
   *)
  (*[3%]*) Parameter run : Prog -> nat -> nat.

  (*[1%]*) Axiom run_Example1 : run Done 0 = 0.
  (*[1%]*) Axiom run_Example2 : run (MulThen 5 (AddThen 2 Done)) 1 = 7.
  (*[1%]*) Axiom run_Example3 : run (SetToThen 3 (MulThen 2 Done)) 10 = 6.

  (* Define [numInstructions] to compute the number of instructions
   * in a program, not counting [Done] as an instruction.
   *)
  (*[3%]*) Parameter numInstructions : Prog -> nat.

  (*[1%]*) Axiom numInstructions_Example :
    numInstructions (MulThen 5 (AddThen 2 Done)) = 2.

  (* Define [concatProg] such that [concatProg p1 p2] is the program
   * that first runs [p1] and then runs [p2].
   *)
  (*[3%]*) Parameter concatProg : Prog -> Prog -> Prog.

  (*[1%]*) Axiom concatProg_Example :
     concatProg (AddThen 1 Done) (MulThen 2 Done)
   = AddThen 1 (MulThen 2 Done).

  (* Prove that the number of instructions in the concatenation of
   * two programs is the sum of the number of instructions in each
   * program.
   *)
  (*[8%]*) Axiom concatProg_numInstructions : forall p1 p2,
      numInstructions (concatProg p1 p2)
      = numInstructions p1 + numInstructions p2.

  (* Prove that running the concatenation of [p1] with [p2] is
     equivalent to running [p1] and then running [p2] on the
     result. *)
  (*[8%]*) Axiom concatProg_run : forall p1 p2 initState,
      run (concatProg p1 p2) initState =
      run p2 (run p1 initState).

  (* As there is no intuitive or broadly useful definition for x/0,
     common processors handle it differently. We would like to model the
     portable behavior of a program, that is, its behavior to the extent
     it is known without relying on arbitrary choices about division by
     zero. The following interpreter returns (b, s), where the Boolean [b]
     indicates whether the execution completed without division by
     zero, and if it did, then [s] is the final state. First, you will be
     asked to prove that [s] matches [run] in those cases. *)
  Fixpoint runPortable (p : Prog) (state : nat) : bool * nat :=
    match p with
    | Done => (true, state)
    | AddThen n p => runPortable p (n+state)
    | MulThen n p => runPortable p (n*state)
    | DivThen n p =>
        if n ==n 0 then (false, state) else
        runPortable p (state/n)
    | VidThen n p =>
        if state ==n 0 then (false, 0) else
        runPortable p (n/state)
    | SetToThen n p =>
        runPortable p n
    end.

  (*[8%]*) Axiom runPortable_run : forall p s0 s1,
    runPortable p s0 = (true, s1) -> run p s0 = s1.

  (* Static analysis to validate that a program never divides by 0 *)

  (* The final goal of this pset is to implement [validate : Prog -> bool] 
   * Note that this problem is harder than the previous ones and will take 
   * more time! 
   *)
  (*[5%]*) Parameter validate : Prog -> bool.
  (* such that if this function returns [true], the program would not trigger
     division by zero regardless of what state it starts out in.  [validate] is
     allowed to return [false] for some perfectly good programs that never cause
     a division by zero, but it must recognize as good the examples given below.
     In jargon, [validate] is required to be sound but not complete, but
     "complete enough" for the use cases defined by the examples given here.
     We also ask you to define one additional negative test and prove that
     [validate] correctly flags it. *)

  Definition goodProgram1 := AddThen 1 (VidThen 10 Done).
  Definition goodProgram2 := AddThen 0 (MulThen 10 (AddThen 0 (DivThen 1 Done))).
  Definition goodProgram3 := AddThen 1 (MulThen 10 (AddThen 0 (VidThen 1 Done))).
  Definition goodProgram4 := Done.
  Definition goodProgram5 := SetToThen 0 (DivThen 1 Done).
  Definition goodProgram6 := SetToThen 1 (VidThen 1 Done).
  Definition goodProgram7 := AddThen 1 (DivThen 1 (DivThen 1 (VidThen 1 Done))).
  (*[0.5%]*) Axiom validate1 : validate goodProgram1 = true.
  (*[0.5%]*) Axiom validate2 : validate goodProgram2 = true.
  (*[0.5%]*) Axiom validate3 : validate goodProgram3 = true.
  (*[0.5%]*) Axiom validate4 : validate goodProgram4 = true.
  (*[0.5%]*) Axiom validate5 : validate goodProgram5 = true.
  (*[0.5%]*) Axiom validate6 : validate goodProgram6 = true.
  (*[0.5%]*) Axiom validate7 : validate goodProgram7 = true.

  Definition badProgram1 := AddThen 0 (VidThen 10 Done).
  Definition badProgram2 := AddThen 1 (DivThen 0 Done).
  (*[0.5%]*) Axiom validateb1 : validate badProgram1 = false.
  (*[0.5%]*) Axiom validateb2 : validate badProgram2 = false.

  (*[1.5%]*) Parameter badProgram3 : Prog.
  (*[1%]*) Axiom validateb3 : validate badProgram3 = false.

  (*[10%]*) (* Informal proof sketch for `validate_sound`. *)
  (* Before diving into the Coq proof, try to convince yourself that your code
   * is correct by applying induction by hand.  Can you describe the high-level
   * structure of the proof?  Which cases will you have to reason about?  What
   * do the induction hypotheses look like?  Which key lemmas do you need?
   * Write a short (~10-20 lines) informal proof sketch before proceeding. *)

  (*[20%]*) Axiom validate_sound : forall p, validate p = true ->
    forall s, runPortable p s = (true, run p s).
End S.

  
(*|
TIPS: A few things to keep in mind as you work through pset 1
=============================================================
|*)

Require Import Frap.

(*|
Coq resources
-------------

- Start by looking for examples in the course textbook, including the tactic appendix at the end of the book.

- For help on standard Coq tactics, consult Coq's reference manual (https://coq.inria.fr/distrib/current/refman/), starting from the indices at https://coq.inria.fr/distrib/current/refman/appendix/indexes/index.html.  The manual can be overwhelming, so it's best used for looking up fine details.

Useful commands
---------------

Coq comes with many predefined types, functions, and theorems (“objects”).  The most important commands to help you discover them are `Check`, `About`, `Print`, `Search`, and `Compute`.  Try the following examples:

`Check` gives the type of any term, even with holes:
|*)

Check (1 + _).
Check (fun b => match b with true => 0 | false => 1 end).

(*|
`About` gives general information about an object:
|*)

About bool.
About nat.

(*|
`Print` displays the definition of an object:
|*)

Print bool.
Print Nat.add.

(*|
`Search` finds objects.  Its syntax is very flexible:
|*)

(* Find functions of type [nat -> nat -> bool]. *)
Search (nat -> nat -> bool).
(* Find theorems about "+". *)
Search "+".
(* Find theorems whose statement mentions S and eq. *)
Search eq S.
(* Search for a lemma proving the symmetry of eq. *)
Search (?x = ?y -> ?y = ?x).

(*|
If you are puzzled by a notation, the `Locate` command can help:
|*)

Locate "*".

(*|
To evaluate an expression, use `Compute`:
|*)

Compute (2 * 3, 4 + 4, 0 - 2 + 2, pred (S (S (S 0)))).

(*|
Syntax recap
------------

To define a function inline, use `fun`:
|*)

Check (fun x => x + 1).
Check (fun x: bool => xorb x x).

(*|
To perform a case analysis on a value, use `match`:
|*)

Check (fun b (x y: nat) =>
         match b with
         | true => x
         | false => y
         end).

Check (fun (n: nat) =>
         match n with
         | 0 => 1
         | S n => n
         end).

(*|
In Coq, `if` is just short for `match`:
|*)

Check (fun (b: bool) (x y: nat) =>
         if b then x else y).

(*|
To define a global object, use `Definition` or `Lemma` (`Theorem` is an alias of `Lemma`):
|*)

Definition choose (b: bool) (x y: nat) :=
  if b then x else y.

Compute (choose true 6 512).

Lemma plus_commutes :
  forall x, x = x + 0 + 0.
Proof.
  intros.
  Search (_ + 0).
  rewrite <- plus_n_O.
  rewrite <- plus_n_O.
  equality.
Qed.

(*|
Recursive functions use the keyword `Fixpoint`:
|*)

Fixpoint do_n_times (ntimes: nat) (step: nat -> nat) (start_from: nat) :=
  match ntimes with
  | 0 => start_from
  | S ntimes' => step (do_n_times ntimes' step start_from)
  end.

Compute (6, do_n_times 12 (fun x => x + 65) 42).

(*|
You can use bullets or braces to structure your proofs:
|*)

Lemma both_zero:
  forall x y z: nat, x + y + z = 0 -> x = 0 /\ y = 0 /\ z = 0.
Proof.
  intros x.
  cases x.
  - intros.
    cases y.
    + propositional.
    + simplify.
      invert H.
  - intros y z Heq.
    simplify.
    invert Heq.
Qed.

(*|
A few gotchas
-------------

Natural numbers saturate at 0:
|*)

Compute (3 - 5 + 3).

(*|
The order in which you perform induction on variables matters: if `x` comes before `y` and you induct on `y`, your induction hypothesis will not be general enough.
|*)

Lemma add_comm:
  forall x y: nat, x + y = y + x.
Proof.
  induct y.
  - induct x; simplify; equality.
  - simplify.
    (* `IHy` is valid only for one specific `y` *)
Abort.

Lemma add_comm:
  forall x y: nat, x + y = y + x.
Proof.
  induct x.
  - induct y; simplify; equality.
  - simplify.
    (* `IHx` starts with `forall y`. *)
Abort.

(*|
Here's an example where this subtlety matters:
|*)

Fixpoint factorial (n: nat) :=
  match n with
  | O => 1
  | S n' => n * factorial n'
  end.

Fixpoint factorial_acc (n: nat) (acc: nat) :=
  match n with
  | O => acc
  | S n' => factorial_acc n' (n * acc)
  end.

(*|
First attempt, but our lemma is too weak.
|*)

Lemma factorial_acc_correct:
  forall n, factorial n = factorial_acc n 1.
Proof.
  induct n.
  - equality.
  - simplify.
    Search (_ * 1).
    rewrite Nat.mul_1_r.

(*|
Stuck!  We have no way to simplify `factorial_acc n (S n)`.
|*)

Abort.

(*|
Second attempt: a generalized lemma, but we put the `acc` first, so induction will not generalize it.
|*)

Lemma factorial_acc_correct:
  forall acc n, factorial n * acc = factorial_acc n acc.
Proof.
  induct n.
  - simplify.
    Search (_ + 0).
    rewrite Nat.add_0_r.
    equality.
  - simplify.
    Fail rewrite <- IHn.

(*|
Stuck!  IHn is too weak.
|*)

Abort.

(*|
Third time's the charm!  Note how we ordered `n` and `acc`.
|*)

Lemma factorial_acc_correct:
  forall n acc, factorial n * acc = factorial_acc n acc.
Proof.
  induct n.
  - simplify.
    linear_arithmetic.
  - simplify.

(*|
IHn is strong enough now!
|*)

    rewrite <- IHn.
    linear_arithmetic.
Qed.
  

(*|
HINTS: A few hints to help you if you get stuck on certain 
       problems in pset 1.
       Beware! Don't read further if you don't want spoilers!
=============================================================
|*)










































(* HINT 1: *)
(*   Definition validate p := validate' p false. *)
(*   Fixpoint validate' (p : Prog) (nz : bool) : bool. Admitted. *)
        (* if [nz=true], [validate'] can assume that the [state] on which
           [p] will be run is nonzero. When calling [validate']
           recursively, take care to pass in [nz] that corresponds to the
           state after the current operation. *)




























(* HINT 2: some lemmas about arithmetic on natural numbers
   are necessary to prove the soundness of this validator.
   Some of them can be proven inline using [linear_arithmetic].
   The rest that we needed we found from the standard library by using
   [Search]. *)

































(* HINT 3: to prove soundness of [validate'] from hint 1,
    it makes sense to do induction on the input program.
    The key to choosing the predicate [P] is to relate the
    [nz] indicator to the state of a program during a hypothetical
    execution of the program. *)































(* HINT 4: to prove soundness of [validate'] by induction on the
    program, one workable [P] looks like
      Definition P (p : Prog) :=
        forall nz : bool, validate' p nz = true ->
          forall s : nat, (*PRECONDITION ABOUT nz and s HERE*) ->
            runPortable p s = (true, run p s).
    This [P] is inferred by [induct p] from the goal
      forall p nz, validate' p nz = true ->
        forall s, (*PRECONDITION ABOUT nz and s HERE*) ->
          runPortable p s = (true, run p)]. *)
































(* HINT 5: to prove soundness of [validate'] by induction on the
    program and develop a workable [P], consider the two cases in
    executing [validate'] separately. Split the soundness of [validate']
    into the case where the indicator passed into [validate'] is true
    and in the case where it is false.
 *)

































(* HINT 6: to prove soundness of [validate'] by induction on the
    program, one workable [P] is
    forall p,
       (validate' p true = true ->
        forall s, s <> 0 -> runPortable p s = (true, run p s)) /\
       (validate' p false = true ->
        forall s, runPortable p s = (true, run p s)). *)

(* Authors:
 * Peng Wang
 * Adam Chlipala
 * Joonwon Choi
 * Benjamin Sherman
 * Andres Erbsen
 * Clément Pit-Claudel
 * Amanda Liu
 * Dustin Jamner
 *)
