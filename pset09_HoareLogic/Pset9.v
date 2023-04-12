(*|
=============================================================
 6.512 Formal Reasoning About Programs, Spring 2023 - Pset 9
=============================================================
|*)

Require Import Pset9.Pset9Sig.

(*|
Hoare Logic with Input/Output Traces
====================================

Hoare logic as covered in lecture is only the beginning, in terms of programming
features that can be supported. In this problem set, we will use a variant, a
Hoare logic that deals with input/output traces.

This problem set is not about defining a program logic; instead, we'll focus
on proving programs.
|*)

Module Impl.

(*|
Language syntax
===============

There is nothing special with the definitions of `exp` and `bexp`; they are
similar to what we've seen in lecture.
|*)

Inductive nat_op :=
| Plus
| Minus
| Times.

Inductive exp :=
| Const (n : nat)
| Var (x : string)
| Read (e1 : exp)
| NatOp (b: nat_op) (e1 e2 : exp).

Inductive bool_op :=
| Equal
| Less.

Inductive bexp :=
| BoolOp (b: bool_op) (e1 e2 : exp)
| Neg (b: bexp).

(*|
`heap` and `valuation` are also as usual.
|*)

Definition heap := fmap nat nat.
Definition valuation := fmap var nat.

(*|
Besides `heap` and `valuation` objects, we now have `trace` objects.  Traces are
lists of `io` events used to track communication with the outside world.
|*)

Inductive io := In (v : nat) | Out (v : nat).
Definition trace := list io.

(*|
Assertions now talk about traces in addition to internal states.
|*)

Definition assertion := trace -> heap -> valuation -> Prop.

(*|
`cmd` has two new constructors: `Input` and `Output`.
|*)

Inductive cmd :=
| Skip
| Assign (x : var) (e : exp)
| Write (e1 e2 : exp)
| Seq (c1 c2 : cmd)
| If_ (be : bexp) (then_ else_ : cmd)
| While_ (inv : assertion) (be : bexp) (body : cmd)
  (* `Input` takes an input from the external world and assigns
     the value to the local variable `x`. *)
| Input (x : var)
  (* `Output` sends the value of `e` to the outside world. *)
| Output (e : exp).

(* BEGIN NOTATION MAGIC *)
Coercion Const : nat >-> exp.
Coercion Var : string >-> exp.
Declare Scope cmd_scope.
Notation "*[ e ]" := (Read e) : cmd_scope.
Notation "a + b" := (NatOp Plus a b) : cmd_scope.
Notation "a - b" := (NatOp Minus a b) : cmd_scope.
Notation "a * b" := (NatOp Times a b) : cmd_scope.
Notation "a = b" := (BoolOp Equal a b) : cmd_scope.
Notation "a < b" := (BoolOp Less a b) : cmd_scope.
Notation "! e" := (Neg e) (at level 90) : cmd_scope.
Definition set (dst src : exp) : cmd :=
  match dst with
  | Read dst' => Write dst' src
  | Var dst' => Assign dst' src
  | _ => Assign "Bad LHS" 0
  end.
Infix "<-" := set (no associativity, at level 70) : cmd_scope.
Infix ";;" := Seq (right associativity, at level 75) : cmd_scope.
Notation "'when' b 'then' then_ 'else' else_ 'done'" :=
  (If_ b then_ else_) (at level 75, b at level 0) : cmd_scope.
Notation "'when' b 'then' then_ 'done'" :=
  (If_ b then_ Skip) (at level 75, b at level 0) : cmd_scope.
Notation "{{ I }}  'while' b 'loop' body 'done'" := (While_ I%nat%type b body) (at level 75) : cmd_scope.
Notation "x '<--' 'input'" := (Input x) (at level 75) : cmd_scope.
Notation "'output' e" := (Output e) (at level 75) : cmd_scope.
Delimit Scope cmd_scope with cmd.
(* END NOTATION MAGIC *)

(*|
Big-step operational semantics for commands
===========================================

Here is the definition of a big-step operational semantics for commands.  It is
very similar to what we've seen in class, but it also describes how `trace`
objects are accumulated as a program runs.  Note that IO events happen in
reverse chronological order: the most recent IO event appears at the *front* of
the list in the trace.

In the definition of `exec` below, the first three arguments are the trace,
heap, and valuation before execution, and the final three arguments are the
trace, heap, and valuation after execution.
|*)

(* Convenience notation: look up and default to 0 *)
Notation "m $! k" := (match m $? k with Some n => n | None => O end) (at level 30).

Fixpoint eval (e : exp) (h : heap) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x => v $! x
  | Read e1 => h $! eval e1 h v
  | NatOp b e1 e2 =>
    let e1 := eval e1 h v in
    let e2 := eval e2 h v in
    match b with
    | Plus => e1 + e2
    | Minus => e1 - e2
    | Times => e1 * e2
    end
  end.

Fixpoint beval (b : bexp) (h : heap) (v : valuation) : bool :=
  match b with
  | BoolOp b e1 e2 =>
    let e1 := eval e1 h v in
    let e2 := eval e2 h v in
    match b with
    | Equal => if eval e1 h v ==n eval e2 h v then true else false
    | Less => if eval e2 h v <=? eval e1 h v then false else true
    end
  | Neg e => negb (beval e h v)
  end.

Inductive exec : trace -> heap -> valuation -> cmd ->
                 trace -> heap -> valuation -> Prop :=
| ExSkip : forall tr h v,
    exec tr h v Skip tr h v
| ExAssign : forall tr h v x e,
    exec tr h v (Assign x e) tr h (v $+ (x, eval e h v))
| ExWrite : forall tr h v e1 e2,
    exec tr h v (Write e1 e2) tr (h $+ (eval e1 h v, eval e2 h v)) v
| ExSeq : forall tr1 h1 v1 c1 tr2 h2 v2 c2 tr3 h3 v3,
    exec tr1 h1 v1 c1 tr2 h2 v2 ->
    exec tr2 h2 v2 c2 tr3 h3 v3 ->
    exec tr1 h1 v1 (Seq c1 c2) tr3 h3 v3
| ExIfTrue : forall tr1 h1 v1 b c1 c2 tr2 h2 v2,
    beval b h1 v1 = true ->
    exec tr1 h1 v1 c1 tr2 h2 v2 ->
    exec tr1 h1 v1 (If_ b c1 c2) tr2 h2 v2
| ExIfFalse : forall tr1 h1 v1 b c1 c2 tr2 h2 v2,
    beval b h1 v1 = false ->
    exec tr1 h1 v1 c2 tr2 h2 v2 ->
    exec tr1 h1 v1 (If_ b c1 c2) tr2 h2 v2
| ExWhileFalse : forall I tr h v b c,
    beval b h v = false ->
    exec tr h v (While_ I b c) tr h v
| ExWhileTrue : forall I tr1 h1 v1 b c tr2 h2 v2 tr3 h3 v3,
    beval b h1 v1 = true ->
    exec tr1 h1 v1 c tr2 h2 v2 ->
    exec tr2 h2 v2 (While_ I b c) tr3 h3 v3 ->
    exec tr1 h1 v1 (While_ I b c) tr3 h3 v3
| ExInput : forall tr h v x inp,
    exec tr h v (Input x) (In inp :: tr) h (v $+ (x, inp))
| ExOutput : forall tr h v e,
    exec tr h v (Output e) (Out (eval e h v) :: tr) h v.

(*|
Note an interesting property of `ExInput`: it's *nondeterministic*, as we
consider that any `Input` command could read any value.  Without that rule,
our semantics would remain deterministic.

Hoare logic
===========

Up to this point in the class, we've mostly proved properties directly using
operational semantics, but it turns out that using a program logic is usually
much more convenient.

The logic below derives triples of the form `<{ P }> c <{ Q }>`, where `P` and
`Q` have type `assertion` and `c` has type `cmd`. It is also very similar to
the Hoare logic we've defined in class.

For succinctness, we write pre- and postconditions with `fun/inv tr h v => …`,
as an alias for `fun (tr: trace) (h: heap) (v: valuation) => …`

Definition of the logic
-----------------------
|*)

(* Cool Coq trick: forward-declare a notation to use it in a definition. *)
Reserved Notation "<{ P }> c <{ Q }>"
         (at level 90, c at next level,
          format "'[hv' <{  P  }> '/'  c  '/' <{  Q  }> ']'").

Notation "'fun/inv' tr h v => e" :=
  (fun (tr : trace) (h : heap) (v : valuation) => e%nat%type)
    (at level 90, tr name, h name, v name).

Inductive hoare_triple : assertion -> cmd -> assertion -> Prop :=
| HtSkip : forall P, <{ P }> Skip <{ P }>
| HtAssign : forall P x e,
    <{ P }>
    Assign x e
    <{ fun/inv tr h v => exists v', P tr h v' /\ v = v' $+ (x, eval e h v') }>
| HtWrite : forall P (e1 e2 : exp),
    <{ P }>
    Write e1 e2
    <{ fun/inv tr h v =>
         exists h', P tr h' v /\ h = h' $+ (eval e1 h' v, eval e2 h' v) }>
| HtSeq : forall (P Q R : assertion) c1 c2,
    <{ P }> c1 <{ Q }> -> <{ Q }> c2 <{ R }> -> <{ P }> c1;; c2 <{ R }>
| HtIf : forall (P Q1 Q2 : assertion) b c1 c2,
    <{ fun/inv tr h v => P tr h v /\ beval b h v = true }> c1 <{ Q1 }> ->
    <{ fun/inv tr h v => P tr h v /\ beval b h v = false }> c2 <{ Q2 }> ->
    <{ P }> (when b then c1 else c2 done) <{ fun/inv tr h v => Q1 tr h v \/ Q2 tr h v }>
| HtWhile : forall (I P : assertion) b c,
    (forall tr h v, P tr h v -> I tr h v) ->
    <{ fun/inv tr h v => I tr h v /\ beval b h v = true }> c <{ I }> ->
    <{ P }>
    {{ I }} while b loop c done
    <{ fun/inv tr h v => I tr h v /\ beval b h v = false }>
| HtInput : forall (P : assertion) x,
    <{ P }>
    x <-- input
    <{ fun/inv tr h v =>
         exists tr' v' inp, P tr' h v' /\ tr = In inp :: tr' /\ v = v' $+ (x, inp) }>
| HtOutput : forall (P : assertion) e,
    <{ P }>
    output e
    <{ fun/inv tr h v => exists tr', P tr' h v /\ tr = Out (eval e h v) :: tr' }>
| HtConsequence : forall (P Q P' Q' : assertion) c,
    <{ P }> c <{ Q }> ->
    (forall tr h v, P' tr h v -> P tr h v) ->
    (forall tr h v, Q tr h v -> Q' tr h v) ->
    <{ P' }> c <{ Q' }>
where "<{ P }> c <{ Q }>" := (hoare_triple P c%cmd Q).

(*|
Consistency proof
-----------------

This logic is consistent with the semantics we've defined.  The consistency
theorem below will be needed to prove the correctness of our programs.
|*)

Lemma hoare_triple_big_step_while:
  forall I b c,
    (forall tr h v tr' h' v',
        exec tr h v c tr' h' v' ->
        I tr h v /\ beval b h v = true ->
        I tr' h' v') ->
    forall tr h v tr' h' v',
      exec tr h v (While_ I b c) tr' h' v' ->
      I tr h v ->
      I tr' h' v' /\ beval b h' v' = false.
Proof.
  induct 2; eauto.
Qed.

Theorem hoare_triple_big_step :
  forall pre c post,
    hoare_triple pre c post ->
    forall tr h v tr' h' v',
      exec tr h v c tr' h' v' ->
      pre tr h v -> post tr' h' v'.
Proof.
  induct 1; eauto.
  all: invert 1; simplify.
  all: eauto 6 using hoare_triple_big_step_while.
Qed.

(*|
Helper tactics
--------------

Phew, almost done with the setup!  The last step is to define some convenient
tactics for proving programs, which we'll demonstrate by example shortly.
That is, it's not important to understand these tactic definitions.
|*)

Lemma HtStrengthenPost :
  forall (P Q Q' : assertion) c,
    hoare_triple P c Q ->
    (forall tr h v, Q tr h v -> Q' tr h v) ->
    hoare_triple P c Q'.
Proof.
  simplify; eapply HtConsequence; eauto.
Qed.

Ltac cleanup :=
  lazymatch goal with
  | [  |- <{ _ }> _ <{ _ }> ] => fail "Can't clean up a Hoare triple"
  | _ => autounfold with core; cbv beta; first_order; subst; simplify
  end.

Ltac autosolve_t :=
  match goal with
  | [ _ : context[?a <=? ?b] |- _ ] => destruct (a <=? b); try discriminate
  | [ _ : context[?a ==n ?b] |- _ ] => destruct (a ==n b); try discriminate
  | [ H: _ <= 0 |- _ ] => apply Nat.le_0_r in H
  | [ H : ?E = ?E |- _ ] => clear H
  | [ H : ?E <= ?E |- _ ] => clear H
  | _ => progress subst
  end.

Ltac autosolve :=
  repeat autosolve_t; simplify; propositional; eauto 10; try equality; try linear_arithmetic.

Ltac ht1 :=
  lazymatch goal with
  | [  |- <{ _ }> _ <{ ?P }> ] =>
    tryif is_evar P then
      apply HtSkip || apply HtAssign || apply HtWrite || eapply HtSeq
      || eapply HtIf || eapply HtWhile
      || eapply HtInput || eapply HtOutput
    else eapply HtStrengthenPost
  | _ => fail "Goal is not a Hoare triple"
  end.

Ltac ht := simplify; repeat ht1; cleanup; autosolve.

(*|
Hoare-logic-based program proofs
================================

Now it's time to verify programs using the Hoare logic we've just defined!
Your task is to prove the theorems stated below using Hoare logic.  Do *not*
appeal directly to the operational semantics!  Using the Hoare logic is much
more automated and pleasant, and using completely manual derivations with
operational semantics would be particularly unpleasant (especially for the
last problem!).

Here is an example, to help you orient yourself:

First, a program:
|*)

Example add_two_inputs :=
  ("x" <-- input;;
   "y" <-- input;;
   output ("x" + "y"))%cmd.

(*|
Second, its specification and proof.  We'll demonstrate four versions:

- A proof ignoring the Hoare logic (but don't do this!)
- A proof using the Hoare logic by hand (usually not needed)
- A proof using the `ht1` automated tactic (great for debugging)
- A proof using the full `ht` automation (great after trying `ht1` for a bit).

The `ht` tactic is simple but powerful.  In particular, it runs `simplify`
and `eauto`, so you can add new rewritings to it using `Hint Rewrite …` and
new lemmas to it using `Hint Resolve …: core`.
|*)

Lemma add_two_inputs_ok0 :
  forall tr h v tr' h' v',
    exec tr h v add_two_inputs tr' h' v' ->
    tr = nil ->
    exists vx vy, tr' = [Out (vx + vy); In vy; In vx].
Proof.
  simplify.
  unfold add_two_inputs.
  invert H.
  invert H6.
  invert H10.
  invert H4.
  invert H8.
  simplify; subst; eauto.
Qed.

Lemma add_two_inputs_ok1:
  forall tr h v tr' h' v',
    exec tr h v add_two_inputs tr' h' v' ->
    tr = nil ->
    exists vx vy, tr' = [Out (vx + vy); In vy; In vx].
Proof.
  eapply hoare_triple_big_step
    with (pre := fun/inv tr _ _ => tr = nil)
         (post := fun/inv tr _ _ => exists vx vy, tr = [Out (vx + vy); In vy; In vx]).
  eapply HtSeq.
  eapply HtInput.
  eapply HtSeq.
  eapply HtInput.
  eapply HtStrengthenPost.
  eapply HtOutput.
  cleanup.
  autosolve.
Qed.

Lemma add_two_inputs_ok2:
  forall tr h v tr' h' v',
    exec tr h v add_two_inputs tr' h' v' ->
    tr = nil ->
    exists vx vy, tr' = [Out (vx + vy); In vy; In vx].
Proof.
  eapply hoare_triple_big_step.
  ht1.
  ht1.
  ht1.
  ht1.
  ht1.
  ht1.
  cleanup.
  autosolve.
Qed.

Lemma add_two_inputs_ok:
  forall tr h v tr' h' v',
    exec tr h v add_two_inputs tr' h' v' ->
    tr = nil ->
    exists vx vy, tr' = [Out (vx + vy); In vy; In vx].
Proof.
  eapply hoare_triple_big_step; ht.
Qed.

(*|
Notice how we started by applying `hoare_triple_big_step`.  In the following,
we'll give you goals phrased directly in terms of Hoare-logic triples.

Simple programs
===============

Your turn!  The following program finds the maximum of three numbers.  Try to
step through the execution with `ht1` before handing control to `ht`!.
|*)

Example max3 :=
  ("x" <-- input;;
   "y" <-- input;;
   "z" <-- input;;
   when "x" < "y" then
     when "y" < "z" then
       output "z"
     else
       output "y"
     done
   else
     when "x" < "z" then
       output "z"
     else
       output "x"
     done
   done)%cmd.

Definition max3_spec (tr: trace): Prop :=
  exists x y z,
    tr = [Out (max x (max y z)); In z; In y; In x].



Theorem max3_ok:
  <{ fun/inv tr _ _ => tr = [] }>
  max3
  <{ fun/inv tr' _ _ => max3_spec tr' }>.
Proof.
Admitted.

(*|
Euclidian Algorithm for GCD
---------------------------

Our first example with loops involves the classic Euclidean algorithm for 
calculating the greatest common denominator of two natural numbers.

The definition below is parametric in an invariant ‘inv’ — the key part of
your job is to define an ‘inv’ that is correct and strong enough to make the
proof go through.

|*)

Example euclidean_algorithm a b inv :=
  ("a_orig" <- Const a;;
   "b_orig" <- Const b;;

   "a" <- "a_orig";;
   "b" <- "b_orig";;
   
   {{inv}}
   while !"a" = "b" loop
     when "a" < "b"
       then "b" <- "b" - "a" 
       else "a" <- "a" - "b"
     done
   done;;
   output "a")%cmd.

Definition euclidean_algorithm_invariant a b : assertion :=
   fun/inv _ _ _ => True.

Local Hint Unfold euclidean_algorithm_invariant : core.



(* HINT 1 (see Pset9Sig.v) *) 
Theorem euclidean_algorithm_ok : forall a b,
    <{ fun/inv tr h v =>
         0 < a /\ 0 < b /\
       tr = [] }>
    euclidean_algorithm a b (euclidean_algorithm_invariant a b)
    <{ fun/inv tr h v =>
         v $! "a" = v $! "b"
         /\ exists d, tr = [Out d]/\ Nat.gcd a b = d }>.
Proof.
Admitted.


(*|
Streaming Fibonacci sequence
----------------------------

Let's tackle a program that makes nontrivial use of the trace. Our next
example with loops recycles our favorite example, an iterative computation of
the Fibonnaci sequence, but with a twist: it outputs all intermediate results.

Once again, the definition is parametric in an invariant ‘inv’ that is then
key for proving the final specification.
|*)

Example fibonacci n inv :=
  ("cnt" <- 0;;
   "x" <- 0;;
   output "x";;
   "y" <- 1;;
   output "y";;
   {{ inv }}
   while "cnt" < n loop
     "tmp" <- "y";;
     "y" <- "x" + "y";;
     "x" <- "tmp";;
     "cnt" <- "cnt" + 1;;
     output "y"
   done)%cmd.

Inductive fibonacci_spec : trace -> Prop :=
| FibInit: fibonacci_spec [Out 1; Out 0]
| FibRec: forall x y tr,
    fibonacci_spec (Out y :: Out x :: tr) ->
    fibonacci_spec (Out (x + y) :: Out y :: Out x :: tr).

(*|
Here's the definition of the loop invariant that you will have to modify to complete the proof:
|*)

(* HINT 2 (see Pset9Sig.v) *) 
Definition fibonacci_invariant (n: nat) : assertion :=
   fun/inv _ _ _ => True.

Local Hint Unfold fibonacci_invariant : core.
Local Hint Constructors fibonacci_spec : core.

Theorem fibonacci_ok (n: nat):
  <{ fun/inv tr _ _ => tr = [] }>
  fibonacci n (fibonacci_invariant n)
  <{ fun/inv tr' _ _ => fibonacci_spec tr' }>.
Proof.
Admitted.

(*|
Streaming factorial
-------------------

The Fibonnaci example above cheats somewhat: the number of iteration of the
main loop, `n`, is a compile-time constant.  In the ‘fact’ example below,
which streams partial results of a factorial computation, "n" is a regular
variable taken by the program as input.  As before, the definition of ‘fact’
takes an arbitrary invariant, and the hardest part of your job is to find one
that makes the proof go through.
|*)

Example fact inv :=
  ("cnt" <- 0;;
   "x" <- 1;;
   output "x";;
   {{ inv }}
   while "cnt" < "n" loop
     "cnt" <- 1 + "cnt";;
     "x" <- "x" * "cnt";;
     output "x"
   done)%cmd.

Inductive fact_spec : nat -> trace -> Prop :=
| FactInit: fact_spec 0 [Out 1]
| FactRec: forall x n tr,
    fact_spec n (Out x :: tr) ->
    fact_spec (S n) (Out (x * S n) :: Out x :: tr).

Definition fact_invariant (n: nat) : assertion :=
   fun/inv _ _ _ => True.

Local Hint Unfold fact_invariant : core.
Local Hint Constructors fact_spec : core.

(* HINT 3 (see Pset9Sig.v) *) 
Theorem fact_ok (n: nat):
  <{ fun/inv tr _ v => tr = [] /\ v $! "n" = n }>
  fact (fact_invariant n)
  <{ fun/inv tr' _ _ => fact_spec n tr' }>.
Proof.
Admitted.

Fixpoint fact_rec (n: nat) :=
  match n with
  | 0 => 1
  | S n => fact_rec n * S n
  end.

(* Sanity check: *)
Lemma fact_spec_fact_rec : forall n hd tl,
    fact_spec n (Out hd :: tl) -> fact_rec n = hd.
Proof.
  induct 1; simplify; equality.
Qed.

(*|
Heap-manipulating programs
==========================

Mailbox
-------

Let's spice things up a little by exploiting the heap, too.  The program
below implements a mailbox server: every time a client sends an address and a
value, the server stores the value and responds by outputting the previously
stored value.  The process stops as soon as a client tries to write to
address 0.
|*)

Example mailbox inv :=
  ("done" <- 0;;
   {{ inv }}
   while "done" = 0 loop
     "address" <-- input;;
     when "address" = 0 then
       "done" <- 1
     else
       "val" <-- input;;
       output *["address"];;
       *["address"] <- "val"
     done
   done)%cmd.

(*|
Take a moment to think about how you would specify this program before
reading the inductive spec below.
|*)

Inductive mailbox_spec : forall (h: heap) (tr: trace), Prop :=
| MBNil: mailbox_spec $0 []
| MBPut: forall h address val ret tr,
    address <> 0 ->
    ret = h $! address ->
    mailbox_spec h tr ->
    mailbox_spec (h $+ (address, val)) (Out ret :: In val :: In address :: tr).

Inductive mailbox_done (h: heap) : trace -> Prop :=
| MBDone: forall tr,
    mailbox_spec h tr ->
    mailbox_done h (In 0 :: tr).

(*|
Here is an example to help you understand how the spec works:
|*)

Goal mailbox_done
       ($0 $+ (5, 41)  (* From request 1 *)
           $+ (3, 11)  (* From request 2 *)
           $+ (5, 18)  (* From request 3 *)
           $+ (3, 39)) (* From request 4 *)
       [(* Final request: stop program by writing at 0 *)
        In 0;
        (* Fourth request: put 39 at address 3 (returns 11 from request 2) *)
        Out 11; In 39; In 3;
        (* Third request: put 18 at address 5 (returns 41 from request 1) *)
        Out 41; In 18; In 5;
        (* Second request: put 11 at address 3 (returns 0) *)
        Out 0; In 11; In 3;
        (* First request: put 41 at address 5 (returns 0) *)
        Out 0; In 41; In 5].
Proof.
  econstructor.
  econstructor; [ simplify; equality.. | ].
  econstructor; [ simplify; equality.. | ].
  econstructor; [ simplify; equality.. | ].
  econstructor; [ simplify; equality.. | ].
  econstructor.
Qed.

(*|
As always, the key part of the proof is the choice of invariant.
|*)

Definition mailbox_invariant : assertion :=
   fun/inv _ _ _ => True.

Local Hint Unfold mailbox_invariant : core.
Local Hint Constructors mailbox_spec mailbox_done : core.

(* HINT 4 (see Pset9Sig.v) *) 
Theorem mailbox_ok:
  <{ fun/inv tr h _ => tr = [] /\ h = $0 }>
  mailbox mailbox_invariant
  <{ fun/inv tr' h' _ => mailbox_done h' tr' }>.
Proof.
Admitted.

(*|
Streaming search
----------------

Our final example is the trickiest.  It takes the address of an array (“ptr”)
and its length ("length") as local variables, then reads a value to search
for (“needle”) as input and outputs the indices of all positions in the
array at which the value is found.
|*)

Example search inv :=
  ("needle" <-- input;;
   {{ inv }}
   while 0 < "length" loop
     "length" <- "length" - 1;;
     when *["ptr" + "length"] = "needle" then
       output "length" done
   done)%cmd.

(*|
The specification of this program is a bit trickier. There are three cases:

- Searching an empty array doesn't produce output.
- Searching an array that ends with the right value produces one output and
  continues the search.
- Searching an array that ends with another value continues the search
  without producing output.

The key to understand the definition of this predicate is to remember that
the most recent output is at the front of the trace, and we're searching from
the end of the array.
|*)

Inductive search_spec (needle: nat) : forall (offset: nat) (haystack: list nat), trace -> Prop :=
| SearchNil: forall offset,
    search_spec needle offset [] [In needle]
| SearchConsYes: forall n offset haystack tr,
    0 < offset ->
    n = needle ->
    search_spec needle offset haystack tr ->
    search_spec needle (offset - 1) (n :: haystack) (Out (offset - 1) :: tr)
| SearchConsNo: forall n offset haystack tr,
    0 < offset ->
    n <> needle ->
    search_spec needle offset haystack tr ->
    search_spec needle (offset - 1) (n :: haystack) tr.

Inductive search_done haystack tr : Prop :=
| SearchDone: forall needle offset,
    offset = 0 ->
    search_spec needle offset haystack tr ->
    search_done haystack tr.

(*|
Here is an example to help you understand how the spec works:
|*)

Goal search_done [1; 82; 9; 3; 8; 82; 8] [Out 1; Out 5; In 82].
Proof.
  apply SearchDone with (offset := 0) (needle := 82); auto.
  change 0 with (7 - 1 - 1 - 1 - 1 - 1 - 1 - 1) at 2.
  constructor; [ linear_arithmetic | equality | ].
  constructor; [ linear_arithmetic | equality | ].
  constructor; [ linear_arithmetic | equality | ].
  constructor; [ linear_arithmetic | equality | ].
  constructor; [ linear_arithmetic | equality | ].
  constructor; [ linear_arithmetic | equality | ].
  constructor; [ linear_arithmetic | equality | ].
  constructor.
Qed.

(*|
The predicate `array_at h ptr data` asserts that the values in `data` are found in
the range [ptr; ptr + length [data]) in memory.
|*)

Inductive array_at (h: heap) : nat -> list nat -> Prop :=
| ArrayEmpty : forall ptr, array_at h ptr []
| ArrayCons : forall ptr hd tl,
    h $! ptr = hd ->
    array_at h (S ptr) tl ->
    array_at h ptr (hd :: tl).

(*|
Here's an example: the heap below contains the array [12; 8; 7] starting at
address 3: address 3 contains the value 12, address 4 contains 8, and address
5 contains 7.
|*)

Goal array_at
     ($0 $+ (3, 12) $+ (1, 6) $+ (4, 8) $+ (12, 9) $+ (5, 7))
     3
     [12; 8; 7].
Proof.
  econstructor.
  simplify; equality.
  econstructor.
  simplify; equality.
  econstructor.
  simplify; equality.
  econstructor.
Qed.

(*|
You'll need to customize this invariant:
|*)

Definition search_invariant (ptr: nat) (data: list nat) : assertion :=
   fun/inv _ _ _ => True.

Local Hint Unfold search_invariant : core.
Local Hint Constructors search_spec search_done : core.
Arguments List.nth: simpl nomatch.



(* HINT 5 (see Pset9Sig.v) *) 
Theorem search_ok ptr data:
  <{ fun/inv tr h v =>
       tr = [] /\
       v $! "ptr" = ptr /\
       v $! "length" = Datatypes.length data /\
       array_at h ptr data }>
  search (search_invariant ptr data)
  <{ fun/inv tr' h' _ =>
       array_at h' ptr data /\
       search_done data tr' }>.
Proof.
Admitted.

(*|
Congratulations!  If you have extra time and you'd like to explore
opportunities for automation, here is a teaser: with appropriate hints added
to the `core` database (`Hint Resolve`, `Hint Extern` for things like linear arithmetic, and
`Hint Rewrite`), our proofs for all programs above are just `ht.`.
|*)

End Impl.

Module ImplCorrect : Pset9Sig.S := Impl.

(*|
Authors:

- Clément Pit-Claudel
- Joonwon Choi
- Amanda Liu
- Adam Chlipala
|*)
