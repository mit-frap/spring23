(*|
=============================================================
 6.512 Formal Reasoning About Programs, Spring 2023 - Pset 8
=============================================================
|*)

Require Coq816.
Require Export Frap.Frap.

Module Type S.
  Inductive bop := Plus | Minus | Times.

  Inductive arith : Set :=
  | Const (n : nat)
  | Var (x : var)
  | Bop (b : bop) (e1 e2 : arith).

  Inductive cmd :=
  | Skip
  | Assign (x : var) (e : arith)
  | Sequence (c1 c2 : cmd)
  | If (e : arith) (thn els : cmd)
  | While (e : arith) (body : cmd).

  Definition valuation := fmap var nat.

  Fixpoint interp (e : arith) (v : valuation) : nat :=
    match e with
    | Const n => n
    | Var x =>
      match v $? x with
      | None => 0
      | Some n => n
      end
    | Bop bp e1 e2 =>
      match bp with
      | Plus => Nat.add
      | Minus => Nat.sub
      | Times => Nat.mul
      end (interp e1 v) (interp e2 v)
    end.

  Inductive eval : valuation -> cmd -> valuation -> Prop :=
  | EvalSkip : forall v,
      eval v Skip v
  | EvalAssign : forall v x e,
      eval v (Assign x e) (v $+ (x, interp e v))
  | EvalSeq : forall v c1 v1 c2 v2,
      eval v c1 v1
      -> eval v1 c2 v2
      -> eval v (Sequence c1 c2) v2
  | EvalIfTrue : forall v e thn els v',
      interp e v <> 0
      -> eval v thn v'
      -> eval v (If e thn els) v'
  | EvalIfFalse : forall v e thn els v',
      interp e v = 0
      -> eval v els v'
      -> eval v (If e thn els) v'
  | EvalWhileTrue : forall v e body v' v'',
      interp e v <> 0
      -> eval v body v'
      -> eval v' (While e body) v''
      -> eval v (While e body) v''
  | EvalWhileFalse : forall v e body,
      interp e v = 0
      -> eval v (While e body) v.

  Fixpoint vars (e: arith) : set var :=
    match e with
    | Const n => {} (** A constant has no variables **)
    | Var x => {x} (** A variable has… one variable! **)
    | Bop _ e1 e2 => vars e1 \cup vars e2 (** An operator's variables are the variables of its subterms **)
    end.

  Inductive Confidential (pub: set var) : set var (* pc *) -> cmd (* program *) -> Prop :=
  | ConfidentialSkip : forall pc,
      Confidential pub pc Skip
  (** A `Skip` is safe. **)
  | ConfidentialAssignPrivate : forall pc x e,
      ~ x \in pub ->
              Confidential pub pc (Assign x e)
  (** Assigning to a private variable is safe. **)
  | ConfidentialAssignPublic : forall pc x e,
      vars e \subseteq pub ->
      pc \subseteq pub ->
      Confidential pub pc (Assign x e)
  (** Assigning to a public variable variable is safe as long as the expression does not mention private variables and we are not under a conditional that depends on private variables. **)
  | ConfidentialSeq : forall pc c1 c2,
      Confidential pub pc c1 ->
      Confidential pub pc c2 ->
      Confidential pub pc (Sequence c1 c2)
  (** A sequence is safe if both halves of it are safe. **)
  | ConfidentialIf : forall pc e thn els,
      Confidential pub (pc \cup vars e) thn ->
      Confidential pub (pc \cup vars e) els ->
      Confidential pub pc (If e thn els)
  (** A conditional is safe if both branches are safe, noting that the branches run with additional variables in the `pc`. **)
  | ConfidentialWhile : forall pc e body,
      Confidential pub (pc \cup vars e) body ->
      Confidential pub pc (While e body).
  (** A while loop is safe if its body is safe, noting that the body runs with additional variables in the `pc`. **)

  Definition same_public_state pub (v1 v2: valuation) :=
    restrict pub v1 = restrict pub v2.

  
  (*[5%]*) Parameter private_can_determine_termination : bool.
  

  (*[85%]*) Axiom non_interference :
    forall pub c v1 v1' v2 v2',
      eval v1 c v1' ->
      eval v2 c v2' ->
      Confidential pub {} c ->
      same_public_state pub v1 v2 ->
      same_public_state pub v1' v2'.

  Definition pub_example := {"x", "y", "z"}. (* Variables x, y, z are public. *)

  Parameter tricky_example : cmd.

  (*[5%]*) Axiom tricky_rejected : ~ Confidential pub_example {} tricky_example.

  (*[5%]*) Axiom tricky_confidential :
    forall v1 v1' v2 v2',
      eval v1 tricky_example v1' ->
      eval v2 tricky_example v2' ->
      same_public_state pub_example v1 v2 ->
      same_public_state pub_example v1' v2'.
End S.

(*|
TIPS: A few things that might be helpful keep in mind as you work on Pset 8
===========================================================================


The `set` type
==============

- `set A` is a set of values of type `A`.

- Common operators include `x \in s` (membership), `s1 \subseteq s2`
  (inclusion), `s1 \cup s2` (union).  Because of the way sets are implemented,
  `x \in s` is the same as `s x`.

- Sets can be used in conjunction with maps: `restrict s m` computes a new map
  from `m` with all variables not in set `s` removed.

- If you find yourself proving properties of sets, especially regarding
  `restrict`, try the `sets` tactic — it often helps.

- If you want to reason on whether a particular element `k` is in set `s`, you
  can use the `excluded_middle` tactic, as `excluded_middle (k \in s)`.

Here is an example demonstrating some of these points (remember that, to prove
equality on maps, you can use the `maps_equal` tactic):
|*)

Goal forall {K V} (k: K) (v: V) (s: set K) (m: fmap K V),
    k \in s ->
    restrict s (m $+ (k, v)) = (restrict s m) $+ (k, v).
Proof.
  simplify.
  maps_equal.
  - rewrite lookup_restrict_true.
    + simplify; equality.
    + eassumption.
  - excluded_middle (k0 \in s).
    + rewrite !lookup_restrict_true by assumption.
      simplify; equality.
    + rewrite !lookup_restrict_false by assumption.
      equality.
Qed.



(*|
HINTS: A few hints to help you if you get stuck on certain 
       problems in Pset 8.
       Beware! Don't read further if you don't want spoilers!
=============================================================
|*)






































(*|
HINT 1: Generalize `non_interference`
=====================================

You will need to generalize the noninterference theorem statement to prove it by induction.
*)





































(*|
HINT 2: `invert`ing `Confidential` hypotheses
=============================================

Some of your theorems will take `Confidential … c` premises.  In the case of a while loop, `invert`-ing `Confidential pub pc (While e body)` will give you `Confidential pub (pc \cup vars e) body`, but you will lose the original `Confidential pub pc (While e body)` fact.  In our proof, we had to reprove it (you could also make a copy of it) a few times, to apply a theorem to the `eval _ (While _ _) _` premise of the `EvalWhileTrue` constructor.  (This hint will make more sense when you get there.)
*)
