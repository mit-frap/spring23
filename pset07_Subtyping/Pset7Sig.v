(** * 6.512 Formal Reasoning About Programs, Spring 2023 - Pset 7 *)

Require Coq816.
Require Import Frap.Frap.

Module Type S.

  (* --- DEFINITIONS --- *)

  Inductive exp  :=
  | Var (x : var)
  | Abs (x : var) (e1 : exp)
  | App (e1 e2 : exp)
  | TupleNil
  | TupleCons (e1 e2 : exp)
  | Proj (e : exp) (n : nat)
  .

  Inductive value : exp -> Prop :=
  | VAbs : forall x e1, value (Abs x e1)
  | VTupleNil : value TupleNil
  | VTupleCons : forall e1 e2, value e1 -> value e2 -> value (TupleCons e1 e2)
  .

  Fixpoint subst (e1 : exp) (x : var) (e2 : exp) : exp :=
    match e2 with
    | Var y => if y ==v x then e1 else Var y
    | Abs y e2' => Abs y (if y ==v x then e2' else subst e1 x e2')
    | App e2' e2'' => App (subst e1 x e2') (subst e1 x e2'')
    | TupleNil => TupleNil
    | TupleCons e2' e2'' => TupleCons (subst e1 x e2') (subst e1 x e2'')
    | Proj e2' n => Proj (subst e1 x e2') n
    end.

  Inductive context :=
  | Hole
  | App1 (C : context) (e2 : exp)
  | App2 (v1 : exp) (C : context)
  | TupleCons1 (C : context) (e2 : exp)
  | TupleCons2 (v1 : exp) (C : context)
  | Proj1 (C : context) (n : nat)
  .

  Inductive plug : context -> exp -> exp -> Prop :=
  | PlugHole : forall e, plug Hole e e
  | PlugApp1 : forall e e' C e2,
      plug C e e'
      -> plug (App1 C e2) e (App e' e2)
  | PlugApp2 : forall e e' v1 C,
      value v1
      -> plug C e e'
      -> plug (App2 v1 C) e (App v1 e')
  | PlugTupleCons1 : forall C e e' e2,
      plug C e e'
      -> plug (TupleCons1 C e2) e (TupleCons e' e2)
  | PlugTupleCons2 : forall v1 C e e',
      value v1
      -> plug C e e'
      -> plug (TupleCons2 v1 C) e (TupleCons v1 e')
  | PlugProj : forall C e e' n,
      plug C e e'
      -> plug (Proj1 C n) e (Proj e' n)
  .

  Inductive step0 : exp -> exp -> Prop :=
  | Beta : forall x e v,
      value v
      -> step0 (App (Abs x e) v) (subst v x e)
  | Proj0 : forall v1 v2,
      value v1
      -> value v2
      -> step0 (Proj (TupleCons v1 v2) 0) v1
  | ProjS : forall v1 v2 n,
      value v1
      -> value v2
      -> step0 (Proj (TupleCons v1 v2) (1 + n)) (Proj v2 n)
  .

  Inductive step : exp -> exp -> Prop :=
  | StepRule : forall C e1 e2 e1' e2',
      plug C e1 e1'
      -> plug C e2 e2'
      -> step0 e1 e2
      -> step e1' e2'.

  Definition trsys_of (e : exp) :=
    {| Initial := {e}; Step := step |}.

  Inductive type :=
  | Fun (dom ran : type)
  | TupleTypeNil
  | TupleTypeCons (t1 t2 : type)
  .

  Inductive subtype : type -> type -> Prop :=
  | StFun : forall t1' t2' t1 t2,
      subtype t1 t1' ->
      subtype t2' t2 ->
      subtype (Fun t1' t2') (Fun t1 t2)
  | StTupleNilNil :
      subtype TupleTypeNil TupleTypeNil
  | StTupleNilCons : forall t1 t2,
      subtype (TupleTypeCons t1 t2) TupleTypeNil
  | StTupleCons : forall t1' t2' t1 t2,
      subtype t1' t1 ->
      subtype t2' t2 ->
      subtype (TupleTypeCons t1' t2') (TupleTypeCons t1 t2)
  .

  Infix "$<:" := subtype (at level 70).

  Inductive proj_t : type -> nat -> type -> Prop :=
  | ProjT0 : forall t1 t2,
      proj_t (TupleTypeCons t1 t2) 0 t1
  | ProjTS : forall t1 t2 n t,
      proj_t t2 n t ->
      proj_t (TupleTypeCons t1 t2) (1 + n) t
  .

  Inductive has_ty : fmap var type -> exp -> type -> Prop :=
  | HtVar : forall G x t,
      G $? x = Some t ->
      has_ty G (Var x) t
  | HtAbs : forall G x e1 t1 t2,
      has_ty (G $+ (x, t1)) e1 t2 ->
      has_ty G (Abs x e1) (Fun t1 t2)
  | HtApp : forall G e1 e2 t1 t2,
      has_ty G e1 (Fun t1 t2) ->
      has_ty G e2 t1 ->
      has_ty G (App e1 e2) t2
  | HtTupleNil : forall G,
      has_ty G TupleNil TupleTypeNil
  | HtTupleCons: forall G e1 e2 t1 t2,
      has_ty G e1 t1 ->
      has_ty G e2 t2 ->
      has_ty G (TupleCons e1 e2) (TupleTypeCons t1 t2)
  | HtProj : forall G e n t t',
      has_ty G e t' ->
      proj_t t' n t ->
      has_ty G (Proj e n) t
  | HtSub : forall G e t t',
      has_ty G e t' ->
      t' $<: t ->
      has_ty G e t
  .

  (* --- THEOREMS TO PROVE (in Pset7.v) --- *)

  (*[5%]*)
  Axiom subtype_refl : forall t, t $<: t.

  (*[25%]*)
  Axiom subtype_trans : forall t1 t2 t3, t1 $<: t2 -> t2 $<: t3 -> t1 $<: t3.

  (*[70%]*)
  Axiom safety :
    forall e t,
      has_ty $0 e t -> invariantFor (trsys_of e)
                                    (fun e' => value e'
                                               \/ exists e'', step e' e'').

End S.

(*|
TIPS: A few things that might be helpful keep in mind as you work on Pset 7
===========================================================================

Use LambdaCalculusAndTypeSoundness.v
====================================

Make sure you read and understand `LambdaCalculusAndTypeSoundness.v` from 
FRAP, since a lot of the proof structure from that file can be reused in this Pset!
We certainly aren't expecting you to reconstruct the whole theory of type soundness
from scratch.  Then, the follow-on file `EvaluationContexts.v` is an even
better source of examples to copy from, since this pset adopts the evaluation-contexts
technique exercised thoroughly by that file/chapter.

---

Automate with `Hint Constructors`
================================

By using a command of the form:

```
Local Hint Constructors <inductive predicate> : core.
```

the constructors of the <inductive predicate> are now included in the 
proof search that `auto` and `eauto` performs.
*)


(*|
HINTS: A few hints to help you if you get stuck on certain 
       problems in Pset 7.
       Beware! Don't read further if you don't want spoilers!
=============================================================
|*)






































(*|
HINT 1: Transitivity of subtyping
=================================

Before attempting to prove `subtype_trans`, make sure you understand why in `StFun`, the subtyping order of the argument types is reversed (this is called contravariance). Maybe it helps to think of it this way: If we have `u1 $<: u2`, all code expecting a `u2` should also work if we give it something more specific, such as a `u1`. Now if we have `Apple $<: Fruit $<: Food`, and `u2` is the type of fruit consumers, i.e. `u2 = Fun Fruit Result`, what can you safely replace a fruit consumer with? If you replace it with an apple consumer, but keep treating it like a fruit consumer, you might end up feeding pears to an apple consumer, and it might be allergic to pears, and you have a problem. On the other hand, replacing a fruit consumer with a food consumer and continuing to treat it like a fruit consumer is safe: All the apples you'll feed to the food consumer will be accepted by it (and the food consumer might be a bit surprised that its diet is less varied than expected, but that's not a soundness issue ;-)).

If you try to prove `subtype_trans` as-is by inducting on the proof tree of `t1 $<: t2`, you will get stuck in the case where `t1 $<: t2` was created using `StFun`.
To discuss this case, we will use `A`s for argument types and `B`s for return types, and use numbers such that they match the subtyping order, e.g. `A0 $<: A1 $<: A2 $<: A3` etc. Coq's autogenerated names will look different, and we encourage you to use commands like `rename t1 into myNewName` to give more intuitive names to the variables.
In the `StFun` case, `induct` knows that the `t1 $<: t2` you're inducting on was created using the `StFun` constructor, and therefore the original `t1 $<: t2` can be written as `Fun A2 B1 $<: Fun A1 B2`, and the preconditions of `StFun` hold, that is, `A1 $<: A2` and `B1 $<: B2`.
Moreover, you got a `t2 $<: t3`, and since you know that `t2` is a function type, inverting it will reveal that `t3` is a function type as well, so it can be written as `Fun A1 B2 $<: Fun A0 B3`, and `invert` also gave you `A0 $<: A1` and `B2 $<: B3` because these are the preconditions of `StFun`.
Using this, and some IHs, you have to prove `t1 $<: t3`, i.e. `Fun A2 B1 $<: Fun A0 B3`. If you try applying `StFun`, you'll need to prove `A0 $<: A2` and `B1 $<: B3`. If you forgot to generalize `t3`, this will not work at all, but even if you change the statement to

```
Lemma subtype_trans_aux : forall t1 t2, t1 $<: t2 -> forall t3, t2 $<: t3 -> t1 $<: t3).
```

you can now prove `B1 $<: B3`, but proving `A0 $<: A2` will still not work.
Let's look at the IH which allows us to prove `B1 $<: B3`: `induct` provided it because `B1 $<: B2` is a subproof of the derivation you're inducting on, and it tells you that you can "append" any subtyping derivation of the form `B2 $<: B3` to the right of it to obtain a `B1 $<: B3`.
Now the other IH (the one which `induct` provides because `A1 <: A2` is a subproof of the derivation you're inducting on) also tells you that you can "append" another subtyping derivation to the right, but what you'd really need here would be to "append" an `A0 $<: A1` derivation *to the left* of the `A1 <: A2`.

So it might help to spell out the *induction motive* `P` explicitly, that is, to write

```
Definition P(t1 t2: type): Prop := ...
```

and then to prove

```
Lemma subtype_trans_aux : forall t1 t2, t1 $<: t2 -> P t1 t2.
```

In our previous attempt, we did something which is equivalent to defining

```
Definition P t1 t2 := forall t3, t2 $<: t3 -> t1 $<: t3.
```

and observe how this only allows you to append a subtyping derivation on the right.
Therefore, by using a conjunction `/\` in `P`, you should say that you can also append a subtyping derivation on the left, so that you get a stronger IH in the `StFun` case, and then `induct` on the `t1 $<: t2` derivation will work.
 *)






































(*|
HINT 2: Helper lemmas for progress: Canonical forms
===================================================

While proving the progress lemma, you will have a case where you know that the type of some expression is a function type and that this expression is a value. Without subtyping, you could just invert these two hypotheses (in the right order) to conclude that the expression is an `Abs` expression. But now that we have subtyping, the typing derivation could contain any number of `HtSub` usages, so you will need induction to peel them off, and to do that, you should prove a separate lemma.
Also prove a similar lemma saying that if an expression has type `TupleTypeCons` and is a value, the expression is indeed a `TupleCons`.
Existential quantifiers can be helpful to state those lemmas.
 *)






































(*|
HINT 3: Helper lemmas for preservation: Typing inversion
========================================================

In the proof of preservation for `step0`, you will have `has_ty` hypotheses for for expressions with known constructors, e.g. for an `(Abs x e)` or for a `(TupleCons e1 e2)` etc.
Without subtyping, inverting such a `has_ty` would give you just one subgoal, where the `has_ty` is replaced by the preconditions that were used to construct it.
Now, with subtyping, you get one additional subgoal for the `HtSub` case, where the original `has_ty` is replaced by a similar looking `has_ty` and a subtyping derivation. You could invert that new `has_ty` again, and again and again, and your proving endeavor would never end.
This hint shows how to solve this problem for `TupleCons`, but you will have to apply this trick for all constructors of `exp`.
Without subtyping, we would know that if `TupleCons e1 e2` has a type t, then there are some types t1 and t2 such that e1 has type t1, e2 has type t2, and `t = TupleTypeCons t1 t2`. This fact would follow directly from the fact that there is only a single rule for typing a TupleCons expression.
However, once we add subtyping, the HtSub rule allows us to type an expression of any form, and so the above property doesn't hold. A typing derivation for the fact that `TupleCons e1 e2` has type t can be arbitrarily long even when e1 and e2 are small, but we still know that it must start from an application of the HtTupleCons rule, followed by potentially many applications of the HtSub rule. Since we have proven that the subtype relation is reflexive and transitive, we know the many applications of the HtSub rule can be replaced with exactly one, meaning we know that there is a derivation for TupleCons e1 e2 that is an HtSub rule applied to the HtTupleCons rule. This tells us the following fact:

```
Lemma has_ty_TupleCons G e e' t:
   has_ty G (TupleCons e e') t ->
   exists t1 t2, has_ty G e t1 /\ has_ty G e' t2 /\ TupleTypeCons t1 t2 $<: t.
```

Knowing this fact is useful for the type-safety proof, because now whenever we know that `TupleCons e e'` has some type, we can directly get information about the types of its subexpressions. If we only tried to invert the original typing derivation, the last rule in the derivation may have been HtSub, in which case we would make no "progress" down towards finding the application of the rule HtTupleCons.

You should be able to formulate and prove similar lemmas for Abs, App, and Proj.

 *)
