(** * 6.512 Formal Reasoning About Programs, Spring 2023 - Pset 12 *)

Require Import Frap.
Require Export Eqdep. (* for inj_pair2 as referenced in a hint *)

Local Set Implicit Arguments.

(** * Rely/Guarantee Reasoning *)

(* In this problem set we will reason about concurrent programs using a program
 * logic called “rely-guarantee”.  In this logic, in addition to
 * precondition and postcondition, each Hoare triple also contains a "rely,"
 * which specifies how the environment (i.e. other threads) can interfere and
 * change the state at any point; and a "guarantee," which specifies how
 * *any piece of* this program can change the state (so the Hoare triple should
 * really be called "Hoare quintuple").  The name "rely-guarantee" comes from
 * the interpretation "I rely on the environment to interfere in a way
 * compatible with the rely condition, and I guarantee that I will make no
 * atomic state change not allowed by the guarantee condition."  It is important
 * that the guarantee condition is imposed on all atomic state changes, because
 * any piece of a program can be run in a burst of execution by the scheduler,
 * and its effect is interference from other threads' points of view.  By
 * decomposing a multi-thread program into threads with rely/guarantee acting as
 * their interface, we achieve modular, thread-local reasoning. *)

(** Similar language definition as before, except that we group [Read] and
    [Write] into a syntax category called [Atomic] operations. *)

Inductive loop_outcome acc :=
| Done (a : acc)
| Again (a : acc).

Inductive atomic : Set -> Type :=
| Read (addr : nat) : atomic nat
| Write (addr : nat) (value : nat) : atomic unit.

Inductive cmd : Set -> Type :=
| Return {t : Set} (r : t) : cmd t
| Bind {t t' : Set} (c1 : cmd t) (c2 : t -> cmd t') : cmd t'
| Fail {result} : cmd result
| Par (c1 c2 : cmd unit) : cmd unit
| Atomic {t : Set} (a : atomic t) : cmd t
| Loop {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) : cmd acc.

Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 80).
Notation "'for' x := i 'loop' c1 'done'" := (Loop i (fun x => c1)) (right associativity, at level 80).
Infix "||" := Par.

Notation heap := (fmap nat nat).
Notation "m $! k" := (match m $? k with Some n => n | None => O end) (at level 30).


(* The next two definitions, of step relations, should be unsurprising by now,
 * essentially copying rules we've seen already in other contexts. *)

(* atomic step *)
Inductive astep : forall {t : Set}, heap * atomic t -> heap * t -> Prop :=
| StepRead : forall h a,
    astep (h, Read a) (h, h $! a)
| StepWrite : forall h a v,
    astep (h, Write a v) (h $+ (a, v), tt).

Global Hint Constructors astep : core.

Inductive step : forall {t : Set}, heap * cmd t -> heap * cmd t -> Prop :=
| StepBindRecur : forall {t t' : Set} (c1 c1' : cmd t) (c2 : t -> cmd t') h h',
    step (h, c1) (h', c1')
    -> step (h, Bind c1 c2) (h', Bind c1' c2)
| StepBindProceed : forall {t t' : Set} (v : t) (c2 : t -> cmd t') h,
    step (h, Bind (Return v) c2) (h, c2 v)
| StepPar1 : forall h c1 c2 h' c1',
    step (h, c1) (h', c1')
    -> step (h, Par c1 c2) (h', Par c1' c2)
| StepPar2 : forall h c1 c2 h' c2',
    step (h, c2) (h', c2')
    -> step (h, Par c1 c2) (h', Par c1 c2')
| StepAtomic : forall {t : Set} h a h' (v : t),
    astep (h, a) (h', v)
    -> step (h, Atomic a) (h', Return v) 
| StepLoop : forall (acc : Set) (init : acc) (body : acc -> cmd (loop_outcome acc)) h,
  step (h, Loop init body) (h, x <- body init; match x with
                                               | Done y => Return y
                                               | Again y => Loop y body
                                               end).

(* predicates on heaps *)
Definition hprop := heap -> Prop.
(* binary relations on heaps *)
Definition hrel := heap -> heap -> Prop.

(* "Stability" is an important notion in rely-guarantee logic.  A heap predicate
 * is stable under some interference (expressed as a binary relation on heaps,
 * telling us which heap changes the interference can cause) if whenever the
 * predicate holds before the interference, it will still hold after the
 * interference.  In other words, predicate [P] is preserved by relation [R]. *)
Definition stableP (P : hprop) (R : hrel) := forall h h', P h -> R h h' -> P h'.

(* [stableP] defined the basic interference notion, while [stableQ] adapts it to
 * work for postconditions, which are additionally parameterized over return
 * values. *)
Definition stableQ {t : Set} (Q : t -> hprop) (R : hrel) := forall v, stableP (Q v) R.

(* Here's a convenient predicate to assert both kinds of stability at once.  A
   convenient way to think of it is that P and Q are preserved by R's heap
   modifications. *)
Definition stable {t : Set} (P : hprop) (Q : t -> hprop) R :=
  stableP P R /\ stableQ Q R.

Inductive hoare_triple : forall {t : Set}, hprop -> hrel -> cmd t -> hrel -> (t -> hprop) -> Prop :=
| HtBind : forall {t t' : Set} (c1 : cmd t) (c2 : t -> cmd t') P1 R G Q1 Q2 ,
    (* The bind rule is almost the same as before.  The same rely and guarantee
     * are propagated into subparts.  (Subparts can relax these parameters using
     * the Consequence rule.) *)
    hoare_triple P1 R c1 G Q1
    -> (forall r, hoare_triple (Q1 r) R (c2 r) G Q2)
    -> hoare_triple P1 R (Bind c1 c2) G Q2

| HtPar : forall P1 c1 Q1 P2 c2 Q2 R G1 G2 (P : hprop),
    (* The essence of rely-guarantee reasoning is shown here: one thread's
     * guarantee becomes another thread's rely. *)
    hoare_triple P1 (fun h h' => R h h' \/ G2 h h') c1 G1 Q1
    -> hoare_triple P2 (fun h h' => R h h' \/ G1 h h') c2 G2 Q2

    (* By design we require preconditions to remain stable. *)
    -> stableP P R

    (* We also allow weakening of the precondition into a different
     * more-permissive version for each new thread. *)
    -> (forall h, P h -> P1 h)
    -> (forall h, P h -> P2 h)

    -> hoare_triple P R (Par c1 c2) (fun h h' => G1 h h' \/ G2 h h') (fun r h => Q1 r h /\ Q2 r h)
    (* Note that the combined guarantee is effectively the union of guarantees
     * of the individual threads, while the combined postcondition is the
     * intersection of postconditions. *)

| HtFail : forall {result} R,
    (* Nothing changes for failure: it must be impossible to reach. *)
    hoare_triple (fun _ => False) R (Fail (result := result)) (fun _ _ => False) (fun _ _ => False)

| HtReturn : forall {t : Set} (P : hprop) (R G : hrel) (v : t),
    (* We add one extra premise for [Return], about stability. *)
    stableP P R
    -> hoare_triple P R (Return v) G (fun r h => P h /\ r = v)

| HtAtomic : forall {t : Set} (P : hprop) (R G : hrel) (Q : t -> hprop) a,
    (* Here is the rule that forces us to pick a nonempty guarantee set: it
     * should contain the effect of every atomic operation we run. *)
    (forall (v : t) h h', P h -> astep (h, a) (h', v) -> G h h')

    (* Furthermore, taking an atomic step should get us to the postcondition. *)
    -> (forall (v : t) h h', P h -> astep (h, a) (h', v) -> Q v h')

    (* Here we require both precondition and postcondition to be stable.
     * That is, the environment should not be able to invalidate the truth of
     * either one, when it only takes steps permitted by [R]. *)
    -> stable P Q R

    -> hoare_triple P R (Atomic a) G Q

| HtLoop : forall {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc))
             (I : loop_outcome acc -> hprop) R G,
    (* This rule is about the same as before, with an extra stability
     * requirement. *)
    (forall acc, hoare_triple (I (Again acc)) R (body acc) G I)
    -> (forall acc, stableP (I (Done acc)) R)
    -> hoare_triple (I (Again init)) R (Loop init body) G (fun r h => I (Done r) h)

| HtConsequence : forall {t : Set} P R c G Q (P' : hprop) (R' G' : hrel) (Q' : t -> hprop),
    (* You can relax any part, in the right direction. *)
    hoare_triple P R c G Q
    -> (forall h, P' h -> P h)
    -> (forall v h, Q v h -> Q' v h)
    -> (forall h h', R' h h' -> R h h')
    -> (forall h h', G h h' -> G' h h')
    (* But make sure the new precondition is stable! *)
    -> stableP P' R'
    -> hoare_triple P' R' c G' Q'.


Global Hint Constructors step : core.
Global Hint Constructors hoare_triple : core.

(* Two lemmas for tactics below: *)
Lemma always_stableP : forall (t : Set) P R c G (Q : t -> _),
    hoare_triple P R c G Q -> stableP P R.
Proof. induct 1; unfold stableP in *; first_order. Qed.
(* (* do not do this, makes eauto slow *) Hint Resolve always_stableP : core. *)
Lemma HtWeakenFancy : forall {t : Set} P R c G Q (G' : hrel) (Q' : t -> hprop),
    hoare_triple P R c G Q ->
    (forall v h, Q v h -> Q' v h) ->
    (forall h h', G h h' -> G' h h') ->
    hoare_triple P R c G' Q'.
Proof. eauto using always_stableP. Qed.

(* The usual step and simplification tactics: *)

Ltac simp := repeat (simplify; subst; propositional;
                     try match goal with
                         | [ H : ex _ |- _ ] => invert H
                         | [ H : astep _ _ |- _ ] => invert H
                         | [ H : existT _ _ _ = existT _ _ _ |- _ ] => eapply inj_pair2 in H; subst
                         | [ |- stableP _ _ ] => unfold stableP in *
                         | [ |- stable _ _ _ ] => unfold stable, stableP, stableQ in *
                         end); try solve [ intuition linear_arithmetic | equality ].

Ltac step := eapply HtBind; simp.


(* NEW TACTICS: *)

(* The [fork] tactic builds a Hoare triple for a parallel program
 * with particular preconditions, rely/guarantees, and postconditions. *)
Ltac fork P1_ G1_ Q1_ P2_ G2_ Q2_ := eapply HtWeakenFancy; [ eapply HtPar with (P1 := P1_) (G1 := G1_) (Q1 := Q1_) (P2 := P2_) (G2 := G2_) (Q2 := Q2_) | .. ].

(* The [atomic] tactic builds a Hoare triple for an atomic step
 * with a particular postcondition. *)
Ltac atomic Q_ := eapply HtAtomic with (Q := Q_); simp.


(* KEY DEFINITIONS FOR SAFETY: *)
Inductive notAboutToFail : forall {t : Set}, cmd t -> Prop :=
| NatfBind : forall t t' (c1 : cmd t) (c2 : t -> cmd t'),
    notAboutToFail c1 ->
    notAboutToFail (Bind c1 c2)
| NatfPar : forall c1 c2,
    notAboutToFail c1 ->
    notAboutToFail c2 ->
    notAboutToFail (Par c1 c2)
| NatfReturn : forall (t : Set) (v : t),
    notAboutToFail (Return v)
| NatfAtomic : forall t (a : atomic t),
    notAboutToFail (Atomic a)
| NatfLoop : forall (acc : Set) (init : acc) (body : acc -> cmd (loop_outcome acc)),
    notAboutToFail (Loop init body).

Definition trsys_of h {t : Set} (c : cmd t) := {|
  Initial := {(h, c)};
  Step := step (t := t)
|}.

Module Type S.
  (*[1%]*) Axiom always_stableP_find_me : forall (t : Set) P R c G (Q : t -> _),
    hoare_triple P R c G Q -> stableP P R.
  
  (*[20%]*) Axiom ht_increment : forall init,
    hoare_triple
      (fun h => h $! 0 = init)
      (fun _ _ => False)
      (   (tmp <- Atomic (Read 0); Atomic (Write 0 (tmp + 1)))
       || (tmp <- Atomic (Read 0); Atomic (Write 0 (tmp + 1)))
      )
      (fun _ _ => True)
      (fun _ h => h $! 0 > init).

  (*[79%]*) Axiom hoare_triple_sound : forall (t : Set) P (c : cmd t) Q,
    hoare_triple P (fun _ _ => False) c (fun _ _ => True) Q ->
    forall h, P h ->
    invariantFor (trsys_of h c) (fun st => notAboutToFail (snd st)).
End S.

(* Authors:
   - Peng Wang,
   - Adam Chlipala *)

(*|
HINTS: A few hints to help you if you get stuck on certain 
       problems in Pset 12.
       Beware! Don't read further if you don't want spoilers!
=============================================================
|*)





































(*|

HINT 1: Summarizing the effects of other threads as "rely"
==========================================================

The challenge of the first problem is of course to come up with the right 'rely' and 'guarantee' and weakened precondition (which needs to be stable).  How can you summarize the effects of other threads in a compact 'rely'?

Here is the one used by our solution:
```
  fork (fun h => h $! 0 >= init)
       (fun h h' => h = h' \/ h' $! 0 > init)
       (fun (_ : unit) h => h $! 0 > init)
       (fun h => h $! 0 >= init)
       (fun h h' => h = h' \/ h' $! 0 > init)
       (fun (_ : unit) h => h $! 0 > init).
```

|*)





































(*|
HINT 2: Soundness strategy
==========================

Our proof template for logic soundness starts as usual by appealing to an 'invariant weaking' lemma and an 'invariant induction' lemma.  We can also call them the 'progress' lemma and the 'preservation' lemma. Roughly, the first one says that commands that have a Hoare triple in the current state are not about to fail, and the second says that if a command with a Hoare triple in the current state takes a step, the resulting command will still have a Hoare triple in the resulting state.

A particularly useful lemma from Pset12Sig that is easily missed is `always_stableP`:

```
Lemma always_stableP : forall (t : Set) P R c G (Q : t -> _),
    hoare_triple P R c G Q -> stableP P R.
```
|*)





































(*|
HINT 3: Progress
================

We strengthen the invariant to say that some Hoare triple holds of the current program such that the current heap satisfies the precondition of the Hoare triple: `progress` says that this indeed implies that the program is not about to fail:
```
Lemma progress :
  forall (t : Set) P (c : cmd t) R G Q,
    hoare_triple P R c G Q ->
    forall h, P h ->
         notAboutToFail c.
```
|*)





































(*|
HINT 4: Preservation
====================

Then the 'invariant induction' lemma says that this is in fact an inductive invariant: `preservation` says that if some Hoare triple holds and the current heap satisfies its precondition and we take a step, then another Hoare triple holds with a particular precondition that holds of the new heap:
```
Lemma preservation :
  forall (t : Set) P (c : cmd t) R G Q,
    hoare_triple P R c G Q ->
    forall h,
      P h ->
      forall h' c',
        step (h, c) (h', c') ->
        hoare_triple (fun h'' => R^* h' h'') R c' G Q.
```
|*)





































(*|
HINT 5: Using guarantee for soundness
=====================================

In proving the preservation lemma, you will need to think what the 'guarantee' part of a Hoare triple gives you.  That is, you will need to prove that the 'guarantee' actually guarantees the range of effects. Formally, here is a lemma you will want to prove:
```
Lemma guarantee :
  forall (t : Set) P (c : cmd t) R G Q,
    hoare_triple P R c G Q ->
    forall h,
      P h ->
      forall h' c',
        step (h, c) (h', c') ->
        G^* h h'.
```
|*)





































(*|
HINT 6: Equalities involving existT
===================================

When inverting facts involving `cmd`s, you may find that you have
equalities of the form `existT P p x = existT P p y`. The following
tactic derives the equality `x = y` from facts of this sort and
performs substitution. You may find this useful for your soundness
proof of the rely-guarantee logic.
(This tactic performs a subset of what `simp` does.)
So what makes these strange-looking goals pop into existence, anyway?
They arise from inversion on hypotheses involving fancy types.
In general, inversion derives new equalities.  Sometimes a particular
derived equality relates terms whose *types* are computed via some
fancy recipe.  The constructor `existT` is used to package a term together
with its (first-class) type.  Interestingly, the natural inversion
principle, for equalities on those sorts of packages, is not provable in
Coq!  It's actually formally independent of Coq's logic.  However, a
standard-library lemma `inj_pair2` proves the inversion principle from a
more basic axiom.  For more detail (orthogonal to this course), see the
`Eqdep` module of the Coq standard library.
```
Ltac existT_subst :=
   repeat match goal with
   | [ H : existT _ _ _ = existT _ _ _ |- _ ] => eapply inj_pair2 in H
   end; subst.
```
|*)
