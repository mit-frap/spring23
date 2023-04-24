(** * 6.512 Formal Reasoning About Programs, Spring 2023 - Pset 11 *)

Require Coq816.
Require Import Frap.

Set Implicit Arguments.
Set Asymmetric Patterns.

(** * Shared notations and definitions; main material starts afterward. *)

Notation "m $! k" := (match m $? k with Some n => n | None => O end) (at level 30).
Notation heap := (fmap nat nat).
Notation locks := (set nat).

Global Hint Extern 1 (_ <= _) => linear_arithmetic : core.


(** * Some helpful lemmas to get out of the way *)

Theorem Forall_app_fwd : forall A (P : A -> Prop) ls1 ls2,
    Forall P (ls1 ++ ls2)
    -> Forall P ls1 /\ Forall P ls2.
Proof.
  induct ls1; invert 1; simplify; subst; eauto.
  apply IHls1 in H3; propositional; auto.
Qed.

Theorem Forall_app_bwd : forall A (P : A -> Prop) ls1 ls2,
    Forall P ls1
    -> Forall P ls2
    -> Forall P (ls1 ++ ls2).
Proof.
  induct 1; invert 1; simplify; eauto.
Qed.

Global Hint Resolve Forall_app_bwd : core.

Lemma notin_from_order : forall a l,
  (forall a', a' \in l -> a' > a)
  -> ~a \in l.
Proof.
  sets.
  apply H in H0.
  linear_arithmetic.
Qed.

Global Hint Immediate notin_from_order : core.

Lemma gt_lt : forall n m, n > m -> m < n.
Proof.
  linear_arithmetic.
Qed.

Global Hint Resolve gt_lt : core.


(** * A variant of the object language from lecture *)

(* We'll work with a simpler language that (1) removes [Fail] and (2) only uses
 * a flat nesting structure for multithreading.  In particular, the [cmd] type
 * no longer contains parallel composition. *)

Inductive cmd :=
| Return (r : nat)
| Bind (c1 : cmd) (c2 : nat -> cmd)
| Read (a : nat)
| Write (a v : nat)
| Lock (a : nat)
| Unlock (a : nat).

Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 80).

(* Instead, we separately define a program as a list of commands, for different
 * threads. *)
Notation prog := (list cmd).

(* The intra-thread step relation looks the same as before. *)
Inductive step0 : heap * locks * cmd -> heap * locks * cmd -> Prop :=
| StepBindRecur : forall c1 c1' c2 h h' l l',
  step0 (h, l, c1) (h', l', c1')
  -> step0 (h, l, Bind c1 c2) (h', l', Bind c1' c2)
| StepBindProceed : forall v c2 h l,
  step0 (h, l, Bind (Return v) c2) (h, l, c2 v)

| StepRead : forall h l a,
  step0 (h, l, Read a) (h, l, Return (h $! a))
| StepWrite : forall h l a v,
  step0 (h, l, Write a v) (h $+ (a, v), l, Return 0)

| StepLock : forall h l a,
  ~a \in l
  -> step0 (h, l, Lock a) (h, l \cup {a}, Return 0)
| StepUnlock : forall h l a,
  a \in l
  -> step0 (h, l, Unlock a) (h, l \setminus {a}, Return 0).

(* The whole-program step relation uses list operations to select a thread and
 * step it. *)
Inductive step : heap * locks * prog -> heap * locks * prog -> Prop :=
| StepThread : forall h l cs1 c cs2 h' l' c',
    step0 (h, l, c) (h', l', c')
    -> step (h, l, cs1 ++ c :: cs2) (h', l', cs1 ++ c' :: cs2).

Definition trsys_of (h : heap) (l : locks) (p : prog) := {|
  Initial := {(h, l, p)};
  Step := step
|}.

(* These properties may come in handy: *)

Lemma StepThread1 : forall h l c cs2 h' l' c',
    step0 (h, l, c) (h', l', c')
    -> step (h, l, c :: cs2) (h', l', c' :: cs2).
Proof.
  simplify.
  apply StepThread with (cs1 := []); auto.
Qed.

Global Hint Resolve StepThread1 : core.
Global Hint Constructors step0 step : core.

Lemma step_cat : forall h l p x a,
    step (h, l, p) x
    -> exists h_l_p', step (h, l, a :: p) h_l_p'.
Proof.
  invert 1.
  exists (h', l', a :: cs1 ++ c' :: cs2).
  change (step (h, l, (a :: cs1) ++ c :: cs2) (h', l', (a :: cs1) ++ c' :: cs2)).
  eauto.
Qed.

Global Hint Resolve step_cat : core.


(** * A static analysis for principled use of locks *)

(* If every thread passes the check built into this relation, then we can
 * guarantee lack of deadlock.  (Don't worry; you'll prove it!)
 * A fact [goodCitizen l1 c l2] tells us that when we run [c] in a starting
 * state where it "owns" exactly the locks in [l1], it follows the lock-order
 * rules and terminates in a state where it owns the locks in [l2]. *)
Inductive goodCitizen : locks -> cmd -> locks -> Prop :=
| GcReturn : forall l r,
    goodCitizen l (Return r) l
| GcBind : forall l1 c1 l2 c2 l3,
    goodCitizen l1 c1 l2
    -> (forall r, goodCitizen l2 (c2 r) l3)
    -> goodCitizen l1 (Bind c1 c2) l3
| GcRead : forall l a,
    goodCitizen l (Read a) l
| GcWrite : forall l a v,
    goodCitizen l (Write a v) l
| GcLock : forall l a,
    (forall a', a' \in l -> a' > a)
    (* ^-- Note that this premise enforces the total order on locks!
     *     That is, every lock already held must be greater than the new one. *)
    -> goodCitizen l (Lock a) (l \cup {a})
| GcUnlock : forall l a,
    a \in l
    (* ^-- We also require that a thread only tries to unlock locks that it
     *     owns. *)
    -> goodCitizen l (Unlock a) (l \setminus {a}).


(** * An alternative semantics that tracks lock ownership *)

(* To prove deadlock-freedom from [goodCitizen], we go by way of an alternative
 * semantics that assigns each held lock to an owning thread.  Concretely, we
 * represent a program with a lockset annotated on each command. *)
Definition prog' := list (locks * cmd).

(* These next two functions project back out the baseline components of an
 * instrumented state. *)

Fixpoint progOf (p : prog') : prog :=
  match p with
  | nil => nil
  | (_, c) :: p' => c :: progOf p'
  end.

Fixpoint locksOf (p : prog') : locks :=
  match p with
  | nil => {}
  | (l, _) :: p' => l \cup locksOf p'
  end.
(* That [\cup] is set union.  We also use [\cap] for intersection and
 * [\setminus] for set difference.  There are also binary relations [\in] for
 * membership and [\subseteq] for subset inclusion.  When faced with any goal
 * that seems to follow just from the laws of set theory, try calling the [sets]
 * tactic from the book library. *)

(* You'll likely want to use this lemma in your solution. *)
Lemma progOf_app : forall p1 p2,
    progOf (p1 ++ p2) = progOf p1 ++ progOf p2.
Proof.
  induct p1; simplify; eauto.
  cases a; simplify.
  equality.
Qed.

(* This predicate captures the property that no lock has multiple owners.
 * NOTE: you won't actually need to understand this function in detail, as we
 * will be proving enough starter lemmas to hide all reasoning about it! *)
Fixpoint disjointLocks (p : prog') : Prop :=
  match p with
  | nil => True
  | (l, _) :: p' => l \cap locksOf p' = {}
                    /\ disjointLocks p'
  end.


(** * Proof that the ownership semantics simulates the baseline semantics *)

(* In this section, we prove for you a useful invariant of any program that is
 * full of good citizens.  It's safe to skip ahead to the statement of
 * [a_useful_invariant]. *)

(* But, for the curious: we use this relation to connect a baseline state to an
 * ownership-tracking state. *)
Inductive assign_lock_ownership : heap * locks * prog -> heap * prog' -> Prop :=
| ALO : forall h p',
    Forall (fun l_c => goodCitizen (fst l_c) (snd l_c) {}) p'
    -> disjointLocks p'
    -> assign_lock_ownership (h, locksOf p', progOf p') (h, p').

Fixpoint prog'Of (p : prog) : prog' :=
  match p with
  | nil => nil
  | c :: p' => ({}, c) :: prog'Of p'
  end.

Lemma progOf_prog'Of : forall p,
    progOf (prog'Of p) = p.
Proof.
  induct p; simplify; equality.
Qed.

Lemma locksOf_prog'Of : forall p,
    locksOf (prog'Of p) = {}.
Proof.
  induct p; simplify; eauto.
  rewrite IHp.
  sets.
Qed.

Lemma goodCitizen_prog'Of : forall p,
    Forall (fun c => goodCitizen {} c {}) p
    -> Forall (fun l_c => goodCitizen (fst l_c) (snd l_c) {}) (prog'Of p).
Proof.
  induct 1; simplify; eauto.
Qed.

Lemma disjointLocks_init : forall p, disjointLocks (prog'Of p).
Proof.
  induct p; simplify; propositional.
  sets.
Qed.

Lemma init : forall h p,
    Forall (fun c => goodCitizen {} c {}) p
    -> assign_lock_ownership (h, {}, p) (h, prog'Of p).
Proof.
  simplify.
  rewrite <- (progOf_prog'Of p) at 1.
  rewrite <- (locksOf_prog'Of p).
  constructor.
  eauto using goodCitizen_prog'Of.
  apply disjointLocks_init.
Qed.

Lemma invert_progOf : forall p' cs1 c cs2,
    progOf p' = cs1 ++ c :: cs2
    -> exists p1' l p2',
      p' = p1' ++ (l, c) :: p2'
      /\ progOf p1' = cs1
      /\ progOf p2' = cs2.
Proof.
  induct p'; simplify.

  cases cs1; simplify; equality.

  cases a.
  cases cs1; simplify.

  invert H.
  exists [], s, p'; auto.

  invert H.
  apply IHp' in H2.
  first_order; subst.
  exists ((s, c1) :: x), x0, x1; auto.
Qed.

Lemma locksOf_app : forall p1 p2,
    locksOf (p1 ++ p2) = locksOf p1 \cup locksOf p2.
Proof.
  induct p1; simplify; eauto.
  sets.
  cases a.
  rewrite IHp1.
  sets.
Qed.

Global Hint Constructors goodCitizen : core.

Lemma take_step' : forall h l c h' l' c',
    step0 (h, l, c) (h', l', c')
    -> forall l1 l2, goodCitizen l1 c l2
    -> (l' = l
        /\ goodCitizen l1 c' l2)
       \/ (exists a, ~a \in l
                     /\ ~a \in l1
                     /\ l' = l \cup {a}
                     /\ goodCitizen (l1 \cup {a}) c' l2)
       \/ (exists a, a \in l
                     /\ a \in l1
                     /\ l' = l \setminus {a}
                     /\ goodCitizen (l1 \setminus {a}) c' l2).
Proof.
  induct 1; invert 1; simplify; eauto 8.

  apply IHstep0 in H4; auto.
  first_order; subst; eauto 8.

  invert H3.
  eauto.

  right; left; exists a; repeat split; eauto.
  sets.
Qed.

Global Hint Constructors assign_lock_ownership : core.

Lemma disjointLocks_unchanged : forall x x0 c x1,
    disjointLocks (x ++ (x0, c) :: x1)
    -> forall c', disjointLocks (x ++ (x0, c') :: x1).
Proof.
  induct x; simplify; propositional.
  cases a; propositional; eauto.
  repeat rewrite locksOf_app in *; auto.
Qed.

Lemma disjointLocks_add : forall a x x0 c x1,
    disjointLocks (x ++ (x0, c) :: x1)
    -> ~a \in locksOf (x ++ (x0, c) :: x1)
    -> forall c', disjointLocks (x ++ (x0 \cup {a}, c') :: x1).
Proof.
  induct x; simplify; propositional.

  sets.

  cases a0; propositional; eauto.
  repeat rewrite locksOf_app in *; simplify; auto.
  sets.

  replace ({a} \cup x0) with (x0 \cup {a}) by sets.
  eapply IHx; eauto.
  sets.
Qed.

Lemma disjointLocks_remove : forall a x x0 c x1,
    disjointLocks (x ++ (x0, c) :: x1)
    -> a \in x0
    -> forall c', disjointLocks (x ++ (x0 \setminus {a}, c') :: x1).
Proof.
  induct x; simplify; propositional.

  sets.

  cases a0; propositional; eauto.
  repeat rewrite locksOf_app in *; simplify; auto.
  sets.
Qed.

Global Hint Immediate disjointLocks_unchanged disjointLocks_add disjointLocks_remove : core.

Lemma disjointLocks_middle' : forall s x x0 c x1,
    s \cap locksOf (x ++ (x0, c) :: x1) = { }
    -> x0 \cap s = { }.
Proof.
  induct x; simplify.

  sets.

  cases a.
  repeat rewrite locksOf_app in *.
  simplify.
  sets.
Qed.

Lemma disjointLocks_middle : forall x x0 c x1,
    disjointLocks (x ++ (x0, c) :: x1)
    -> x0 \cap locksOf x = {}
       /\ x0 \cap locksOf x1 = {}.
Proof.
  induct x; simplify.

  propositional.
  sets.

  cases a.
  invert H.
  apply IHx in H1.
  propositional.
  repeat rewrite locksOf_app in *; simplify.
  sets.
Qed.

Lemma take_step : forall s1 s2,
    step s1 s2
    -> forall s1', assign_lock_ownership s1 s1'
    -> exists s2', assign_lock_ownership s2 s2'.
Proof.
  invert 1; invert 1.
  apply invert_progOf in H4; first_order; subst.
  apply Forall_app_fwd in H5; propositional.
  invert H1; simplify.
  eapply take_step' in H0; eauto; first_order; subst.

  exists (h', x ++ (x0, c') :: x1).
  replace (locksOf (x ++ (x0, c) :: x1))
          with (locksOf (x ++ (x0, c') :: x1))
    by (repeat rewrite locksOf_app; simplify; sets).
  replace (progOf x ++ c' :: progOf x1)
          with (progOf (x ++ (x0, c') :: x1))
    by (repeat rewrite progOf_app; simplify; sets).
  eauto.

  exists (h', x ++ (x0 \cup {x2}, c') :: x1).
  replace (locksOf (x ++ (x0, c) :: x1) \cup {x2})
          with (locksOf (x ++ (x0 \cup {x2}, c') :: x1))
    by (repeat rewrite locksOf_app; simplify; sets).
  replace (progOf x ++ c' :: progOf x1)
          with (progOf (x ++ (x0 \cup {x2}, c') :: x1))
    by (repeat rewrite progOf_app; simplify; sets).
  eauto.

  exists (h', x ++ (x0 \setminus {x2}, c') :: x1).
  replace (locksOf (x ++ (x0, c) :: x1) \setminus {x2})
          with (locksOf (x ++ (x0 \setminus {x2}, c') :: x1))
    by (repeat apply disjointLocks_middle in H6; propositional;
        repeat rewrite locksOf_app; simplify; sets).
  replace (progOf x ++ c' :: progOf x1)
          with (progOf (x ++ (x0 \setminus {x2}, c') :: x1))
    by (repeat rewrite progOf_app; simplify; sets).
  eauto.
Qed.

(* Now the invariant proof: starting with good citizens, we always wind up in a
 * baseline state that has a matching ownership-tracking state. *)
Theorem a_useful_invariant : forall h p,
    Forall (fun c => goodCitizen {} c {}) p
    -> invariantFor (trsys_of h {} p) (fun st => exists st', assign_lock_ownership st st').
Proof.
  simplify.
  apply invariant_induction; simplify; first_order; subst.
  eauto using init.
  eauto using take_step.
Qed.


(* OK, now to state the deadlock-freedom property that we ask you to prove! *)

(* This predicate captures when a command is done executing. *)
Inductive finished : cmd -> Prop :=
| Finished : forall r, finished (Return r).

Global Hint Constructors finished : core.

(* It has this useful connection to [progOf]: *)
Lemma finished_progOf : forall p,
    Forall (fun l_c => finished (snd l_c)) p
    -> Forall finished (progOf p).
Proof.
  induct 1; simplify; eauto.
  cases x; eauto.
Qed.

Global Hint Immediate finished_progOf : core.

Module Type S.
  (* Finally, your task is to prove deadlock-freedom: if all commands are good
   * citizens, then execution is either completely finished running, or
   * it is possible to take a step. *)
  (*[100%]*) Axiom deadlock_freedom : forall h p,
      Forall (fun c => goodCitizen {} c {}) p
      -> invariantFor (trsys_of h {} p) (fun h_l_p =>
                                           let '(_, _, p') := h_l_p in
                                           Forall finished p'
                                           \/ exists h_l_p', step h_l_p h_l_p').
End S.

(*|
TIPS: A few things that might be helpful keep in mind as you work on Pset 11
============================================================================

Sets and Lists
==============
If you are stuck trying to prove any fiddly but obvious-seeming fact, say about sets or lists, please ask the course staff for advice!


Lemma Statements
================
Most lemma statements are at the bottom of the file; the pset will be more interesting if you start with just the textual hints and then look at the statements only if you need them!

Structure of the proof
======================

The key trick in this proof is to distinguish two cases: does any thread hold a lock, or not?
You can use the `excluded_middle` tactic for this. 

Progress without locking
========================

You will need to consider the case in which no thread holds any lock.  In that case, can threads get blocked?  If yes, how?  Does the `goodCitizen` assumption rule that case out, and if so what can you say about the progress of each individual thread?

Progress with locking
=====================

If some lock is taken, we need a bit more work.  Unlike the previous case, some threads may in fact be waiting on other threads and hence cannot make progress.  But, could all threads be blocked?  If not, how can we identify a thread that's ready to run?


 *)


(*|
HINTS: A few hints to help you if you get stuck on certain 
       problems in Pset 11.
       Beware! Don't read further if you don't want spoilers!
=============================================================
|*)





































(*|
HINT 1: Progress with Locking
=============================

We phrased this intuition for progress without locking in the following way (to prove this lemma, you may need a specialized version of it applied to a single command).

```
Lemma who_has_the_lock : forall l h a p,
      Forall (fun l_c => goodCitizen (fst l_c) (snd l_c) {}) p
      -> a \in locksOf p
      -> locksOf p \subseteq l
      -> (exists h_l_p', step (h, l, progOf p) h_l_p')
        \/ (exists a', a' < a /\ a' \in l).
```

What this means is that we can either find a command that's ready to run, or we can find another owned lock that is *less than* `a`, the one we already knew had an owner.  If we apply this lemma repeatedly, we will eventually find a command that can run; can you see why? (hint: the key part is a' < a).

Of course, we can't actually “apply this lemma repeatedly”; we need induction — specifically, strong induction.

|*)






































(*|
HINT 2: Progress with No Locks
==============================

Our no-locks lemma looks like this:

```
Theorem if_no_locks_held_then_progress : forall h p,
      Forall (fun l_c => goodCitizen (fst l_c) (snd l_c) {}) p
      -> locksOf p = {}
      -> Forall (fun l_c => finished (snd l_c)) p
        \/ exists h_l_p', step (h, locksOf p, progOf p) h_l_p'.
```
|*)






































(*|
HINT 3: Progress with Locks
===========================
Out with-locks lemma looks like this:

```
Theorem if_lock_held_then_progress : forall bound a h p,
    Forall (fun l_c => goodCitizen (fst l_c) (snd l_c) {}) p
    -> a \in locksOf p
    -> a < bound
    -> Forall (fun l_c => finished (snd l_c)) p
       \/ exists h_l_p', step (h, locksOf p, progOf p) h_l_p'.
```
|*)






































(*|
HINT 4: Single Command Progress with Locks 
==========================================
The following lemma zooms in on a single command for proving progress with locks:

```
Lemma who_has_the_lock' : forall h a l l1 c,
      goodCitizen l1 c {}
      -> a \in l1
      -> l1 \subseteq l
      -> (exists h' l' c', step0 (h, l, c) (h', l', c'))
        \/ (exists a', a' < a /\ a' \in l).
```

To prove this sub-lemma, we relax the restriction on the owned-lock set from *after* running `c`, so now we must also consider the case where `c` is finished. (A good-citizen command that owns a lock before and owns no locks afterward can never be finished, since it must do its civic duty and release the lock.)

```
Lemma who_has_the_lock'' : forall h a l l1 c l2,
      goodCitizen l1 c l2
      -> a \in l1
      -> l1 \subseteq l
      -> finished c
         \/ (exists h' l' c', step0 (h, l, c) (h', l', c'))
         \/ (exists a', a' < a /\ a' \in l).
```

Out with-locks lemma looks like this:

```
Theorem if_lock_held_then_progress : forall bound a h p,
    Forall (fun l_c => goodCitizen (fst l_c) (snd l_c) {}) p
    -> a \in locksOf p
    -> a < bound
    -> Forall (fun l_c => finished (snd l_c)) p
       \/ exists h_l_p', step (h, locksOf p, progOf p) h_l_p'.
```
|*)



































(*|
HINT 5: Excluded Middle in Deadlock Freedom
===========================================

Our proof of deadlock_freedom' begins by using calling `excluded_middle (exists a, a \in locksOf p)`.
|*)
