(** * 6.512 Formal Reasoning About Programs, Spring 2023 - Pset 10 *)
Require Coq816.
Require Import Frap Setoid Classes.Morphisms SepCancel.
Export Setoid Classes.Morphisms.

Set Implicit Arguments.
Set Asymmetric Patterns.

(** * Shared notations and definitions; main material starts afterward. *)

Notation "m $! k" := (match m $? k with Some n => n | None => O end) (at level 30).
Definition heap := fmap nat nat.
Definition assertion := heap -> Prop.

Global Hint Extern 1 (_ <= _) => linear_arithmetic : core.
Global Hint Extern 1 (@eq nat _ _) => linear_arithmetic : core.

Ltac simp := repeat (simplify; subst; propositional;
                     try match goal with
                         | [ H : ex _ |- _ ] => invert H
                         end); try linear_arithmetic.


(** * Encore of last mixed-embedding language from last time *)

(* First, almost exactly the same syntactic language definition as from class: *)

Inductive loop_outcome acc res :=
| Done (r : res)
| Again (a : acc).
(* ^-- One slight difference: we allow the result type from a loop to differ from the
 *     type of the iteration variable.
 *)

Arguments Done {acc} {res}.
Arguments Again {acc} {res}.

Inductive cmd : Set -> Type :=
| Return {result : Set} (r : result) : cmd result
| Bind {result result'} (c1 : cmd result') (c2 : result' -> cmd result) : cmd result
| Read (a : nat) : cmd nat
| Write (a v : nat) : cmd unit
| Loop {acc res : Set} (init : acc) (body : acc -> cmd (loop_outcome acc res)) : cmd res
| Fail {result} : cmd result
| Alloc (numWords : nat) : cmd nat
| Free (base numWords : nat) : cmd unit.

Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 80).
Notation "'for' x := i 'loop' c1 'done'" := (Loop i (fun x => c1)) (right associativity, at level 80).

Fixpoint initialize (h : heap) (base numWords : nat) : heap :=
  match numWords with
  | O => h
  | S numWords' => initialize h base numWords' $+ (base + numWords', 0)
  end.

Fixpoint deallocate (h : heap) (base numWords : nat) : heap :=
  match numWords with
  | O => h
  | S numWords' => deallocate (h $- base) (base+1) numWords'
  end.

(* Now here's *almost* exactly the same semantics.  See one exception noted
 * below. *)
Inductive step : forall A, heap * cmd A -> heap * cmd A -> Prop :=
| StepBindRecur : forall result result' (c1 c1' : cmd result') (c2 : result' -> cmd result) h h',
  step (h, c1) (h', c1')
  -> step (h, Bind c1 c2) (h', Bind c1' c2)
| StepBindProceed : forall (result result' : Set) (v : result') (c2 : result' -> cmd result) h,
  step (h, Bind (Return v) c2) (h, c2 v)

| StepLoop : forall (acc res : Set) (init : acc) (body : acc -> cmd (loop_outcome acc res)) h,
  step (h, Loop init body) (h, o <- body init; match o with
                                               | Done a => Return a
                                               | Again a => Loop a body
                                               end)

| StepRead : forall h a v,
  h $? a = Some v
  -> step (h, Read a) (h, Return v)
| StepWrite : forall h a v v',
  h $? a = Some v
  -> step (h, Write a v') (h $+ (a, v'), Return tt)

| StepAlloc : forall h numWords a,
  (forall i, i < numWords -> h $? (a + i) = None)
  -> a <> 0
  -> step (h, Alloc numWords) (initialize h a numWords, Return a)
(* ^-- DIFFERENCE FROM CLASS: Now we record that a freshly allocated object has
 * a nonnull address, so that we are free to use null (0) for a special purpose
 * in linked data structures. *)

| StepFree : forall h a numWords,
  step (h, Free a numWords) (deallocate h a numWords, Return tt).

Definition trsys_of (h : heap) {result} (c : cmd result) := {|
  Initial := {(h, c)};
  Step := step (A := result)
|}.


(* Here's exactly the same instantiation of the separation-logic connectives and
 * their algebraic laws. *)
Module Import Sep <: SEP.
  Definition hprop := heap -> Prop.

  (* Implication *)
  Definition himp (p q : hprop) := forall h, p h -> q h.

  (* Equivalence *)
  Definition heq (p q : hprop) := forall h, p h <-> q h.

  (* Lifting a pure proposition *)
  Definition lift (P : Prop) : hprop :=
    fun h => P /\ h = $0.

  (* Separating conjunction, one of the two big ideas of separation logic *)
  Definition star (p q : hprop) : hprop :=
    fun h => exists h1 h2, split h h1 h2 /\ disjoint h1 h2 /\ p h1 /\ q h2.

  (* Existential quantification *)
  Definition exis A (p : A -> hprop) : hprop :=
    fun h => exists x, p x h.

  (* Convenient notations *)
  Declare Scope sep_scope.
  Notation "[| P |]" := (lift P) : sep_scope.
  Infix "*" := star : sep_scope.
  Notation "'exists' x .. y , p" := (exis (fun x => .. (exis (fun y => p)) ..)) : sep_scope.
  Delimit Scope sep_scope with sep.
  Notation "p === q" := (heq p%sep q%sep) (no associativity, at level 70).
  Notation "p ===> q" := (himp p%sep q%sep) (no associativity, at level 70).

  Local Open Scope sep_scope.

  Lemma iff_two : forall A (P Q : A -> Prop),
    (forall x, P x <-> Q x)
    -> (forall x, P x -> Q x) /\ (forall x, Q x -> P x).
  Proof.
    firstorder.
  Qed.

  Local Ltac t := (unfold himp, heq, lift, star, exis; propositional; subst);
                 repeat (match goal with
                         | [ H : forall x, _ <-> _ |- _  ] =>
                           apply iff_two in H
                         | [ H : ex _ |- _ ] => destruct H
                         | [ H : split _ _ $0 |- _ ] => apply split_empty_fwd in H
                         end; propositional; subst); eauto 15.

  Theorem himp_heq : forall p q, p === q
                               <-> (p ===> q /\ q ===> p).
  Proof.
    t.
  Qed.

  Theorem himp_refl : forall p, p ===> p.
  Proof.
    t.
  Qed.

  Theorem himp_trans : forall p q r, p ===> q -> q ===> r -> p ===> r.
  Proof.
    t.
  Qed.

  Theorem lift_left : forall p (Q : Prop) r,
    (Q -> p ===> r)
    -> p * [| Q |] ===> r.
  Proof.
    t.
  Qed.

  Theorem lift_right : forall p q (R : Prop),
    p ===> q
    -> R
    -> p ===> q * [| R |].
  Proof.
    t.
  Qed.

  Local Hint Resolve split_empty_bwd' : core.

  Theorem extra_lift : forall (P : Prop) p,
    P
    -> p === [| P |] * p.
  Proof.
    t.
    apply split_empty_fwd' in H1; subst; auto.
  Qed.

  Theorem star_comm : forall p q, p * q === q * p.
  Proof.
    t.
  Qed.

  Theorem star_assoc : forall p q r, p * (q * r) === (p * q) * r.
  Proof.
    t.
  Qed.

  Theorem star_cancel : forall p1 p2 q1 q2, p1 ===> p2
    -> q1 ===> q2
    -> p1 * q1 ===> p2 * q2.
  Proof.
    t.
  Qed.

  Theorem exis_gulp : forall A p (q : A -> _),
    p * exis q === exis (fun x => p * q x).
  Proof.
    t.
  Qed.

  Theorem exis_left : forall A (p : A -> _) q,
    (forall x, p x ===> q)
    -> exis p ===> q.
  Proof.
    t.
  Qed.

  Theorem exis_right : forall A p (q : A -> _) x,
    p ===> q x
    -> p ===> exis q.
  Proof.
    t.
  Qed.

  Theorem emp_heap : forall h, lift True h -> h = $0.
  Proof.
    t.
  Qed.
End Sep.

(* Instantiate our big automation engine to these definitions. *)
Module Import Se := SepCancel.Make(Sep).
Export Sep Se.

(* ** Some extra predicates outside the set that the engine knows about *)

(* These are exactly the same as before, too! *)

(* Capturing single-mapping heaps *)
Definition heap1 (a v : nat) : heap := $0 $+ (a, v).
Definition ptsto (a v : nat) : hprop :=
  fun h => h = heap1 a v.

Theorem try_ptsto_first : forall a v, try_me_first (ptsto a v).
Proof.
  simplify.
  apply try_me_first_easy.
Qed.

Global Hint Resolve try_ptsto_first : core.

(* Helpful notations, some the same as above *)
Notation "[| P |]" := (lift P) : sep_scope.
Notation emp := (lift True).
Infix "*" := star : sep_scope.
Notation "'exists' x .. y , p" := (exis (fun x => .. (exis (fun y => p)) ..)) : sep_scope.
Delimit Scope sep_scope with sep.
Notation "p === q" := (heq p%sep q%sep) (no associativity, at level 70).
Notation "p ===> q" := (himp p%sep q%sep) (no associativity, at level 70).
Infix "|->" := ptsto (at level 30) : sep_scope.

Fixpoint multi_ptsto (a : nat) (vs : list nat) : hprop :=
  match vs with
  | nil => emp
  | v :: vs' => a |-> v * multi_ptsto (a + 1) vs'
  end%sep.

Infix "|-->" := multi_ptsto (at level 30) : sep_scope.

Fixpoint zeroes (n : nat) : list nat :=
  match n with
  | O => nil
  | S n' => zeroes n' ++ 0 :: nil
  end.

Fixpoint allocated (a n : nat) : hprop :=
  match n with
  | O => emp
  | S n' => (exists v, a |-> v) * allocated (a+1) n'
  end%sep.

Infix "|->?" := allocated (at level 30) : sep_scope.


(** * Finally, the Hoare logic *)

(* The only change we make here is in the loop rule. *)

Inductive hoare_triple : forall {result}, assertion -> cmd result -> (result -> assertion) -> Prop :=
(* First, some basic rules that look exactly the same as before *)
| HtReturn : forall P {result : Set} (v : result),
    hoare_triple P (Return v) (fun r => P * [| r = v |])%sep
| HtBind : forall P {result' result} (c1 : cmd result') (c2 : result' -> cmd result) Q R,
    hoare_triple P c1 Q
    -> (forall r, hoare_triple (Q r) (c2 r) R)
    -> hoare_triple P (Bind c1 c2) R

(* THIS RULE IS DIFFERENT. *)
| HtLoop : forall {acc res : Set} (init : acc) (body : acc -> cmd (loop_outcome acc res)) P Q,
    (* As before, the premise forces us to consider any accumulator at the start
     * of a loop iteration, proving a Hoare triple for each case. *)
    (forall acc,
        (* Important difference: now the rule is parameterized over both a
         * precondition [P] and a postcondition [Q], each of which takes, as an
         * extra argument, the latest accumulator value. *)
        hoare_triple (P acc) (body acc)
                     (fun r =>
                        match r with
                        | Done res =>
                          Q acc res
                          (* The loop is done?  Then the postcondition had
                           * better be satisfied directly.  Note that it takes
                           * the "before" and "after" accumulators as arguments.
                           * We'll see shortly why that pays off.... *)
                        | Again acc' =>
                          (* It's time for more iterations?  Then we'd better
                           * satisfy [P] w.r.t. the "after" accumulator, but
                           * with a twist.  We are allowed to *forget* some
                           * state, captured by the arbitrary frame predicate
                           * [R].  The idea is that the state we shunt into [R]
                           * will not be touched again until the loop finishes
                           * running. *)
                          exists R, P acc' * R
                                    (* There is another important requirement on
                                     * [R]: Assume that the loop finishes, so
                                     * that the postcondition [Q] is satisfied
                                     * w.r.t. the new accumulator [acc'].  If we
                                     * *put back* [R], we should then arrive at
                                     * a state where the postcondition is
                                     * satisfied w.r.t. the "before" accumulator
                                     * [acc]! *)
                                    * [| forall r, Q acc' r * R ===> Q acc r |]
                        end%sep))
    -> hoare_triple (P init) (Loop init body) (Q init)
(* All that may be a bit abstract, but we will soon show an example
 * verification, to illustrate. *)

| HtFail : forall {result},
    hoare_triple (fun _ => False) (Fail (result := result)) (fun _ _ => False)

| HtRead : forall a R,
    hoare_triple (exists v, a |-> v * R v)%sep (Read a) (fun r => a |-> r * R r)%sep
| HtWrite : forall a v v',
    hoare_triple (a |-> v)%sep (Write a v') (fun _ => a |-> v')%sep
| HtAlloc : forall numWords,
    hoare_triple emp%sep (Alloc numWords) (fun r => [| r <> 0 |] * r |--> zeroes numWords)%sep
| HtFree : forall a numWords,
    hoare_triple (a |->? numWords)%sep (Free a numWords) (fun _ => emp)%sep

| HtConsequence : forall {result} (c : cmd result) P Q (P' : assertion) (Q' : _ -> assertion),
    hoare_triple P c Q
    -> P' ===> P
    -> (forall r, Q r ===> Q' r)
    -> hoare_triple P' c Q'
| HtFrame : forall {result} (c : cmd result) P Q R,
    hoare_triple P c Q
    -> hoare_triple (P * R)%sep c (fun r => Q r * R)%sep.

(* Now more duplicated infrastructure from class.  Feel free to skip ahead to
 * the example verification. *)

Notation "{{ P }} c {{ r ~> Q }}" :=
  (hoare_triple P%sep c (fun r => Q%sep))
    (at level 90, c at next level,
     format "'[hv' {{ P }} '/'  c  '/' {{ r  ~>  Q }} ']'").

Lemma HtStrengthen : forall {result} (c : cmd result) P Q (Q' : _ -> assertion),
    hoare_triple P c Q
    -> (forall r, Q r ===> Q' r)
    -> hoare_triple P c Q'.
Proof.
  simplify.
  eapply HtConsequence; eauto.
  reflexivity.
Qed.

Lemma HtWeaken : forall {result} (c : cmd result) P Q (P' : assertion),
    hoare_triple P c Q
    -> P' ===> P
    -> hoare_triple P' c Q.
Proof.
  simplify.
  eapply HtConsequence; eauto.
  reflexivity.
Qed.

(* Fancy theorem to help us rewrite within preconditions and postconditions *)
Global Instance hoare_triple_morphism : forall A,
  Proper (heq ==> eq ==> (eq ==> heq) ==> iff) (@hoare_triple A).
Proof.
  Transparent himp.
  repeat (hnf; intros).
  unfold pointwise_relation in *; intuition subst.

  eapply HtConsequence; eauto.
  rewrite H; reflexivity.
  intros.
  hnf in H1.
  specialize (H1 r _ eq_refl).
  rewrite H1; reflexivity.

  eapply HtConsequence; eauto.
  rewrite H; reflexivity.
  intros.
  hnf in H1.
  specialize (H1 r _ eq_refl).
  rewrite H1; reflexivity.
Qed.

Global Opaque heq himp lift star exis ptsto.

Theorem use_lemma : forall result P' (c : cmd result) (Q : result -> assertion) P R,
  hoare_triple P' c Q
  -> P ===> P' * R
  -> hoare_triple P c (fun r => Q r * R)%sep.
Proof.
  simp.
  eapply HtWeaken.
  eapply HtFrame.
  eassumption.
  eauto.
Qed.

Theorem HtRead' : forall a v,
  hoare_triple (a |-> v)%sep (Read a) (fun r => a |-> v * [| r = v |])%sep.
Proof.
  simp.
  apply HtWeaken with (exists r, a |-> r * [| r = v |])%sep.
  eapply HtStrengthen.
  apply HtRead.
  simp.
  cancel; auto.
  subst; cancel.
Qed.

Theorem HtRead'' : forall p P R,
  P ===> (exists v, p |-> v * R v)
  -> hoare_triple P (Read p) (fun r => p |-> r * R r)%sep.
Proof.
  simp.
  eapply HtWeaken.
  apply HtRead.
  assumption.
Qed.

Lemma HtReturn' : forall P {result : Set} (v : result) Q,
    P ===> Q v
    -> hoare_triple P (Return v) Q.
Proof.
  simp.
  eapply HtStrengthen.
  constructor.
  simp.
  cancel.
  subst. assumption.
Qed.

(* This tactic is just for the purposes of error messages,
   it does nothing if it succeeds
 *)
Ltac check_type_of desc e t :=
  let t' := type of e in
  (tryif unify t' t then idtac else fail 0 desc e
                                      "should have the type" t
                                      "but instead has the type" t').

(* This tactic is just for the purposes of error messages,
   it does nothing if it succeeds
 *)
Ltac check_loop_inv_args pre post :=
  lazymatch goal with
  | |- hoare_triple _ (@Loop ?acc ?res _ _) _ =>
      check_type_of "loop precondition" pre
        constr:(forall _ : acc, assertion);
      check_type_of "loop postcondition" post
        constr:(forall (_ : acc) (_ : res), assertion)
  | |- _ => fail "This tactic expects a Hoare triple for a loop"
  end.

Ltac basic := apply HtReturn' || eapply HtWrite || eapply HtAlloc || eapply HtFree.

Ltac step0 := basic || eapply HtBind || (eapply use_lemma; [ basic | cancel; auto ])
              || (eapply use_lemma; [ eapply HtRead' | solve [ cancel; auto ] ])
              || (eapply HtRead''; solve [ cancel ])
              || (eapply HtStrengthen; [ eapply use_lemma; [ basic | cancel; auto ] | ])
              || (eapply HtConsequence; [ apply HtFail | .. ]).
Ltac step := step0; simp.
Ltac ht := simp; repeat step.
Ltac conseq := simplify; eapply HtConsequence.
Ltac use_IH H := conseq; [ apply H | .. ]; ht.
Ltac loop_inv0 P0 Q0 := eapply HtConsequence; [ apply HtLoop with (P := P0) (Q := Q0) | .. ].
Ltac loop_inv P0 Q0 := check_loop_inv_args P0 Q0; loop_inv0 P0 Q0; ht.
Ltac use H := (eapply use_lemma; [ eapply H | cancel; auto ])
              || (eapply HtStrengthen; [ eapply use_lemma; [ eapply H | cancel; auto ] | ]).

Ltac heq := intros; apply himp_heq; split.

(* Some lemmas that may or may not be useful. *)

Lemma star_emp_l P :
  emp * P === P.
Proof.
  heq; cancel.
Qed.

Lemma star_emp_r P :
  P * emp === P.
Proof.
  heq; cancel.
Qed.

(** * Binary trees *)

(* Now we define binary trees and ask you to verify two of their classic
 * operations. *)

Inductive tree :=
| Leaf
| Node (l : tree) (x : nat) (r : tree).

(* [m] for memory! *)
Fixpoint mtree' (t : tree) (p : nat) : hprop :=
  match t with
  | Leaf => [| p = 0 |]
  | Node l x r => [| p <> 0 |]
                  * exists p1 p2, p |--> [p1; x; p2]
                                  * mtree' l p1
                                  * mtree' r p2
  end%sep.

(* Here's the version that forgets exactly which tree it is. *)
Definition mtree (p : nat) : hprop :=
  (exists t, mtree' t p)%sep.

(* And here's an extra layer of indirection: a mutable pointer to a tree, which
 * comes in handy for operations that modify the tree. *)
Definition mtreep (p : nat) : hprop :=
  (exists p', [| p <> 0 |] * p |-> p' * mtree p')%sep.

(* Here's the usual lookup operation. *)
Definition lookup (x p : nat) :=
  t <- Read p; (* First peel away the initial layer of indirection.
                * You will want to use the regular old frame rule to forget
                * about some of the state that you won't need after this
                * point! *)
  for a := t loop
    (* The accumulator tells us: the node of the tree we have reached
     * (for [Again]) or whether the key [x] has been found (for [Done]). *)
    if a ==n 0 then
      (* Oh, the pointer is null.  Sorry, didn't find [x]. *)
      Return (Done false)
    else
      (* Read the data value of the current node (which must be nonnull). *)
      y <- Read (a + 1);
      if x ==n y then
        (* Found it! *)
        Return (Done true)
      else if x <=? y then
        (* The key must be earlier in the tree.  Read the left-child pointer and
         * continue looping with it. *)
        l <- Read a;
        Return (Again l)
      else
        (* The key must be later in the tree.  Read the right-child pointer and
         * continue looping with it. *)
        r <- Read (a + 1 + 1);
        (* Why [+ 1 + 1] instead of [+ 2]?  It happens to work better with the
         * automation we're using. ;) *)
        Return (Again r)
  done.

(* And here's the operation to add a new key to a tree. *)
Definition insert (x p : nat) :=
  for a := p loop
    (* Note that now the accumulator is not the latest tree root, but instead
     * *a pointer to it*, so that we may overwrite that pointer if necessary.
     * We start by reading the actual root out of the pointer [p]. *)
    q <- Read a;
    if q ==n 0 then
      (* It's a null pointer?  Perfect.  This is the spot to insert a new
       * node. *)
      node <- Alloc 3;
      (* Initialize its data field with [x]. *)
      _ <- Write (node + 1) x;
      (* Redirect the pointer [p] to the new node. *)
      _ <- Write a node;
      Return (Done tt)
    else
      (* Nonnull?  Read the data field into [y]. *)
      y <- Read (q + 1);
      if x <=? y then
        (* The right spot to insert must be to the left.  Recurse thataway. *)
        Return (Again q)
      else
        (* The right spot to insert must be to the right.  Recurse thataway. *)
        Return (Again (q + 1 + 1))
  done.

(* Something very subtle happened in that loop: we iterated using a pointer into
 * *the interior of a struct*, in each branch of the last [if]!  This is a fun
 * example of the kinds of tricks that can be played in a low-level language,
 * and the verification techniques are up to the challenge. *)


(* Your task: verify the two methods.  (By the way, our solution also includes a
 * soundness proof for this logic, but we aren't asking you to write one.)
 *
 * IMPORTANT NOTE:
 * The difficulty of this problem set is scoped assuming you will use the
 * tactics included in this file, which are very similar to the ones from
 * Lecture 19!  Trying to attack these proofs from first principles will likely
 * lead to proof size spiraling out of control.  The main ingredients you should
 * expect to reuse are:
 *  - [step]: A tactic to choose the right Hoare-logic rule to apply next, when
 *    your goal is a Hoare triple
 *  - [cancel]: A tactic to prove an implication between two separation-logic
 *    assertions, or reduce it to a simpler implication by *cancel*ing matching
 *    subformulas; before calling [cancel], be sure you have marked [Opaque]
 *    all of the predicates standing for data structures!  There is an
 *    [Opaque mtree] command in Pset10.v for precisely this reason; don't
 *    remove it, and put any lemmas about this predicate before it.
 *  - [heq]: A tactic to reduce a separation-logic assertion equivalence (using
 *    [===]) to two implications (using [===>])
 *  - [loop_inv P0 Q0]: A tactic to apply the loop rule, given an invariant
 *    split in a peculiar way; see Pset10.v for an example
 *  - [setoid_rewrite H]: A tactic to rewrite within a separation-logic
 *    implication, using an equivalence that applies to one of its subterms
 *
 * Our solution also has a few direct uses of rules [HtConsequence] and
 * [HtFrame], sometimes using the [with] syntax of [apply] to specify values
 * for some variables that appear in these rules' statements. In particular,
 * you can use [HtConsequence] before [HtFrame] to ensure that the predicate
 * that you want to frame out is in the desired syntactic position so that
 * [HtFrame] will apply. The [exis_right] lemma will also be handy, as used
 * in the example included in Pset10.v. *)
Module Type S.
  (* Confirm that [lookup] has no memory errors and that [p] still points to
   * some binary tree once [lookup] has completed. Note that this theorem is
   * very similar to [llength_ok]. We encourage you to adapt that proof to
   * this one.
   *)
  (*[40%]*) Axiom lookup_ok : forall x p,
    {{ mtreep p }}
      lookup x p
    {{ _ ~> mtreep p }}.

  (* Confirm that [insert] has no memory errors and preserves the binary
   * tree structure pointed to by [p].
   *)
  (*[60%]*) Axiom insert_ok : forall x p,
    {{ mtreep p }}
      insert x p
    {{ _ ~> mtreep p }}.
End S.

(* For an extra challenge, you might try implementing and verifying deletion. *)
