Require Import Frap Pset10.Pset10Sig.
(** * 6.512 Formal Reasoning About Programs, Spring 2023 - Pset 10 *)

(* The Forgetful Loop Rule

 In this pset, we explore a different proof rule for loops, which combines
 some of the nifty small-footprint reasoning of the frame rule.  Specifically,
 we consider loops where we traverse linked data structures, *forgetting*
 about nodes as we pass through them, narrowing our focus to just the subsets
 of nodes that future loop iterations might touch.  Recall how, to prove
 linked-list length, we needed to do some grunt work with a predicate for
 linked-list segments, even though the function will never again access the
 segments described in the loop invariant.  The forgetful loop rule will allow
 us to skip the segments and write a loop invariant the matches the overall
 function specification.

 Most of the relevant definitions and documentation are contained in
 Pset10Sig.v; we recommend that you read through it now.  Most of the contents
 are the same as what we saw in class, and the important differences are
 highlighted below:

Inductive hoare_triple
  : forall {result}, assertion -> cmd result -> (result -> assertion) -> Prop :=
…

(* THIS RULE IS DIFFERENT. *)
| HtLoop : forall {acc res : Set} (init : acc) (body : acc -> cmd (loop_outcome acc res)) P Q,
    (* As before, the premise forces us to consider any accumulator at the start
       of a loop iteration, proving a Hoare triple for each case. *)
    (forall acc,
        (* Important difference: now the rule is parameterized over both a
           precondition [P] and a postcondition [Q], each of which takes, as an
           extra argument, the latest accumulator value. *)
        hoare_triple (P acc) (body acc)
                     (fun r =>
                        match r with
                        | Done res =>
                          Q acc res
                          (* The loop is done?  Then the postcondition had
                             better be satisfied directly.  Note that it takes
                             the "before" and "after" accumulators as arguments.
                             We'll see shortly why that pays off.... *)
                        | Again acc' =>
                          (* It's time for more iterations?  Then we'd better
                             satisfy [P] w.r.t. the "after" accumulator, but
                             with a twist.  We are allowed to *forget* some
                             state, captured by the arbitrary frame predicate
                             [R].  The idea is that the state we shunt into [R]
                             will not be touched again until the loop finishes
                             running. *)
                          exists R, P acc' * R
                                    (* There is another important requirement on
                                       [R]: Assume that the loop finishes, so
                                       that the postcondition [Q] is satisfied
                                       w.r.t. the new accumulator [acc'].  If we
                                       *put back* [R], we should then arrive at
                                       a state where the postcondition is
                                       satisfied w.r.t. the "before" accumulator
                                       [acc]! *)
                                    * [| forall r, Q acc' r * R ===> Q acc r |]
                        end%sep))
    -> hoare_triple (P init) (Loop init body) (Q init)
(* All that may be a bit abstract, but we will show an example
 * verification below, to illustrate. *)

| HtAlloc : forall numWords,
    hoare_triple emp%sep (Alloc numWords) (fun r => [| r <> 0 |] * r |--> zeroes numWords)%sep
(* ----------------------------------------------------^^^^^^
   DIFFERENCE FROM CLASS: Now we record that a freshly allocated object has
   a nonnull address, so that we are free to use null (0) for a special purpose
   in linked data structures. *)
*)

(* Let's make this a bit more concrete with an example: *)

(** * EXAMPLE VERIFICATION: linked-list length revisited *)

(* First, here's essentially the same list-predicate definition from class. *)

Fixpoint llist' (ls : list nat) (p : nat) : hprop :=
  match ls with
  | nil => [| p = 0 |]
  | x :: ls' => [| p <> 0 |] * exists p', p |--> [x; p'] * llist' ls' p'
  end%sep.

(* Let's define a less precise version, which forgets exactly which data a list
 * stores, only remembering that there is indeed a list rooted at [p]. *)
Definition llist (p : nat) :=
  (exists ls, llist' ls p)%sep.
(* In general with this pset, we'll work with less precise predicates like this
   [llist], to give you a bit of a break! *)

(* We can prove some logical equivalences on our predicates. *)
Lemma llist'_null : forall {ls p}, p = 0
  -> llist' ls p === [| ls = nil |].
Proof.
  heq; cases ls; cancel.
Qed.

Theorem llist_null : forall p, p = 0
  -> llist p === emp.
Proof.
  unfold llist; simplify.
  setoid_rewrite (llist'_null H).
  (* setoid_rewrite does not support "with", just positional arguments *)
  heq; cancel.
Qed.

Lemma llist'_nonnull : forall {ls p}, p <> 0
  -> llist' ls p === exists ls' x p', [| ls = x :: ls' |] * p |--> [x; p'] * llist' ls' p'.
Proof.
  heq; cases ls; cancel.
  - equality.
  - invert H0; cancel.
Qed.

Theorem llist_nonnull : forall {p}, p <> 0
  -> llist p === exists x p', p |--> [x; p'] * llist p'.
Proof.
  unfold llist; simplify.
  setoid_rewrite (llist'_nonnull H).
  heq; cancel.
Qed.

Opaque llist.
(* It's important that we mark [llist] as opaque after we've finished proving
 * the lemmas, so that its definition is never again unfolded.  Rather, we
 * reason about it only with the two lemmas we proved for it. *)

(* Now here's linked-list length again. *)
Definition llength (p : nat) :=
  for a := (p, 0) loop
    if fst a ==n 0 then
      Return (Done (snd a))
    else
      y <- Read (fst a + 1);
      Return (Again (y, snd a + 1))
  done.

(* And here's the simpler proof. However, this time around, we
 * don't prove any functional correctness. We only confirm
 * the absence of memory errors and that if a [llength] call finishes,
 * [p] still points to some linked list.
 *)
Theorem llength_ok : forall p,
  {{ llist p }}
    llength p
  {{ _ ~> llist p }}.
Proof.
  unfold llength.
  simp.
  (* We have reached the loop, and it's time to pick an invariant.  The
   * forgetful loop rule asks for both a precondition and a postcondition, so
   * the [loop_inv] tactic takes both as separate arguments. 
   *
   * The arguments to [loop_inv] are exactly the arguments for the precondition
   * and postcondition passed to [HtLoop]. The precondition is an assertion
   * that is a fuction of the accumulator. The postcondition is an assertion
   * that is a function of the accumulator and the result.
   *)
  loop_inv (fun a : nat * nat => llist (fst a))
           (fun (a : nat * nat) (_ : nat) => llist (fst a)).
    (* We can use the most natural invariant: there is a list rooted at the first
     * component of the accumulator [a]. *)
  -
    cases (a ==n 0).
    + step.
      cancel.
    + rewrite llist_nonnull by assumption.
      step.
      step.
      simp.
      step.
      (* Here's where we encounter the extra quantified [R] from the forgetful loop
       * rule.  The automation isn't quite smart enough to pick a good [R] for us,
       * and anyway we might prefer to be in control of what we forget!  We use the
       * lemma [exis_right] for manual instantiatiation of the existential quantifier
       * immediately to the right of [===>]. *)
      apply exis_right with (x := ((a+1) |-> r * exists n0, a |-> n0)%sep).
      (* The right choice in this case: forget the list cell that [a] points to.  We
       * are done with this cell and can continue the loop using only the cells that
       * follow it. *)
      cancel.
      rewrite (llist_nonnull n).
      (* We specify the hypothesis [n] of [llist_nonnull] so that Coq chooses to
       * rewrite the correct occurrence of [llist] in the goal.  Try without that
       * detail and watch Coq make the wrong choice! *)
      cancel.
  - cancel.
  - cancel.
Qed.

(** * Binary trees *)

(* Now we define binary trees and ask you to verify two of their classic
 * operations. This verification task only concerns memory safety, not
   functional correctness -- which you already tackled in Pset 4! *)

(*
Inductive tree :=
| Leaf
| Node (l : tree) (x : nat) (r : tree).
*)

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

(* Your task: verify the lookup and insertion methods below.

   Before diving into the proof hacking, it might be a good idea to review the
   relevant material from the lecture. To help you do that, we suggest that you
   briefly answer each of the questions below. This exercise is not graded, but
   we hope it will help you understand the material better.
   We will also reference this list in office hours to see where you
   might be stuck.

   - What does A * B mean?


   - If A * B holds for a heap, does A necessarily hold for this heap?


   - What does h === g mean?


   - What does [| P |] do? (When is it necessary?)


   - What does p |--> [x;y] mean?


   - What does emp mean?


   - What memory does an empty llist use?


   - How can code detect that an llist is empty?


   - What memory does an llist cons cell use?


   - How can code detect that an llist starts with a cons cell?


   - If an llist starts with a cons cell, which lemma/theorem can we use to learn something about its tail, and what does it tell us?


   - What is the difference between llist' and llist?


   - How do proofs of lemmas about llist use lemmas about llist'?


   Now proving correctness of binary-tree manipulation shouldn't be too bad. Cheers!
*)

(* IMPORTANT NOTE:
   The difficulty of this problem set is scoped assuming you will use the
   tactics included in the Sig file, which are very similar to the ones from
   lecture!

   Trying to attack these proofs from first principles will likely lead to proof
   size spiraling out of control.  *DO NOT* unfold the separation logic
   connectives like `exis`, `===`, etc. — everything would very quickly get very
   confusing.  Our proof only uses `unfold` on `insert`, `lookup`, and `mtree`.

   The main ingredients you should expect to reuse are:
    - [step]: A tactic to choose the right Hoare-logic rule to apply next, when
      your goal is a Hoare triple
    - [cancel]: A tactic to prove an implication between two separation-logic
      assertions, or reduce it to a simpler implication by *cancel*ing matching
      subformulas; before calling [cancel], be sure you have marked [Opaque]
      all of the predicates standing for data structures!  There is an [Opaque
      mtree] command right below for precisely this reason; please put any lemmas
      about [mtree] before it and all program logic proofs after.
    - [heq]: A tactic to reduce a separation-logic assertion equivalence (using
      [===]) to two implications (using [===>])
    - [loop_inv P0 Q0]: A tactic to apply the loop rule, given an invariant
      split in a peculiar way; see above for an example
    - [setoid_rewrite H]: A tactic to rewrite within a separation-logic
      implication, using an equivalence that applies to one of its subterms

   Our solution also has a few direct uses of rules [HtConsequence] and
   [HtFrame], sometimes using the [with] syntax of [apply] to specify values
   for some variables that appear in these rules' statements. In particular,
   you can use [HtConsequence] before [HtFrame] to ensure that the predicate
   that you want to frame out is in the desired syntactic position so that
   [HtFrame] will apply. The [exis_right] lemma will also be handy, as used
   in the example above. *)

(* Space is provided here for additional lemmas about [mtree] and [mtree']. *)



Opaque mtree.
(* ^-- Keep predicates opaque after you've finished proving all the key
* algebraic properties about them, in order for them to work well with
* the [cancel] tactic. *)

Module Impl.

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

Theorem lookup_ok : forall x p,
  {{ mtreep p }}
    lookup x p
  {{ _ ~> mtreep p }}.
Proof.
Admitted.

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
   *the interior of a struct*, in each branch of the last [if]!  This is a fun
   example of the kinds of tricks that can be played in a low-level language,
   and the verification techniques are up to the challenge. *)

Theorem insert_ok : forall x p,
  {{ mtreep p }}
    insert x p
  {{ _ ~> mtreep p }}.
Proof.
Admitted.

End Impl.

(* Our solution also includes a proof that the Hoare triples in this pset
   correspond to the usual operational semantics, but you do not need
   to prove that. *)

Module ImplCorrect : Pset10Sig.S := Impl.



(* Authors:
   - Adam Chlipala
   - Peng Wang
   - Clément Pit-Claudel
   - Dustin Jamner *)
