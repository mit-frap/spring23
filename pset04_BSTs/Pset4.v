(** * 6.512 Formal Reasoning About Programs, Spring 2023 - Pset 4 *)

(** * Correctness of Binary Search Trees (BSTs) *)

(* This week we'll continue proving the correctness of a binary search tree implementation.
 * BSTs are a famous data structure for finite sets, allowing fast (log-time)
 * lookup, insertion, and deletion of items. (We omit the rebalancing heuristics
 * needed to achieve worst-case log-time operations, but you will prove the
 * correctness of rotation operations these heuristics use to modify the tree.)
 * In this problem set, we show that insertion and deletion functions are
 * correctly defined by relating them to operations on functional sets. *)

(* Since almost all of this assignment's points come from two proofs,
 * make sure to break out any useful facts you come across into helper lemmas
 * to maximize your partial credit in the case that you don't finish one of the proofs. *)

(* As usual, a set of spoiler-containing hints to help you along when you 
 * get stuck with certain pset questions has been provided at the bottom of 
 * the signature file! *)

Require Import Frap Pset4.Pset4Sig.

(* We will study binary trees of natural numbers only for convenience.
   Almost everything here would also work with an arbitrary type
   [t], but with [nat] you can use [linear_arithmetic] to prove
   goals about ordering of multiple elements (e.g., transitivity). *)
Local Notation t := nat.

Module Impl.
  (* Trees are an inductive structure, where [Leaf] doesn't have any items,
   * whereas [Node] has an item and two subtrees. Note that a [tree] can
   * contain nodes in arbitrary order, so not all [tree]s are valid binary
   * search trees. *)

  (* (* Imported from Sig file: *)
  Inductive tree :=
  | Leaf (* an empty tree *)
  | Node (d : t) (l r : tree).
  *)
  (* Then a singleton is just a node without subtrees. *)
  Definition Singleton (v: t) := Node v Leaf Leaf.

  (* [bst] relates a well-formed binary search tree to the set of elements it
     contains. Note that invalid trees with misordered elements are not valid
     representations of any set. All operations on a binary tree are specified
     in terms of how they affect the set that the tree represents. That
     set is encoded as function that takes a [t] and returns the proposition "[t]
     is in this set". *)
  Fixpoint bst (tr : tree) (s : t -> Prop) :=
    match tr with
    | Leaf => forall x, not (s x) (* s is empty set *)
    | Node d l r =>
        s d /\
        bst l (fun x => s x /\ x < d) /\
        bst r (fun x => s x /\ d < x)
    end.

  (* [member] computes whether [a] is in [tr], but to do so it *relies* on the
     [bst] property -- if [tr] is not a valid binary search tree, [member]
     will (and should, for performance) give arbitrarily incorrect answers. *)
  Fixpoint member (a: t) (tr: tree) : bool :=
    match tr with
    | Leaf => false
    | Node v lt rt =>
      match compare a v with
      | Lt => member a lt
      | Eq => true
      | Gt => member a rt
      end
    end.

  (* Here is a typical insertion routine for BSTs.
   * From a given value, we recursively compare the value with items in
   * the tree from the root, until we find a leaf whose place the new value can take. *)
  Fixpoint insert (a: t) (tr: tree) : tree :=
    match tr with
    | Leaf => Singleton a
    | Node v lt rt =>
      match compare a v with
      | Lt => Node v (insert a lt) rt
      | Eq => tr
      | Gt => Node v lt (insert a rt)
      end
    end.

  (* Helper functions for [delete] below. The *main task* in this pset
     is to understand, specify, and prove these helpers. *)
  Fixpoint rightmost (tr: tree) : option t :=
    match tr with
    | Leaf => None
    | Node v _ rt =>
      match rightmost rt with
      | None => Some v
      | r => r
      end
    end.
  Definition is_leaf (tr : tree) : bool :=
    match tr with Leaf => true | _ => false end.
  Fixpoint delete_rightmost (tr: tree) : tree :=
    match tr with
    | Leaf => Leaf
    | Node v lt rt =>
      if is_leaf rt
      then lt
      else Node v lt (delete_rightmost rt)
    end.
  Definition merge_ordered lt rt :=
    match rightmost lt with
    | Some rv => Node rv (delete_rightmost lt) rt
    | None => rt
    end.

  (* [delete] searches for an element by its value and removes it if it is found.
     Removing an element from a leaf is degenerate (nothing to do), and
     removing the value from a node with no other children (both Leaf) can be done
     by replacing the node itself with a Leaf. Deleting a non-leaf node is
     substantially trickier because the type of [tree] does not allow for a Node
     with two subtrees but no value -- merging two trees is nontrivial. The
     implementation here removes the value anyway and then moves the rightmost
     node of the left subtree up to replace the removed value. This is equivalent
     to using rotations to move the value to be removed into leaf position and
     removing it there. *)
  Fixpoint delete (a: t) (tr: tree) : tree :=
    match tr with
    | Leaf => Leaf
    | Node v lt rt =>
      match compare a v with
      | Lt => Node v (delete a lt) rt
      | Eq => merge_ordered lt rt
      | Gt => Node v lt (delete a rt)
      end
    end.

  (* Here is a lemma that you will almost definitely want to use. *)
  Example bst_iff : forall tr P Q, bst tr P -> (forall x, P x <-> Q x) -> bst tr Q.
  Proof.
    induct tr; simplify.
    { rewrite <- H0. apply H with (x:=x). }
    rewrite H0 in H.
    propositional.
    { apply IHtr1 with (P:=(fun x : t => (fun d => P x /\ x < d) d));
        propositional; cycle 1.
      { rewrite H0; trivial. }
      { rewrite <-H0; trivial. } }
    { apply IHtr2 with (P:=(fun x : t => (fun d => P x /\ d < x) d));
      propositional; cycle 2.
      { rewrite <-H0; trivial. }
      { rewrite H0; trivial. } }
  Qed.

  (* You may want to call these tactics to use the previous lemma. *)
  (* They are just a means to save some typing of [apply ... with]. *)
  Ltac use_bst_iff known_bst :=
    lazymatch type of known_bst with
    | bst ?tree2 ?set2 =>
        lazymatch goal with
        | |- bst ?tree1 ?set1 =>
            apply bst_iff with (P:=set2) (Q := set1);
            lazymatch goal with
            |- bst tree2 set2 => apply known_bst
            | _ => idtac
            end
        end
    end.

  Ltac use_bst_iff_assumption :=
    match goal with
    | H : bst ?t _ |- bst ?t _ =>
      use_bst_iff H
    end.

  (* If you are comfortable with it, [eapply bst_iff] followed by careful
   * application of other [bst] facts (e.g., inductive hypotheses) can
   * save typing in some places where this tactic does not apply, though
   * keep in mind that forcing an incorrect choice for a ?unification
   * variable can make the goal false. *)

  (* It may also be useful to know that you can switch to proving [False] by
   * calling [exfalso]. This, for example, enables you to apply lemmas that end in
   * [-> False]. Of course, only do this if the hypotheses are contradictory. *)

  (* Other tactics used in our solution: apply, apply with, apply with in
   * (including multiple "with" clauses like in [use_bst_iff]), cases, propositional,
     linear_arithmetic, simplify, trivial, try, induct, equality, rewrite, assert. *)

  (* Warm-up exercise: rebalancing rotations *)

  (* Transcribe and prove one of the two rotations shown in [rotation1.svg] and [rotation2.svg].
     The AA-tree rebalancing algorithm applies these only if the annotations of relevant
     subtrees are in violation of a performance-critical invariant, but the rotations
     themselves are correct regardless. (These are straight from
     https://en.wikipedia.org/wiki/AA_tree#Balancing_rotations.) *)
  (* Each one can be written as a simple non-recursive definition
     containing two "match" expressions that returns the original
     tree in cases where the expected structure is not present. *)
  
  (* HINT 1 (see Pset4Sig.v) *)
  Definition rotate (T : tree) : tree.
  Admitted.

  Lemma bst_rotate T s (H : bst T s) : bst (rotate T) s.
  Admitted.

  (* There is a hint in the signature file that completely gives away the proofs
   * of these rotations. We recommend you study that code after completing this
   * exercise to see how we did it, maybe picking up a trick or two to use below. *)

  Lemma bst_insert : forall tr s a, bst tr s ->
    bst (insert a tr) (fun x => s x \/ x = a).
  Proof.
  Admitted.

  (* To prove [bst_delete], you will need to write specifications for its helper
     functions, find suitable statements for proving correctness by induction, and use
     proofs of some helper functions in proofs of other helper functions. The hints
     in the signature file provide examples and guidance but no longer ready-to-prove
     lemma statements. For time-planning purposes: you are not halfway done yet.
     (The Sig file also has a rough point allocation between problems.)

     It is up to you whether to use one lemma per function, multiple lemmas per
     function, or (when applicable) one lemma per multiple functions. However,
     the lemmas you prove about one function need to specify everything a caller
     would need to know about this function. *)

  (* HINT 2-5 (see Pset4Sig.v) *)
  Lemma bst_delete : forall tr s a, bst tr s ->
    bst (delete a tr) (fun x => s x /\ x <> a).
  Admitted.

  (* Great job! Now you have proven all tree-structure-manipulating operations
     necessary to implement a balanced binary search tree. Rebalancing heuristics
     that achieve worst-case-logarithmic running time maintain annotations on
     nodes of the tree (and decide to rebalance based on these). The implementation
     here omits them, but as the rotation operations are correct regardless of
     the annotations, any way of calling them from heuristic code would result in a
     functionally correct binary tree. *)
End Impl.

Module ImplCorrect : Pset4Sig.S := Impl.

(* Authors:
 * Joonwon Choi
 * Adam Chlipala
 * Benjamin Sherman
 * Andres Erbsen
 * Amanda Liu
 *)
