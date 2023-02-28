(** * 6.512 Formal Reasoning About Programs, Spring 2023 - Pset 4 *)


Require Coq816.
Require Import Frap.

Notation t := nat.

Inductive tree :=
| Leaf (* an empty tree *)
| Node (d : t) (l r : tree).

Notation compare := Compare_dec.lt_eq_lt_dec.
Notation Lt := (inleft (left _)) (only parsing).
Notation Eq := (inleft (right _)) (only parsing).
Notation Gt := (inright _) (only parsing).

Module Type S.
  Definition Singleton (v: t) := Node v Leaf Leaf.
  Fixpoint bst (tr : tree) (s : t -> Prop) : Prop :=
    match tr with
    | Leaf => forall x, not (s x)
    | Node d l r =>
        s d /\
        bst l (fun x => s x /\ x < d) /\
        bst r (fun x => s x /\ d < x)
    end.

  Parameter rotate : tree -> tree.

  (*[10%]*) Axiom bst_rotate : forall T s (H : bst T s), bst (rotate T) s.

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

  (*[40%]*) Axiom bst_insert :
    forall tr s a,
      bst tr s ->
      bst (insert a tr) (fun x => s x \/ x = a).

  (*[50%]*) Axiom bst_delete :
    forall tr s a, bst tr s ->
              bst (delete a tr) (fun x => s x /\ x <> a).
End S.

(* three-way comparisions and [cases] support for them *)
Ltac cases E :=
  (is_var E; destruct E) ||
    match type of E with
    | sumor (sumbool _ _) _ => destruct E as [[]|]
    | {_} + {_} => destruct E
    | _ => let Heq := fresh "Heq" in
           destruct E eqn:Heq
    end;
   repeat
    match goal with
    | H:_ = left _ |- _ => clear H
    | H:_ = right _ |- _ => clear H
    | H:_ = inleft _ |- _ => clear H
    | H:_ = inright _ |- _ => clear H
    end.

(*|
TIPS: A few things that might be helpful keep in mind as you work on pset 4
===========================================================================
 *)

(*|
Paper proof and reasoning will help
===================================
Problem set 4 is a lot less guided than previous assignments: you will need to prove multiple lemmas for each of the BST theorems, and we did not give the exact statement of each lemma.  Think about the proofs on paper, take each proof slowly, and do not hesitate to prove useful intermediate results as separate lemmas.

And if you get stuck, come to office hours!
 *)

(*|
Take advantage of propositional
===============================
When writing specifications, you can enable [propositional] to prove more stuff
by sticking to a minimal convention about which comparison operators you use.
We chose to pick [x<y] over [y>x] and [not (y<x)] over [x<=y]. This helps just
a little.
*)

(*|
HINTS: A few hints to help you if you get stuck on certain 
       problems in Pset 4.
       Beware! Don't read further if you don't want spoilers!
=============================================================
|*)







































(*|
HINT 1: 
=======
Definition rotR (T : tree) :=
  match T with
  | Node t L R =>
      match L with
       | Node l A B => Node l A (Node t B R)
       | _ => T
      end
  | _ => T
  end.

Lemma bst_rotR T S (H : bst T S) : bst (rotR T) S.
Proof.
  cases T; propositional.
  cases T1; propositional.
  simplify; propositional;
    use_bst_iff_assumption; propositional; linear_arithmetic.
Qed.

Definition rotL (T : tree) :=
  match T with
  | Node t A R =>
      match R with
       | Node r B X => Node r (Node t A B) X
       | _ => T
      end
  | _ => T
  end.

Lemma bst_rotL T S (H : bst T S) : bst (rotL T) S.
Proof.
  cases T; propositional.
  cases T2; propositional.
  simplify; propositional.
  { eapply bst_iff.
    { eassumption. }
    { propositional.
      linear_arithmetic. } }
  { eapply bst_iff; try eassumption. propositional; linear_arithmetic. }
  { eapply bst_iff; try eassumption. propositional; linear_arithmetic. }
Qed.
*)






































(*|
HINT 2:
=======
Consider [cases (rightmost tr2)] or [cases (is_leaf tr2)] instead of [cases
tr2]. Not breaking apart the tree itself can avoid a mess.
*)





































(*|
HINT 3:
=======
A convenient way to specify "the largest element in this set" is to say that
all elements in this set are no larger than the given element.
*)





































(*|
HINT 4:
=======
merge_ordered needs a rather strong precondition. It does not work correctly
for merging just any two trees. However, it is called in a rather specific
scenario. (And it is feasible to prove its use by inlining it, but we found a
separate specification helpful.) Why is it bad to call merge_ordered [3,4] [1,2]?
*)





































(*|
HINT 5:
=======
Our proof, if avoiding eapply, contains a couple of long apply-with invocations, for example:
apply bst_iff with (P:=let S := (fun x : t => S x /\ d < x) in (fun x : t => S x /\ x < rm)).
*)
