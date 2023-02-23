(** * 6.512 Formal Reasoning About Programs, Spring 2023 - Pset 3 *)


Require Coq816.
Require Import Frap.Frap ZArith.

(* three-way comparisions, and [cases] support for them *)
Notation Lt := (inleft (left _)) (only parsing).
Notation Eq := (inleft (right _)) (only parsing).
Notation Gt := (inright _) (only parsing).

Definition compare
  : forall n m : Z,
    (sumor (sumbool (n < m) (n = m)) (m < n))%Z.
Proof.
  refine (fun n m => match Zorder.Ztrichotomy_inf n m with
                     | Lt => _
                     | Eq => _
                     | Gt => _
                     end).
  all: auto.
  right; linear_arithmetic.
Defined.

Module Type S.
  Inductive tree {A} :=
  | Leaf
  | Node (l : tree) (d : A) (r : tree).
  Arguments tree : clear implicits.

  Fixpoint flatten {A} (t : tree A) : list A :=
    match t with
    | Leaf => []
    | Node l d r => flatten l ++ d :: flatten r
    end.

  (* 1a) HOFs: id and compose *)

  Definition id {A : Type} (x : A) : A := x.
  Definition compose {A B C : Type} (g : B -> C) (f : A -> B) (x : A) : C := g (f x).

  (*[0.5%]*)
  Parameter compose_id_l : forall (A B : Type) (f : A -> B), compose id f = f.

  (*[0.5%]*)
  Parameter compose_id_r : forall (A B : Type) (f : A -> B), compose f id = f.

  (*[1%]*)
  Parameter compose_assoc :
    forall (A B C D : Type) (f : A -> B) (g : B -> C) (h : C -> D),
      compose h (compose g f) = compose (compose h g) f.

  Fixpoint selfCompose{A: Type}(f: A -> A)(n: nat): A -> A :=
    match n with
    | O => id
    | S n' => compose f (selfCompose f n')
    end.

  Parameter exp : nat -> nat -> nat.
  (*[0.25%]*)
  Parameter test_exp_3_2 : exp 3 2 = 9.
  (*[0.25%]*)
  Parameter test_exp_4_1 : exp 4 1 = 4.
  (*[0.25%]*)
  Parameter test_exp_5_0 : exp 5 0 = 1.
  (*[0.25%]*)
  Parameter test_exp_1_3 : exp 1 3 = 1.

  (* 1b) HOFs: Left inverses *)

  Definition left_inverse{A B: Type}(f: A -> B)(g: B -> A): Prop := compose g f = id.

  (*[1%]*)
  Parameter plus2minus2 : left_inverse (fun x : nat => x + 2) (fun x : nat => x - 2).

  (*[2.5%]*)
  Parameter minus2plus2 : ~ left_inverse (fun x : nat => x - 2) (fun x : nat => x + 2).

  (*[4%]*)
  Parameter left_invertible_injective:
    forall {A} (f g: A -> A),
      left_inverse f g ->
      (forall x y, f x = f y -> x = y).

  (*[0.25%]*)
  Parameter left_inverse_id : forall {A : Type}, left_inverse (@id A) (@id A).

  (*[8%]*)
  Parameter invert_selfCompose :
    forall {A : Type} (f g : A -> A) (n : nat), left_inverse f g -> left_inverse (selfCompose f n) (selfCompose g n).

  (* 2a) bitwise tries *)

  Definition bitwise_trie A := tree (option A).

  Parameter lookup : forall {A : Type}, list bool -> bitwise_trie A -> option A.

  (*[1%]*)
  Parameter lookup_example1 : lookup nil (Node Leaf (None : option nat) Leaf) = None.

  (*[1%]*)
  Parameter lookup_example2 :
    lookup (false :: true :: nil)
           (Node (Node Leaf (Some 2) Leaf) None (Node (Node Leaf (Some 1) Leaf) (Some 3) Leaf)) =
    Some 1.

  (*[1%]*)
  Parameter lookup_empty : forall {A : Type} (k : list bool), lookup k (Leaf : bitwise_trie A) = None.

  Parameter insert : forall {A : Type}, list bool -> option A -> bitwise_trie A -> bitwise_trie A.

  (*[1%]*)
  Parameter insert_example1 : lookup nil (insert nil None (Node Leaf (Some 0) Leaf)) = None.

  (*[1%]*)
  Parameter insert_example2 :
    lookup nil (insert (true :: nil) (Some 2) (Node Leaf (Some 0) Leaf)) = Some 0.

  (*[8%]*)
  Parameter lookup_insert :
    forall {A : Type} (k : list bool) (v : option A) (t : bitwise_trie A), lookup k (insert k v t) = v.

  Parameter merge : forall {A : Type}, bitwise_trie A -> bitwise_trie A -> bitwise_trie A.

  (*[0.25%]*)
  Parameter merge_example1 :
    merge (Node Leaf (Some 1) Leaf) (Node Leaf (Some 2) Leaf) =
    Node Leaf (Some 1) Leaf.

  (*[0.5%]*)
  Parameter merge_example2 :
    merge Leaf (Node Leaf (@None nat) Leaf) = Node Leaf None Leaf.

  (*[0.5%]*)
  Parameter merge_example3 :
    merge (Node Leaf None Leaf) (Node Leaf (Some 2) Leaf) =
    Node Leaf (Some 2) Leaf.

  (*[3%]*)
  Parameter left_lookup_merge : forall {A : Type} (t1 t2 : bitwise_trie A) k v,
      lookup k t1 = Some v ->
      lookup k (merge t1 t2) = Some v.

  (*[4%]*)
  Parameter lookup_merge_None : forall {A : Type} (t1 t2 : bitwise_trie A) k,
      lookup k (merge t1 t2) = None ->
      lookup k t1 = None /\ lookup k t2 = None.

  (*[5%]*)
  Parameter merge_selfCompose : forall {A : Type} n (t1 t2 : bitwise_trie A),
      0 < n ->
      selfCompose (merge t1) n t2 = merge t1 t2.

  Parameter mirror : forall {A : Type}, tree A -> tree A.

  (*[1%]*)
  Parameter mirror_test1 :
    mirror (Node Leaf 1 (Node Leaf 2 (Node Leaf 3 Leaf))) =
    Node (Node (Node Leaf 3 Leaf) 2 Leaf) 1 Leaf.

  (*[0.5%]*)
  Parameter mirror_mirror_id : forall {A : Type} (t : tree A),
      mirror (mirror t) = t.

  (*[3%]*)
  Parameter flatten_mirror_rev : forall {A : Type} (t : tree A),
      flatten (mirror t) = rev (flatten t).
    
  (* 2b) HOFs: tree_map *)

  Parameter tree_map : forall {A B : Type}, (A -> B) -> tree A -> tree B.

  (*[1%]*)
  Parameter tree_map_example :
    tree_map (fun x : nat => x + 1) (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 (Node Leaf 4 Leaf))) =
    Node (Node Leaf 2 Leaf) 3 (Node Leaf 4 (Node Leaf 5 Leaf)).

  (*[8%]*)
  Parameter tree_map_flatten :
    forall (A B : Type) (f : A -> B) (t : tree A), flatten (tree_map f t) = List.map f (flatten t).

  Fixpoint tree_forall {A} (P: A -> Prop) (tr: tree A) :=
    match tr with
    | Leaf => True
    | Node l d r => tree_forall P l /\ P d /\ tree_forall P r
    end.

  Parameter tree_exists : forall {A: Type}, (A -> Prop) -> tree A -> Prop.

  (*[0.5%]*)
  Parameter tree_exists_Leaf :
    forall (A : Type) (P : A -> Prop), ~ tree_exists P Leaf.
  (*[3%]*)
  Parameter tree_forall_exists :
    forall (A : Type) (P : A -> Prop) (tr : tree A),
      tr <> Leaf -> tree_forall P tr -> tree_exists P tr.

  (*[2%]*)
  (* Explain what tree_forall_sound means *)

  (*[3%]*)
  Parameter tree_forall_sound :
    forall (A : Type) (P : A -> Prop) (tr : tree A),
      tree_forall P tr -> forall d : A, tree_exists (fun d' : A => d' = d) tr -> P d.

  (* 2d) Binary search trees *)

  Local Open Scope Z_scope.

  Fixpoint bst (tr : tree Z) (s : Z -> Prop) :=
    match tr with
    | Leaf => forall x, not (s x) (* s is empty set *)
    | Node l d r =>
      s d /\
      bst l (fun x => s x /\ x < d) /\
      bst r (fun x => s x /\ d < x)
    end.

  (*[3%]*)
  Parameter bst_implies :
    forall (tr : tree Z) (s : Z -> Prop), bst tr s -> tree_forall s tr.

  (*[3%]*)
  Parameter bst_node_ordered :
    forall (l : tree Z) (d : Z) (r : tree Z) (s : Z -> Prop),
      bst (Node l d r) s ->
      tree_forall (fun x : Z => x < d) l /\ tree_forall (fun x : Z => d < x) r.

  (*[6%]*)
  Parameter bst_iff :
    forall (tr : tree Z) (P Q : Z -> Prop),
      bst tr P -> (forall x : Z, P x <-> Q x) -> bst tr Q.

  (*[8%]*)
  Parameter bst_strict_monotone_increasing : forall tr P Q f g,
      bst tr P ->
      left_inverse g f ->
      (forall x y, x < y <-> f x < f y) ->
      (forall x, P x <-> Q (f x)) ->
      bst (tree_map f tr) Q.

  (*[8%]*)
  Parameter bst_strict_monotone_decreasing_mirror : forall tr P Q f g,
      bst tr P ->
      left_inverse g f ->
      (forall x y, x < y <-> f x > f y) ->
      (forall x, P x <-> Q (f x)) ->
      bst (mirror (tree_map f tr)) Q.
  
  Fixpoint bst_member (a: Z) (tr: tree Z) : bool :=
    match tr with
    | Leaf => false
    | Node lt v rt =>
      match compare a v with
      | Lt => bst_member a lt
      | Eq => true
      | Gt => bst_member a rt
      end
    end.

  (*[5%]*)
  Parameter member_bst :
    forall (tr : tree Z) (s : Z -> Prop) (a : Z),
      bst tr s -> bst_member a tr = true <-> s a.
End S.

(* Here's a technical note on why this pset overrides a Frap tactic.
   There's no need to understand this at all.

   The "simplify" tactic provided by the Frap library is not quite suitable for this
   pset, because it does "autorewrite with core in *" (which we commented out below),
   and there's a Hint in Coq.Program.Combinators

        Hint Rewrite <- @compose_assoc : core.

   which causes "autorewrite with core in *." to have the
   same effect as

   rewrite <-? Combinators.compose_assoc.

   and apparently, rewrite does not just syntactic matching,
   but matching modulo unification, so it will replace
   our "compose" by "Basics.compose", and rewrite using
   associativity of "compose" as many times as it can.
   It's confusing to have "Basics.compose" appear in our goals,
   and rewriting with associativity is something we want to teach in this
   pset, so we redefine "simplify" to not use "autorewrite": *)
Ltac simplify ::=
  repeat (unifyTails; pose proof I); repeat match goal with
                                            | H:True |- _ => clear H
                                            end;
   repeat progress (simpl in *; intros(*; try autorewrite with core in * *); simpl_maps);
   repeat normalize_set || doSubtract.

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
TIPS: A few things that might be helpful keep in mind as you work on pset 3
===========================================================================
|*)

(*|
You can unfold "not"
====================

"~ P" in Coq stands for "not P", and is defined as "P -> False", so to prove "~ P", it sometimes helps to do "unfold not. simplify."

The propositional tactic will unfold all instances of `not` that it finds.

Behavior of simplify on fixpoints
=================================

Some students have been running into a situation where [simplify] doesn't behave as they expect. This hint will explore the behavior of [simplify] on [Fixpoint] definitions.

Here's a simple [Fixpoint] definition [always_true : Z -> Z] that deserves its name:
|*)

Fixpoint always_true (x : Z) {struct x} : bool := true.

(*|
Note that the syntax [{struct x}] is a hint to Coq that our definition structurally recurses on the [x] argument (the only argument). Of course, there isn't any recursion at all here! So indeed, every recursive call (of which there are none) passes a structurally smaller [x] argument to [always_true].

Now, suppose we try to prove the following theorem:
|*)

Theorem always_true_ok : forall x : Z,
    always_true x = true.
Proof.
  simplify. (* only introduces [x], without doing simplification *)
  Fail equality. (* Fails! *)

(*|
That's surprising, isn't it?

Here's a key fact to understanding how [simplify] works on [Fixpoint] definitions: [simplify] only reduces the application of [Fixpoint] definition when the argument on which it structurally recurses (according to Coq) is in the form of a constructor application.

That's a mouthful. A trivial way to remedy this is to use [cases] on the argument for which the fixpoint is known to be structurally recursive:
|*)

  cases x; equality.
Qed.


Local Close Scope Z_scope.

(*|
Another possible solution for our example here is to just define [always_true] as a [Definition], rather than a [Fixpoint]; then [simplify] will work as expected.

In the problem set, you may run into a [Fixpoint] that can be viewed as structurally recursive on two different arguments, and by using the "{struct}" syntax seen above, you can choose which - one may be more convenient with respect to [simplify]'s behavior as noted in the bolded statement above.

Finally, since Coq usually infers which argument a fixpoint is structurally decreasing on, you can run [Print f] for any fixpoint [f] to see which argument Coq chose.
|*)


(*|
HINTS: A few hints to help you if you get stuck on certain 
       problems in Pset 3.
       Beware! Don't read further if you don't want spoilers!
=============================================================
|*)






































(*|
HINT 1: Specializing function equalities
========================================

You may find it useful to prove the following lemma:

Lemma specialize_fun_eq : forall {A B: Type},
    forall (f g: A -> B), forall x,
        f = g -> f x = g x.
Admitted.
|*)






































(*|
HINT 2: Main insight needed to prove invert_selfCompose
=======================================================

Do not unfold `compose` to prove invert_selfCompose.  Instead, use the following lemma:

Lemma selfCompose_succ_alt{A: Type}: forall (g: A -> A) (n: nat),
    g ∘ selfCompose g n = selfCompose g n ∘ g.
Admitted.
|*)




































(*|
HINT 3: A function to build a trie with only one entry
======================================================

We found the following function helpful to define insert:

Fixpoint build_singleton {A} (k : list bool) (v : option A) : bitwise_trie A :=
  match k with
  | [] => Node Leaf v Leaf
  | x :: k' => let branch := build_singleton k' v in
               if x then Node branch None Leaf
               else Node Leaf None branch
  end.
|*)







































(*|
HINT 4: Helper lemma for lookup_insert
======================================

The following lemma helps with lookup_insert:

Lemma lookup_build_singleton {A} (k : list bool) (v : option A)
  : lookup k (build_singleton k v) = v.
Admitted.
|*)







































(*|
HINT 5 : Proving merge_selfCompose
================================

You may find the following lemmas helpful:

Lemma merge_id {A} : forall (t1 : bitwise_trie A),
    merge t1 t1 = t1.
Admitted.

Lemma merge_idempotent {A} : forall (t1 t2 : bitwise_trie A),
    merge t1 (merge t1 t2) = merge t1 t2.
Admitted.

|*)






































(*|
HINT 6: Helper lemma for tree_map_flatten
=========================================

For tree_map_flatten, use the following intermediate lemma:

Lemma map_append : forall {A B : Type} (f : A -> B) (xs ys : list A),
    map f (xs ++ ys) = map f xs ++ map f ys.
Admitted.
|*)





































(*|
HINT 7: Proving bst_implies
===========================

The following lemma is one way to prove bst_implies:

Lemma tree_forall_implies:
  forall tr (P Q: Z -> Prop),
    tree_forall P tr ->
    (forall x, P x -> Q x) ->
    tree_forall Q tr.
Admitted.
|*)
