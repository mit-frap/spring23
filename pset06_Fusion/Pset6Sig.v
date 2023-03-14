(** * 6.512 Formal Reasoning About Programs, Spring 2023 - Pset 6 *)

Require Coq816.
Require Import Frap.Frap.


(* The `swap` function defined here switches the elements in a list at positions `n1` and `n2`.
     Since it is not the focus of this assignment, we have provided all of the theorems necessary
     to work with it. You should not unfold `swap` and should only use existing theorems
     to reason about it.

   You can look at these proofs if you would like, but most of them will not be similar to
   the proofs you have to complete.
 *)
Module Swap.

  Local Definition swap' {A} (n1 n2 : nat) (l : list A) default :=
    firstn n1 l ++ (nth n2 l default)::(firstn (n2 - S n1) (skipn (S n1) l))
      ++ (nth n1 l default)::(skipn (S n2) l).


  (* Assumption: n1 < n2 < length l *)
  (* uses some tricks to avoid a default element and to make lemmas easier to use *)
  Definition swap {A} (n1 n2 : nat) (l : list A) :=
    if (Nat.leb n2 n1) || (Nat.leb (length l) n2) then l
    else match l with
         | [] => []
         | a::_ => swap' n1 n2 l a
         end.


  Lemma Forall2_nth A B R l1 l2 (a:A) (b:B)
    : Forall2 R l1 l2 ->
      forall n,
        n < length l2 ->
        R (nth n l1 a) (nth n l2 b).
  Proof.
    induct 1;
      simplify;
      try linear_arithmetic;
      auto.
    cases n;
      simplify; eauto.
    apply IHForall2;
      try linear_arithmetic;
      auto.
  Qed.

  Local Hint Constructors Forall2 : core.

  Lemma Forall2_ext A B (R : A -> B -> Prop)
    : forall l1 l2,
      (forall n a b, n < length l2 -> R (nth n l1 a) (nth n l2 b)) ->
      length l1 = length l2 ->
      Forall2 R l1 l2.
  Proof.
    induct l1;
      simplify;
      cases l2;
      simplify;
      auto;
      try linear_arithmetic.
    invert H0.
    pose proof (fun n => H (S n)).
    pose proof (H 0).
    clear H.
    simplify.
    first_order.
    constructor; eauto.
    {
      apply H1; auto; linear_arithmetic.
    }
    {
      apply IHl1; auto.
      simplify; apply H0; linear_arithmetic.
    }
  Qed.


  Local Lemma length_swap' A (l : list A) n1 n2 a
    : n1 < n2 ->
      n2 < length l ->
      length (swap' n1 n2 l a) = length l.
  Proof.
    unfold swap'.
    intros.
    repeat (rewrite ?app_length, ?firstn_length, ?skipn_length; cbn [length]).
    rewrite Nat.min_l by linear_arithmetic.
    rewrite Nat.min_l by linear_arithmetic.
    linear_arithmetic.
  Qed.  

  Lemma length_swap A (l : list A) n1 n2
    : length (swap n1 n2 l) = length l.
  Proof.
    unfold swap.
    destruct (Nat.leb_spec n2 n1);
      simplify; auto.
    destruct (Nat.leb_spec (length l) n2);
      simplify; auto.
    cases l; auto.
    apply length_swap'; auto.
  Qed.
  Global Hint Rewrite length_swap : core.


  Lemma Forall2_length A B (R: A -> B -> Prop) l1 l2
    : Forall2 R l1 l2 ->
      length l1 = length l2.
  Proof.
    induct 1; simplify; eauto.
  Qed.
  Global Hint Resolve Forall2_length : core.


  Lemma Forall2_app A B (R : A -> B -> Prop) l11 l12 l21 l22
    : Forall2 R l11 l12 ->
      Forall2 R l21 l22 ->
      Forall2 R (l11++l21) (l12++l22).
  Proof.
    induct 1; simplify; eauto.
  Qed.

  Lemma Forall2_firstn A B (R : A -> B -> Prop) l1 l2
    : Forall2 R l1 l2 ->
      forall n,
        Forall2 R (firstn n l1) (firstn n l2).
  Proof.
    induct 1; simplify; cases n; simplify; eauto.
  Qed.
  
  Lemma Forall2_skipn A B (R : A -> B -> Prop) l1 l2
    : Forall2 R l1 l2 ->
      forall n,
        Forall2 R (skipn n l1) (skipn n l2).
  Proof.
    induct 1; simplify; cases n; simplify; eauto.
  Qed.  

  Local Lemma Forall2_swap' A B (R : A -> B -> Prop) l1 l2 a b
    : Forall2 R l1 l2 ->
      forall n1 n2,
        n1 < n2 ->
        n2 < length l2 ->
        Forall2 R (swap' n1 n2 l1 a) (swap' n1 n2 l2 b).
  Proof.
    unfold swap'.
    intros.
    repeat first
      [ assumption
      | apply Forall2_app
      | apply Forall2_firstn
      | apply Forall2_skipn
      | apply List.Forall2_cons
      | apply Forall2_nth].
    linear_arithmetic.
  Qed.  

  Lemma Forall2_swap A B (R : A -> B -> Prop) l1 l2
    : Forall2 R l1 l2 ->
      forall n1 n2,
        Forall2 R (swap n1 n2 l1) (swap n1 n2 l2).
  Proof.
    intros.
    unfold swap.
    destruct (Nat.leb_spec n2 n1);
      simplify; auto.
    pose proof (Forall2_length _ _ _ _ _ H) as Hlen;
      rewrite Hlen.
    destruct (Nat.leb_spec (length l2) n2);
      simplify; auto.
    cases l1; cases l2; simplify; try linear_arithmetic.
    apply Forall2_swap'; simplify; propositional.
  Qed.
  Global Hint Resolve Forall2_swap : core.


  Local Lemma app_swap'1
    : forall (A : Type) (l l' : list A) (n1 n2 : nat) a,
      n1 < n2 -> n2 < Datatypes.length l -> swap' n1 n2 (l ++ l') a = (swap' n1 n2 l a)++l'.
  Proof.
    intros.
    unfold swap'.
    rewrite !firstn_app, !skipn_app, !app_nth1 by linear_arithmetic.
    repeat (replace (_ - length l) with 0 by linear_arithmetic).
    repeat change (firstn 0 _) with (@nil A).
    repeat change (skipn 0 ?l) with l.
    rewrite !app_nil_r.
    rewrite <- !app_assoc.
    rewrite !firstn_app.
    rewrite skipn_length.
    replace (n2 - S n1 - (Datatypes.length l - S n1)) with 0 by linear_arithmetic.
    repeat change (firstn 0 _) with (@nil A).
    rewrite !app_nil_r.
    
    cbn [app].
    rewrite <- !app_assoc.
    reflexivity.
  Qed.
  
  Lemma app_swap1
    : forall (A : Type) (l l' : list A) (n1 n2 : nat),
      n1 < n2 -> n2 < Datatypes.length l -> 
      swap n1 n2 (l ++ l') = (swap n1 n2 l)++l'.
  Proof.
    simplify.
    unfold swap. 
    destruct (Nat.leb_spec n2 n1);
      simplify; auto.
    destruct (Nat.leb_spec (length l) n2);
      simplify; try linear_arithmetic.
    destruct (Nat.leb_spec (length (l ++ l')) n2);
      simplify; rewrite app_length in *; try linear_arithmetic.
    cases l; simplify; try linear_arithmetic.
    change (a :: l ++ l') with ((a::l)++l').
    apply app_swap'1; auto.
  Qed.

End Swap.

Arguments Swap.swap : simpl never.
Import Swap.

Module Type S.

(*
  We'll be working with a small stack-based language in this lab, where we
  interpret a program as a transformation from an input stack to an output stack,
  primarily done by pushing and popping values on and off the stack.
 *)

Inductive stack_val :=
| val_lit (n : nat)
| val_nil
| val_cons (v1 v2 : stack_val).

Inductive ty : Set :=
| ty_nat
| ty_list (t : ty).

Inductive val_well_typed : stack_val -> ty -> Prop :=
| val_lit_wt n : val_well_typed (val_lit n) ty_nat
| val_nil_wt t : val_well_typed val_nil (ty_list t)
| val_cons_wt t v1 v2
  : val_well_typed v1 t ->
      val_well_typed v2 (ty_list t) ->
      val_well_typed (val_cons v1 v2) (ty_list t).

Local Notation stack_well_typed := (Forall2 val_well_typed).

Definition stack_unop f (s : list stack_val) :=
  match s with
  | a::s' => (f a)::s'
  | _ => (*this case never happens on well-typed programs*) s
  end.

Definition stack_binop f (s : list stack_val) :=
  match s with
  | a::b::s' => (f a b)::s'
  | _ => (*this case never happens on well-typed programs*) s
  end.

Definition stack_pop (s : list stack_val) :=
  match s with
  | a::s => (a,s)
  | _ => (*this case never happens on well-typed programs*) (val_lit 0, [])
  end.

Definition stack_peek (s : list stack_val) :=
  match s with
  | a::_ => a
  | _ => (*this case never happens on well-typed programs*) val_lit 0
  end.

Fixpoint val_app v1 v2 :=
  match v1 with
  | val_nil => v2
  | val_cons v11 v12 => val_cons v11 (val_app v12 v2)
  | val_lit _ => (*this case never happens on well-typed programs*) val_lit 0
  end.

Fixpoint val_flatmap (f : stack_val -> stack_val) v :=
  match v with
  | val_nil => val_nil
  | val_cons v1 v2 =>
      val_app (f v1) (val_flatmap f v2)
  | val_lit _ => val_lit 0
  end.

Fixpoint val_reduce (f : stack_val -> stack_val -> stack_val) vl vacc :=
  match vl with
  | val_nil => vacc
  | val_cons v1 v2 =>
      val_reduce f v2 (f vacc v1)
  | val_lit _ => val_lit 0
  end.

(*[4%]*)
Parameter val_flatmap_sound
  : forall t1 t2 f l,
    (forall x, val_well_typed x t1 -> val_well_typed (f x) (ty_list t2)) ->
    val_well_typed l (ty_list t1) ->
    val_well_typed (val_flatmap f l) (ty_list t2).

Inductive stack_cmd :=
| cmd_atom (v : stack_val) (c : stack_cmd)
| cmd_unop (f : stack_val -> stack_val) (c : stack_cmd)
| cmd_binop (f : stack_val -> stack_val -> stack_val) (c : stack_cmd)
| cmd_swap (n1 n2 : nat) (c : stack_cmd)
| cmd_flatmap (cf : stack_cmd) (c : stack_cmd)
| cmd_reduce (cf : stack_cmd) (c : stack_cmd)
| cmd_skip.


Inductive cmd_well_typed : list ty -> stack_cmd -> list ty -> Prop :=
| cmd_atom_wt v t S c S'
  : val_well_typed v t ->
    cmd_well_typed (t::S) c S' ->
    cmd_well_typed S (cmd_atom v c) S'
| cmd_unop_wt f t1 t2 S c S'
  : (forall v, val_well_typed v t1 -> val_well_typed (f v) t2) ->
    cmd_well_typed (t2::S) c S' ->
    cmd_well_typed (t1::S) (cmd_unop f c) S'
| cmd_binop_wt f t1 t2 t3 S c S'
  : (forall v1 v2, val_well_typed v1 t1 ->
                   val_well_typed v2 t2 ->
                   val_well_typed (f v1 v2) t3) ->
    cmd_well_typed (t3::S) c S' ->
    cmd_well_typed (t1::t2::S) (cmd_binop f c) S'
| cmd_swap_wt S n1 n2 c S'
  : n1 < n2 ->
    n2 < length S ->
    cmd_well_typed (swap n1 n2 S) c S' ->
    cmd_well_typed S (cmd_swap n1 n2 c) S'
| cmd_flatmap_wt S (cf : stack_cmd) t1 t2 c S'
  : cmd_well_typed ((ty_list t2)::S) c S' ->
    cmd_well_typed [t1] cf [ty_list t2] ->
    cmd_well_typed ((ty_list t1)::S) (cmd_flatmap cf c) S'
| cmd_reduce_wt S (cf : stack_cmd) t t_acc c S'
  : cmd_well_typed (t_acc::S) c S' ->
    cmd_well_typed [t; t_acc] cf [t_acc] ->
    cmd_well_typed ((ty_list t)::t_acc::S) (cmd_reduce cf c) S'
| cmd_skip_wt S
  : cmd_well_typed S (cmd_skip) S.


Fixpoint interp_cmd (c : stack_cmd) (s : list stack_val) : list stack_val :=
  match c with
  | cmd_atom v c' => interp_cmd c' (v::s)
  | cmd_unop f c' => interp_cmd c' (stack_unop f s)
  | cmd_binop f c' => interp_cmd c' (stack_binop f s)
  | cmd_swap n1 n2 c' => interp_cmd c' (swap n1 n2 s)
  | cmd_flatmap cf c' =>
      let (l,s1) := stack_pop s in
      let out := val_flatmap (fun x => stack_peek (interp_cmd cf [x])) l in
      interp_cmd c' (out::s1)
  | cmd_reduce cf c' => 
      let (l,s) := stack_pop s in
      let (acc,s) := stack_pop s in
      let out := val_reduce (fun acc x => stack_peek (interp_cmd cf [x;acc])) l acc in
      interp_cmd c' (out::s)
  | cmd_skip => s
  end.

(*[4%]*)
Parameter interp_sound
  : forall S c S',
    cmd_well_typed S c S' ->
    forall s, stack_well_typed s S ->
              stack_well_typed (interp_cmd c s) S'.  

(*[2%]*)
Parameter cmd_seq : stack_cmd -> stack_cmd -> stack_cmd.

(*[2%]*)
Parameter cmd_seq_wt
  : forall S1 S2 S3 c1 c2,
    cmd_well_typed S1 c1 S2 ->
    cmd_well_typed S2 c2 S3 ->
    cmd_well_typed S1 (cmd_seq c1 c2) S3.

(*[3%]*)
Parameter interp_seq
  : forall c1 c2 s, interp_cmd (cmd_seq c1 c2) s
                    = interp_cmd c2 (interp_cmd c1 s).

(*[8%]*)
Parameter flatmap_fuse : forall cf1 cf2 c s,
    interp_cmd (cmd_flatmap cf1 (cmd_flatmap cf2 c)) s
    = interp_cmd (cmd_flatmap (cmd_seq cf1 (cmd_flatmap cf2 cmd_skip)) c) s.

Parameter partial_eval : stack_cmd -> stack_cmd.

Parameter partial_eval_sound
  : forall S c S', cmd_well_typed S c S' ->
    cmd_well_typed S (partial_eval c) S'.

(*[30%]*)
Parameter partial_eval_correct
  : forall S c S', cmd_well_typed S c S' ->
    forall s, stack_well_typed s S -> interp_cmd (partial_eval c) s = interp_cmd c s.


(*[6%]*)
Parameter loop_fuse : stack_cmd -> stack_cmd.

(* Some common comands for use in our test cases *)
Definition val_add x y :=
  match x,y with
  | val_lit xl, val_lit yl => val_lit (xl + yl)
  | _,_ => (*this case never happens on well-typed programs*) val_lit 0
  end.

Definition val_square x :=
  match x with
  | val_lit xl => val_lit (Nat.square xl)
  | _ => (*this case never happens on well-typed programs*) val_lit 0
  end.

Definition cmd_singleton := cmd_unop (fun x => val_cons x val_nil).
Definition cmd_lit n := cmd_atom (val_lit n).
Definition cmd_cons := cmd_binop val_cons.
Definition cmd_add := cmd_binop val_add.

(*[1%]*)
Parameter loop_fuse_test1
  : loop_fuse (cmd_flatmap (cmd_singleton (cmd_lit 0 (cmd_cons cmd_skip)))
                 (cmd_flatmap (cmd_lit 1 (cmd_add (cmd_singleton cmd_skip))) cmd_skip))
    = (cmd_flatmap (cmd_singleton
                      (cmd_lit 0
                         (cmd_cons
                            (cmd_flatmap (cmd_lit 1 (cmd_add (cmd_singleton cmd_skip)))
                               cmd_skip))))
         cmd_skip).

(*[1%]*)
Parameter loop_fuse_test2
  : loop_fuse (cmd_flatmap (cmd_flatmap (cmd_unop val_square (cmd_singleton cmd_skip))
                              (cmd_flatmap (cmd_unop val_square (cmd_singleton cmd_skip))
                                 (cmd_singleton cmd_skip)))
                 cmd_skip)
    = cmd_flatmap
         (cmd_flatmap
            (cmd_unop val_square
               (cmd_singleton
                  (cmd_flatmap (cmd_unop val_square (cmd_singleton cmd_skip))
                     cmd_skip)))
            (cmd_singleton cmd_skip))
         cmd_skip.


(*[1%]*)
Parameter loop_fuse_test3
  : loop_fuse (cmd_flatmap (cmd_unop val_square (cmd_singleton cmd_skip))
                 (cmd_flatmap (cmd_singleton (cmd_lit 0 (cmd_cons cmd_skip)))
                 (cmd_flatmap (cmd_lit 1 (cmd_add (cmd_singleton cmd_skip))) cmd_skip)))
    = cmd_flatmap
        (cmd_unop val_square
           (cmd_singleton
              (cmd_flatmap
                 (cmd_singleton
                    (cmd_atom (val_lit 0)
                       (cmd_binop val_cons
                          (cmd_flatmap
                             (cmd_atom (val_lit 1)
                                (cmd_binop val_add (cmd_singleton cmd_skip)))
                             cmd_skip))))
                 cmd_skip)))
        cmd_skip.

(*[8%]*)
Parameter loop_fuse_sound
  : forall S c S', cmd_well_typed S c S' ->
    cmd_well_typed S (loop_fuse c) S'.


(*[30%]*)
Parameter loop_fuse_correct
  : forall S c S',
    cmd_well_typed S c S' ->
    forall s, stack_well_typed s S -> interp_cmd (loop_fuse c) s = interp_cmd c s.

End S.

(*|
HINTS: A few hints to help you if you get stuck on certain 
       problems in Pset 6.
       Beware! Don't read further if you don't want spoilers!
=============================================================
|*)







































(*|
HINT 1: 
=======
This lemma is useful:
Lemma val_reduce_sound t1 t2 f l
  : (forall x acc', val_well_typed x t1 ->
                    val_well_typed acc' t2 ->
                    val_well_typed (f acc' x) t2) ->
    val_well_typed l (ty_list t1) ->
    forall acc,
    val_well_typed acc t2 ->
    val_well_typed (val_reduce f l acc) t2.
|*)




































(*|
HINT 2:
=======
You can define a specialzed version of functional extensionality for flatmap.
This will be useful when you want to rewrite inside `f` or `g` while reasoning
about `val_flatmap`.

Lemma flatmap_funext f g l
  : (forall v, f v = g v) ->
    val_flatmap f l = val_flatmap g l.
|*)






































(*|
HINT 3:
=======
If you are failing `loop_fuse_test2`, remember to handle `cf`.
If you are failing `loop_fuse_test3`, think about the order that
`loop_fuse` enounters the three consecutive `cmd_flatmap`s
and what recursive calls you should be making.
|*)






































(*|
HINT 4:
=======
When we are working in a context where we assume everything is well-typed,
the default functional extensionality isn't sufficient since it forgets about
the type information.
You'll need a specialized lemma that keeps it around. This is the one for `flatmap`,
and the one for `reduce` is analogous.


Lemma flatmap_funext_typed f g l t1
  : (forall v, val_well_typed v t1 -> f v = g v) ->
    val_well_typed l (ty_list t1) ->
    val_flatmap f l = val_flatmap g l.
|*)
