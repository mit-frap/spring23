(** * 6.512 Formal Reasoning About Programs, Spring 2023 - Pset 12 *)
Require Import Frap Pset12.Pset12Sig.


(* The next span of code, up to the word "Example", sets up some automation
 * support. Feel free to skip ahead to the example to see the ingredients 
 * in action in the verification of an example program.
 *)

Lemma HtReturn' : forall {t : Set} (P : hprop) (R G : hrel) (Q : _ -> hprop) (v : t),
    stableP P R
    -> (forall h, P h -> Q v h)
    -> hoare_triple P R (Return v) G Q.
Proof.
  simplify.
  eapply HtConsequence with (P' := P) (R' := R) (G' := G); eauto.
  simplify; propositional; subst; eauto.
Qed.

Lemma HtFail' : forall {t : Set} (P : hprop) (R G : hrel) (Q : t -> hprop),
    (forall h, P h -> False)
    -> hoare_triple P R Fail G Q.
Proof.
  simplify.
  eapply HtConsequence with (R' := R) (G' := G) (Q' := Q); eauto.
  simplify; propositional.
  simplify; propositional.
  unfold stableP; simplify.
  first_order.
Qed.

Lemma HtConsequenceBasic : forall {t : Set} P R c G Q (P' : hprop) (Q' : t -> hprop),
    hoare_triple P R c G Q
    -> (forall h, P' h -> P h)
    -> (forall v h, Q v h -> Q' v h)
    -> stableP P' R
    -> hoare_triple P' R c G Q'.
Proof.
  eauto.
Qed.

Lemma HtStrengthen : forall {t : Set} P R c G (Q : t -> _) (P' : hprop),
    hoare_triple P R c G Q
    -> (forall h, P' h -> P h)
    -> stableP P' R
    -> hoare_triple P' R c G Q.
Proof.
  eauto.
Qed.

Lemma HtWeaken : forall {t : Set} P R c G Q (Q' : t -> hprop),
    hoare_triple P R c G Q
    -> (forall v h, Q v h -> Q' v h)
    -> hoare_triple P R c G Q'.
Proof.
  eauto using always_stableP.
Qed.

(* The first several tactics are similar to those that we have
 * already seen for earlier iterations of our Hoare logics.
 *)
Ltac step0 := apply HtReturn' || eapply HtFail' || eapply HtBind.
Ltac step := step0; simp.
Ltac ht := simp; repeat step.
Ltac loop_inv0 Inv := (eapply HtStrengthen; [ apply HtLoop with (I := Inv) | .. ])
                      || (eapply HtConsequenceBasic; [ apply HtLoop with (I := Inv) | .. ]).
Ltac loop_inv Inv := loop_inv0 Inv; simp.
Ltac strengthen P_ := apply HtStrengthen with (P := P_); simp.


(** * Example *)

(* Here is a demonstrative use of rely-guarantee logic to verify a concurrent
 * program.  We prove that two threads cooperate to keep the value in one memory
 * address even.  They follow a manually implemented locking protocol --
 * we code and justify mutual-exclusion functionality explicitly as a part of
 * the implementation. *)

Fixpoint isEven (n : nat) : bool :=
  match n with
  | O => true
  | S (S n') => isEven n'
  | _ => false
  end.

Definition prog2_th turn_addr data_addr me other :=
  (* First, we loop forever adding to a counter. *)
  for _ := tt loop
    (* The next loop waits until it's our turn to run. *)
    _ <- (for _ := tt loop
      (* We read from a flag [turn_addr] that holds the ID of the thread allowed
       * to run next. *)
      turn <- Atomic (Read turn_addr);
      if turn ==n me then
        (* Is it my turn?  Good; exit the loop. *)
        Return (Done tt)
      else
        (* Not my turn?  Go around again. *)
        Return (Again tt)
      done);
    (* OK, we are allowed to run.  Let's read the counter from [data_addr]. *)
    tmp <- Atomic (Read data_addr);
    if isEven tmp then
      (* Just to make this interesting, let's first write an odd value, based on
       * incrementing by 1!  The other thread had better not be looking now. *)
      _ <- Atomic (Write data_addr (1 + tmp));
      (* Now let's read back what we wrote. *)
      tmp2 <- Atomic (Read data_addr);
      (* Then increment again to reach an even value. *)
      _ <- Atomic (Write data_addr (1 + tmp2));
      (* Finally, flip the whose-turn flag to the other thread's ID. *)
      _ <- Atomic (Write turn_addr other);
      Return (Again tt)
    else
      (* Impossible case: we read an odd counter. *)
      Fail
  done.

Example prog2 turn_addr data_addr :=
  prog2_th turn_addr data_addr 0 1 || prog2_th turn_addr data_addr 1 0.

(* Let's prove this program against a natural spec. *)
Lemma ht_prog2 : forall turn_addr data_addr,
    turn_addr <> data_addr
    -> hoare_triple
         (fun h => isEven (h $! data_addr) = true /\ (h $! turn_addr = 0 \/ h $! turn_addr = 1))
         (* Precondition: data starts out even, and it's someone's turn. *)

         (fun _ _ => False)
         (* Rely: no other threads are allowed to do anything at all, because
          * this program is meant to run by itself, with just these two
          * threads. *)
         
         (prog2 turn_addr data_addr)

         (fun _ _ => True)
         (* Guarantee: we are generous to ourselves and allow any steps. ;-)
          * (We will still use stricter guarantees internally within the
          * proof.) *)

         (fun _ _ => False)
         (* Postcondition: the program is nonterminating by design! *).
Proof.
  unfold prog2, prog2_th.
  simp.

  (* We use the [fork] tactic to make progress when we get to a parallel
   * composition. *)
  fork (fun h => (h $! turn_addr = 0 /\ isEven (h $! data_addr) = true)
                 \/ h $! turn_addr = 1)
       (* This is the precondition of the first thread.  Note how we make no
        * claim about the counter value if it is the *other* thread's turn.
        * Otherwise, the precondition would not be *stable*. *)

       (fun h h' => (h $! turn_addr = 0
                     /\ h' $! turn_addr = 0)
                    \/ (h $! turn_addr = 0
                        /\ h' $! turn_addr = 1
                        /\ isEven (h' $! data_addr) = true)
                    \/ (h $! turn_addr = 1
                        /\ h' $! turn_addr = 1
                        /\ h' $! data_addr = h $! data_addr))
       (* This is the first thread's guarantee: any step it takes should satisfy
        * this relation.  The details are easier to read in math than to explain
        * in prose! *)

       (fun (_ : unit) (_ : heap) => False)
       (* And here's the first thread's postcondition. *)

       (* We then repeat the mirror images to give the same specifications for
        * the second thread. *)
       (fun h => (h $! turn_addr = 1 /\ isEven (h $! data_addr) = true)
                 \/ h $! turn_addr = 0)
       (fun h h' => (h $! turn_addr = 1
                     /\ h' $! turn_addr = 1)
                    \/ (h $! turn_addr = 1
                        /\ h' $! turn_addr = 0
                        /\ isEven (h' $! data_addr) = true)
                    \/ (h $! turn_addr = 0
                        /\ h' $! turn_addr = 0
                        /\ h' $! data_addr = h $! data_addr))
       (fun (_ : unit) (_ : heap) => False).

  (* Now we're verifying thread #1. *)

  (* The outer loop invariant is a repeat of the precondition, also asserting
   * that the loop can never terminate (e.g., [Done] mapped to [False]). *)
  loop_inv (fun (o : loop_outcome unit) h => match o with
                                             | Done _ => False
                                             | Again _ => (h $! turn_addr = 0 /\ isEven (h $! data_addr) = true) \/ h $! turn_addr = 1
                                             end).
  step.
  (* Inner loop invariant: if the loop isn't done yet ([Again]), then we repeat
   * the precondition; otherwise, we have learned that it's our turn, so we use
   * the precondition with the case for "it's not my turn" pruned out. *)
  loop_inv (fun (o : loop_outcome unit) h => match o with
                                             | Done _ => h $! turn_addr = 0 /\ isEven (h $! data_addr) = true
                                             | Again _ => (h $! turn_addr = 0 /\ isEven (h $! data_addr) = true) \/ h $! turn_addr = 1
                                             end).
  step.
  (* Every time we reach an atomic command (read or write), we call [atomic],
   * providing the postcondition explicitly.  Some care is needed in choosing
   * this predicate, since it must be *stable*.  That is, other threads must not
   * be allowed to falsify it. *)
  atomic (fun r h =>
            ((h $! turn_addr = 0 /\ isEven (h $! data_addr) = true)
             \/ h $! turn_addr = 1)
            /\ (r = 0 -> h $! turn_addr = 0)).
  (* Further details in this particular proof aren't essential for completing
   * this pset, but feel free to step through and see what's happening. *)
  cases (r ==n 0).
  step.
  step.
  step.
  atomic (fun r h =>
            h $! turn_addr = 0 /\ isEven (h $! data_addr) = true /\ r = h $! data_addr).
  simp.
  cases (isEven r0).
  step.
  atomic (fun (_ : unit) h =>
            exists r, h $! turn_addr = 0 /\ isEven r = true /\ h $! data_addr = 1 + r).
  eauto.
  rewrite H4; eauto.
  simp.
  step.
  atomic (fun r' h =>
            exists r, h $! turn_addr = 0 /\ isEven r = true /\ h $! data_addr = 1 + r /\ r' = 1 + r).
  eauto.
  rewrite H4; eauto.
  rewrite H4; eauto.
  simp.
  step.
  atomic (fun (_ : unit) h =>
            h $! turn_addr = 0 /\ isEven (h $! data_addr) = true).
  rewrite H4; eauto.
  step.
  atomic (fun (_ : unit) h =>
            (h $! turn_addr = 0 /\ isEven (h $! data_addr) = true)
            \/ h $! turn_addr = 1).
  step.
  step.

  (* Here's the proof for the second thread, where we switch [0]s with [1]s. *)
  loop_inv (fun (o : loop_outcome unit) h => match o with
                                             | Done _ => False
                                             | Again _ => (h $! turn_addr = 1 /\ isEven (h $! data_addr) = true) \/ h $! turn_addr = 0
                                             end).
  step.
  loop_inv (fun (o : loop_outcome unit) h => match o with
                                             | Done _ => h $! turn_addr = 1 /\ isEven (h $! data_addr) = true
                                             | Again _ => (h $! turn_addr = 1 /\ isEven (h $! data_addr) = true) \/ h $! turn_addr = 0
                                             end).
  step.
  atomic (fun r h =>
            ((h $! turn_addr = 1 /\ isEven (h $! data_addr) = true)
             \/ h $! turn_addr = 0)
            /\ (r = 1 -> h $! turn_addr = 1)).
  cases (r ==n 1).
  step.
  step.
  step.
  atomic (fun r h =>
            h $! turn_addr = 1 /\ isEven (h $! data_addr) = true /\ r = h $! data_addr).
  simp.
  cases (isEven r0).
  step.
  atomic (fun (_ : unit) h =>
            exists r, h $! turn_addr = 1 /\ isEven r = true /\ h $! data_addr = 1 + r).
  eauto.
  rewrite H4; eauto.
  simp.
  step.
  atomic (fun r' h =>
            exists r, h $! turn_addr = 1 /\ isEven r = true /\ h $! data_addr = 1 + r /\ r' = 1 + r).
  eauto.
  rewrite H4; eauto.
  rewrite H4; eauto.
  simp.
  step.
  atomic (fun (_ : unit) h =>
            h $! turn_addr = 1 /\ isEven (h $! data_addr) = true).
  rewrite H4; eauto.
  step.
  atomic (fun (_ : unit) h =>
            (h $! turn_addr = 1 /\ isEven (h $! data_addr) = true)
            \/ h $! turn_addr = 0).
  step.
  step.
  
  simp.
  simp.
  simp.
  simp.
  simp.
Qed.
