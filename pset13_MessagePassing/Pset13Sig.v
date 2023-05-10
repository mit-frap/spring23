(** * 6.512 Formal Reasoning About Programs, Spring 2023 - Pset 13 *)

Require Coq816.
Require Import Frap MessagesAndRefinement.

Module Type S.

  Inductive request :=
  | GET (client_id key : nat).

  Definition get_key (req : request) : nat :=
    match req with
    | GET _ key => key
    end.

  Inductive response :=
  | FOUND (client_id key : nat) (value : nat)
  | NOT_FOUND (client_id key : nat).

  Definition request_handler (store : fmap nat nat) (source output : channel) : proc :=
    ??source(req: request);
    match req with
    | GET client_id key =>
      match store $? key with
      | Some v => !!output(FOUND client_id key v); Done
      | None => !!output(NOT_FOUND client_id key); Done
      end
    end.

  Definition split_store (full_store even_store odd_store : fmap nat nat) : Prop :=
    (forall k, k mod 2 = 0  -> even_store $? k = full_store $? k) /\
    (forall k, k mod 2 = 0  -> odd_store  $? k = None) /\
    (forall k, k mod 2 <> 0 -> even_store $? k = None) /\
    (forall k, k mod 2 <> 0 -> odd_store  $? k = full_store $? k).

  Definition request_dispatcher (input forward_even forward_odd : channel) : proc :=
    ??input(req: request);
    if get_key req mod 2 ==n 0 then
      !!forward_even(req); Done
    else
      !!forward_odd(req); Done.

  Definition balanced_handler (even_store odd_store : fmap nat nat) (input output : channel) : proc :=
    New[input; output](forward_even);
    New[input; output; forward_even](forward_odd);
    request_dispatcher input forward_even forward_odd
    || (request_handler even_store forward_even output)
    || (request_handler odd_store forward_odd output).

  Definition correctness: Prop := forall full_store even_store odd_store input output,
      split_store full_store even_store odd_store ->
      input <> output ->
      forall trace,
        couldGenerate (balanced_handler even_store odd_store input output) trace ->
        couldGenerate (request_handler full_store input output) trace.

  (*[30%]*)
  Parameter R_alias_for_grading : fmap nat nat -> fmap nat nat ->
                                  fmap nat nat -> channel -> channel ->
                                  proc -> proc -> Prop.

  (*[70%]*)
  Parameter balanced_handler_correct : correctness.
End S.

(*|
HINTS: A few hints to help you if you get stuck on certain 
       problems in Pset 13.
       Beware! Don't read further if you don't want spoilers!
=============================================================
|*)





































(*|
HINT 1: First stage of simulation relation R
============================================

Here's the first case of our simulation relation R:

| Stage0 :
    NoDup [input; output] ->
    R fs es os input output
      (balanced_handler es os input output)
      (request_handler fs input output)
|*)





































(*|
HINT 2: Second stage of simulation relation R
=============================================

Here's the second case of our simulation relation R:

| Stage1 : forall forward_even,
    NoDup [input; output; forward_even] ->
    R fs es os input output
      (Block forward_even;
       New [input; output; forward_even] (forward_odd);
       request_dispatcher input forward_even forward_odd
       || request_handler es forward_even output
       || request_handler os forward_odd output)
      (request_handler fs input output)
|*)





































(*|
HINT 3: Order of invert
=======================

To prove the simulation, you'll get to assume an lstepSilent (or an lstep with an action, in the second subgoal) as well as an R, and you'll have to invert both of them. Depending on which of the two you invert first, your proof might become shorter or longer.
|*)





































(*|
HINT 4: Going from Stage0 to Stage1 in case of a silent step
============================================================

In our solution, there's a case where we have to prove that when the implementation takes a silent step starting at what we called Stage0, then the specification can simulate this.
Our goal looks as follows:

  full_store, even_store, odd_store : fmap nat nat
  input, output : nat
  H : split_store full_store even_store odd_store
  H0 : input = output -> False
  pr1' : proc
  H2 : lstepSilent (balanced_handler even_store odd_store input output) pr1'
  H3 : NoDup [input; output]
  ============================
  exists pr2' : proc,
    (lstepSilent) ^* (request_handler full_store input output) pr2' /\
    R full_store even_store odd_store input output pr1' pr2'

And we prove it with the following code:

    + (* After Stage0: generate fresh forward_even channel *)
      invert H2. rename ch into forward_even.
      eexists. split.
      * eapply TrcRefl.
      * eapply Stage1. lists.
|*)





































(*|
HINT 5: Going from Stage0 to Stage1 in case of a non-silent step
================================================================

In our solution, there's a case where we have to prove that when the implementation takes a non-silent step starting at what we called Stage0, then the specification can simulate this.
Our goal looks as follows:

  full_store, even_store, odd_store : fmap nat nat
  input, output : nat
  H : split_store full_store even_store odd_store
  H0 : input = output -> False
  a : action
  pr1' : proc
  H2 : lstep (balanced_handler even_store odd_store input output) (Action a) pr1'
  H3 : NoDup [input; output]
  ============================
  exists pr2' pr2'' : proc,
    (lstepSilent) ^* (request_handler full_store input output) pr2' /\
    lstep pr2' (Action a) pr2'' /\ R full_store even_store odd_store input output pr1' pr2''

This is a contradiction, because H2 claims that balanced_handler takes a non-silent step, but the first step it takes is to execute a New, which is silent. So, all we have to do in this case is "invert H2."
|*)
