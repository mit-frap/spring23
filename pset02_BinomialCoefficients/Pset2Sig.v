(** * 6.512 Formal Reasoning About Programs, Spring 2023 - Pset 2 *)

Require Coq816.

Require Import Coq.NArith.NArith. Open Scope N_scope.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.micromega.Lia.
Require Import Frap.Frap.

Module Type S.
  Definition fact: N -> N :=
    recurse by cases
    | 0 => 1
    | n + 1 => (n + 1) * recurse
    end.

  (*[5%]*) Parameter exp: N -> N -> N.
  Axiom test_exp_2_3: exp 2 3 = 8.
  Axiom test_exp_3_2: exp 3 2 = 9.
  Axiom test_exp_4_1: exp 4 1 = 4.
  Axiom test_exp_5_0: exp 5 0 = 1.
  Axiom test_exp_1_3: exp 1 3 = 1.

  Definition seq (f: N -> N): N -> N -> list N :=
    recurse by cases
    | 0 => fun start => []
    | n + 1 => fun start => f start :: recurse (start + 1)
    end.

  Definition ith: N -> list N -> N :=
    recurse by cases
    | 0 => fun (l: list N) => match l with
                              | h :: t => h
                              | nil => 0
                              end
    | i + 1 => fun (l: list N) => match l with
                                  | h :: t => recurse t
                                  | nil => 0
                                  end
    end.

  Fixpoint len(l: list N): N :=
    match l with
    | [] => 0
    | h :: t => 1 + len t
    end.

  (*[12%]*)
  Axiom seq_spec: forall f count i start, i < count -> ith i (seq f count start) = f (start + i).

  (*[12%]*)
  Axiom ith_out_of_bounds_0: forall i l, len l <= i -> ith i l = 0.

  Definition C(n k: N): N := fact n / (fact (n - k) * fact k).

  Definition bcoeff(n: N): N -> N :=
    recurse by cases
    | 0 => 1
    | k + 1 => recurse * (n - k) / (k + 1)
    end.

  (*[7%]*)
  Axiom fact_nonzero: forall n, fact n <> 0.

  (*[7%]*)
  Axiom Cn0: forall n, C n 0 = 1.

  (*[7%]*)
  Axiom Cnn: forall n, C n n = 1.

  (*[25%]*)
  Axiom bcoeff_correct: forall n k, k <= n -> bcoeff n k = C n k.

  Definition Pascal's_rule: Prop := forall n k,
      1 <= k <= n ->
      C (n+1) k = C n (k - 1) + C n k.

  Definition nextLine(l: list N): list N :=
    1 :: seq (fun k => ith (k - 1) l + ith k l) (len l) 1.

  Definition all_coeffs_fast: N -> list N :=
    recurse by cases
    | 0 => [1]
    | n + 1 => nextLine recurse
    end.

  (*[25%]*)
  Axiom all_coeffs_fast_correct:
    Pascal's_rule ->
    forall n k,
      k <= n ->
      ith k (all_coeffs_fast n) = C n k.
End S.


(*|
HINTS: A hint to help you if you get stuck on certain 
       problems in pset 2.
       Beware! Don't read further if you don't want spoilers!
=============================================================
|*)


































(*
To prove `all_coeffs_fast_correct`, it might be helpful first to prove

```
Lemma len_all_coeffs_fast: forall n, len (all_coeffs_fast n) = n + 1.
```
*)
