(******************************************************************************)
(* The statement that is proved here                                          *)
(*   Let p and q be integers.                                                 *)
(*   If p, q, p ^ q + q ^ p are prime numbers,                                *)
(*   then (p, q) = (2, 3) or (p, q) = (3, 2)                                  *)
(*                                                                            *)
(* This file requires mczify (https://github.com/math-comp/mczify)            *)
(******************************************************************************)

Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Coq Require Import Lia.
From mathcomp.zify Require Import zify.

Theorem th p q : prime p -> prime q -> prime (p ^ q + q ^ p) -> (p = 2 /\ q = 3) \/ (p = 3 /\ q = 2).
Proof.
wlog : p q / p <= q.
  move=> H.
  case: (leqP p q) => [| /ltnW leqp prmp prmq prmpqqp]; first by exact: H.
  rewrite addnC in prmpqqp.
  by have := H q p leqp prmq prmp prmpqqp; lia.
move=> lepq prmp prmq prmpqqp.
case: (even_prime prmp) => [? | oddp]; case: (even_prime prmq) => [? | oddq]; subst => //.
- case: (boolP (3 %| q)) => [dvd3q | /ltac:(rewrite /dvdn) ndvd3q].
    by case: (primeP prmq) => _ /(_ 3 dvd3q); lia.
  have H1 : 2 ^ q %% 3 = 2.
    rewrite (divn_eq q 2) modn2 oddq.
    elim: (q %/ 2) => // q' IH.
    by rewrite mulSn -addnA expnD; lia.
  have H2 : q ^ 2 %% 3 = 1.
    rewrite (divn_eq q 3).
    elim: (q %/ 3); last by lia.
    have := ltn_pmod q (erefl : 0 < 3).
    move: (q %% 3) ndvd3q; do !case => //.
  have /(prime_nt_dvdP prmpqqp (erefl : 3 != 1)) : (3 %| 2 ^ q + q ^ 2) by rewrite /dvdn -modnDm H1 H2.
  have : 2 ^ q + q ^ 2 > 3 by move: (2 ^ q); lia. (* move がないと lia が失敗する *)
  by lia.
- by have := odd_prime_gt2 oddp prmp; lia.
- have /(prime_oddPn prmpqqp) : ~~ odd (p ^ q + q ^ p) by rewrite oddD !oddX; lia.
  have : (p ^ q + q ^ p > 2).
    have gtp2 := odd_prime_gt2 oddp prmp.
    have gtq2 := odd_prime_gt2 oddq prmq.
    apply: (@ltn_trans (p ^ 1)); try lia.
    by apply: ltn_addr; rewrite ltn_exp2l; lia.
  by lia.
