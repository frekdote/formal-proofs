(******************************************************************************)
(* Reference                                                                  *)
(* - Saidak, F. (2006). A New Proof of Euclid's Theorem. The American         *)
(*   Mathematical Monthly, 113(10), 937-938. doi:10.2307/27642094             *)
(******************************************************************************)

Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint f i :=
  match i with
    0 => 1
  | i'.+1 => f i' * (f i').+1
  end.

Definition p i := pdiv (f i).+1.

Lemma lem1 i : f i > 0.
Proof. by elim: i => //= i IH; rewrite muln_gt0 IH ltnS (ltnW IH). Qed.

Theorem all_elements_of_p_are_prime i : prime (p i).
Proof. by apply: pdiv_prime; exact: lem1. Qed.

Lemma lem2 i j : i <= j -> f i %| f j.
Proof. by move/leP; elim: j / => //= j _; exact: dvdn_mulr. Qed.

Lemma lem3 i j : i < j -> p i %| f j.
Proof.
move=> lt_ij.
apply: (@dvdn_trans (f i.+1)); last by exact: lem2.
by rewrite /=; apply: dvdn_mull; exact: pdiv_dvd.
Qed.

Theorem all_elements_of_p_are_distinct i j : p i = p j -> i = j.
Proof.
case: (i =P j) => // /eqP.
rewrite neq_ltn.
wlog lt_ij : i j / i < j.
  move=> H /orP [lt_ij | lt_ji] Epij; first by apply: H; rewrite ?lt_ij.
  by symmetry; apply: H; rewrite ?lt_ji.
move=> _ Epij.
exfalso.
have dvd_pi_fj := lem3 lt_ij.
have dvd_pj_fj := pdiv_dvd (f j).+1.
have /(coprime_dvdl dvd_pi_fj)/(coprime_dvdr dvd_pj_fj) := coprimenS (f j).
have prime_pi := all_elements_of_p_are_prime i.
have pi_neq_1 : p i != 1 by rewrite neq_ltn prime_gt1 // orbT.
have prime_pj := all_elements_of_p_are_prime j.
rewrite (prime_coprime _ prime_pi).
by move/(prime_nt_dvdP prime_pj pi_neq_1).
Qed.
