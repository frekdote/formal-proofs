(* Prove 0-1 principle that gives a sufficient condition for the validity of sorting networks.              *)

(* Reference                                                                                                *)
(* - The 0-1-principle (https://www.inf.hs-flensburg.de/lang/algorithmen/sortieren/networks/nulleinsen.htm) *)

Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ZeroOnePrinciple.
Variable n : nat.

Implicit Type t : n.-tuple nat.

Inductive network :=
  Comp (i j : 'I_n) of (i < j) & network
| Done.

Fixpoint perform ne t :=
  match ne with
    Comp i j _ ne' =>
      let mn := minn (tnth t i) (tnth t j) in
      let mx := maxn (tnth t i) (tnth t j) in
      let t' :=  [ tuple if k == i then mn
                         else if k == j then mx
                              else tnth t k
                 | k < n ] in
      perform ne' t'
  | Done => t
  end.

Lemma homo_minn f x y :
  {homo f : x y / x <= y} ->
  f (minn x y) = minn (f x) (f y).
Proof.
move=> homo_f.
case: (leqP x y).
  move=> le_xy.
  have le_fxfy := homo_f _ _ le_xy.
  by rewrite (minn_idPl le_xy) (minn_idPl le_fxfy).
move=> /ltnW le_yx.
have le_fyfx := homo_f _ _ le_yx.
by rewrite (minn_idPr le_yx) (minn_idPr le_fyfx).
Qed.

Lemma homo_maxn f x y :
  {homo f : x y / x <= y} ->
  f (maxn x y) = maxn (f x) (f y).
Proof.
move=> homo_f.
case: (leqP x y).
  move=> le_xy.
  have le_fxfy:= homo_f _ _ le_xy.
  by rewrite (maxn_idPr le_xy) (maxn_idPr le_fxfy).
move=> /ltnW le_yx.
have le_fyfx := homo_f _ _ le_yx.
by rewrite (maxn_idPl le_yx) (maxn_idPl le_fyfx).
Qed.

Lemma lem f ne t :
  {homo f : x y / x <= y} ->
  perform ne [tuple of map f t] = [tuple of map f (perform ne t)].
Proof.
move=> homo_f.
elim: ne t => //= i j lt_ij ne IH t.
rewrite -IH; congr perform; apply: eq_from_tnth => k.
by rewrite !tnth_map; do ? case: eqP; rewrite ?homo_minn ?homo_maxn.
Qed.

Arguments lem [f ne t].

Theorem zero_one_principle ne :
  (forall t, {in t, forall x, (x == 0) || (x == 1)} -> sorted leq (perform ne t)) ->
  forall t, sorted leq (perform ne t).
Proof.
move=> H01 t.
apply/negPn/negP => not_sorted.
have [s1 [x [y [s2 [E /negbTE not_le_xy]]]]] : exists s1 x y s2, tval (perform ne t) = s1 ++ x :: y :: s2 /\ ~~ (x <= y).
  move: {ne t H01} (tval (perform ne t)) not_sorted.
  elim => [| x [| y s] IH] //=.
  case/nandP => [not_le_xy | not_sorted].
    by exists [::], x, y, s; split.
  have [s1 [z [w [s2 [E not_le_zw]]]]] := IH not_sorted.
  by exists (x :: s1), z, w, s2; split => //=; congr (_ :: _).
pose f a := if a >= x then 1 else 0.
have homo_f : {homo f : x y / x <= y}.
  move=> a b le_ab; rewrite /f.
  case: (leqP x a) => [le_xa | _]; last by exact: leq0n.
  by rewrite (leq_trans le_xa le_ab).
have {not_le_xy} /negbTE not_le_fxfy : ~~ (f x <= f y).
  by rewrite /f leqnn not_le_xy.
pose t' := [tuple of map f t].
have : ~~ sorted leq (perform ne t').
  rewrite (lem homo_f) /= {}E map_cat.
  case: s1 => [| ??] /=; first by rewrite not_le_fxfy.
  by rewrite cat_path /= not_le_fxfy !andbF.
have /H01-> : {in t', forall x, (x == 0) || (x == 1)}.
  by move=> a /mapP [b _ ->]; rewrite /f; case: leqP.
by [].
Qed.
End ZeroOnePrinciple.
