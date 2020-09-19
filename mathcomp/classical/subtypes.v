
From mathcomp Require Import ssreflect eqtype choice bigop ssreflect ssrbool ssrnat.
From mathcomp Require Import ssrfun fintype finfun seq ssralg generic_quotient.
From mathcomp Require Import tuple ring_quotient boolp ssrpred ideal.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.


Declare Scope subtype_scope.

Module SubTypes.

Local Open Scope subtype_scope.  

Section SubType.

Variables (T : Type) (S : {pred T}).
Let ST := {x : T | x \in S}.

Lemma subP (s : ST) : sval s \in S.
Proof. by case s. Qed.

End SubType.

Section SubZmod.

Variables (A : zmodType) (S : zmodPredT A).
Let ST := {x : A | x \in S}.
(*
Lemma subP (s : ST) : sval s \in S.
Proof. by case s. Qed.
*)
Let zero_in : 0 \in S := rpredT0 S.
Let zeroT : ST := Sub 0 zero_in.

Fact add_in (s1 s2 : ST) : (sval s1 + sval s2) \in S.
Proof. by rewrite rpredTD ?(svalP s1) ?(svalP s2). Qed.
Let addT s1 s2 : ST := Sub (sval s1 + sval s2) (add_in s1 s2).

Fact opp_in (s : ST) : - (sval s) \in S.
Proof. by rewrite rpredTN ?(svalP s). Qed.
Let oppT s : ST := Sub (-sval s) (opp_in s).

Fact addA : associative addT.
Proof. by move=> s1 s2 s3; apply: val_inj; rewrite /= addrA. Qed.

Fact addC : commutative addT.
Proof. by move=> s1 s2; apply: val_inj; rewrite /= addrC. Qed.

Fact add0 : left_id zeroT addT.
Proof. by move=> s; apply: val_inj; rewrite /= add0r. Qed.

Fact addN : left_inverse zeroT oppT addT.
Proof. by move=> s; apply: val_inj; rewrite /= addNr. Qed.

Definition zmod_subMixin := ZmodMixin addA addC add0 addN.
Canonical zmod_subType := Eval hnf in ZmodType ST zmod_subMixin.

Lemma sval_add : additive (sval : ST -> A). Proof. by []. Qed.
Canonical sval_additive := Additive sval_add.

Lemma sval0 : sval (0 : ST) = 0.
Proof. by apply: raddf0. Qed.
Lemma svalD (s1 s2 : ST) : sval (s1 + s2) = (sval s1) + (sval s2).
Proof. by rewrite raddfD. Qed.
Lemma svalB (s1 s2 : ST) : sval (s1 - s2) = (sval s1) - (sval s2).
Proof. by rewrite raddfB. Qed.

End SubZmod.

Section SubRing.

Variables (R : ringType) (S : subringPredT R).

Let ST := {x : R | x \in S}.
Fact one_in : 1 \in S.
Proof. apply: rpredT1. Qed.
Let oneT : ST := Sub 1 one_in.

Lemma mul_in (s1 s2 : ST) : (sval s1 * sval s2) \in S.
Proof. by rewrite rpredTM ?(svalP s1) ?(svalP s2). Qed.
Let mulT s1 s2 : ST := Sub (sval s1 * sval s2) (mul_in s1 s2).

Fact mulA : @associative ST mulT.
Proof. by move=> s1 s2 s3; apply: val_inj; rewrite !SubK mulrA. Qed.
Fact mul1l : left_id oneT mulT.
Proof. by move=> s; apply: val_inj; rewrite !SubK mul1r. Qed.
Fact mul1r : right_id oneT mulT.
Proof. by move=> s; apply: val_inj; rewrite !SubK mulr1. Qed.
Fact mulDl : @left_distributive ST ST mulT +%R.
Proof. by move=> s1 s2 s3; apply: val_inj; rewrite !SubK mulrDl. Qed.
Fact mulDr : @right_distributive ST ST mulT +%R.
Proof. by move=> s1 s2 s3; apply: val_inj; rewrite !SubK mulrDr. Qed.
Fact nz1 : oneT != 0 :> ST.
Proof. by apply: contraNneq (oner_neq0 R)=> /(f_equal sval) /= ->. Qed.

Definition ring_subMixin := RingMixin mulA mul1l mul1r mulDl mulDr nz1.
Canonical ring_subType := Eval hnf in RingType ST ring_subMixin.

Lemma sval_mul : multiplicative (sval : ST -> R). Proof. by []. Qed.
Canonical sval_morphism := AddRMorphism sval_mul.

Lemma sval1 : sval (1 : ST) = 1.
Proof. by apply: rmorph1. Qed.
Lemma svalM (s1 s2 : ST) : sval (s1 * s2) = (sval s1) * (sval s2).
Proof. by rewrite rmorphM. Qed.

End SubRing.

Section SubComRing.

Variables (R : comRingType) (S : subringPredT R).

Let ST := {x : R | x \in S}.
Fact mulC : @commutative ST ST *%R.
Proof. by move=> s1 s2; apply: val_inj; rewrite !SubK mulrC. Qed.

Canonical comRing_subType := Eval hnf in ComRingType ST mulC.

End SubComRing.

End SubTypes.

Notation "{ 'SubZmod' S }" := (SubTypes.zmod_subType S) (at level 0) : subtype_scope.
Notation "{ 'SubRing' S }" := (SubTypes.ring_subType S) (at level 0) : subtype_scope.
Notation "{ 'SubComRing' S }" := (SubTypes.comRing_subType S) (at level 0) : subtype_scope.



