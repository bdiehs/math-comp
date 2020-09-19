
From mathcomp Require Import ssreflect eqtype choice bigop ssreflect ssrbool ssrnat.
From mathcomp Require Import ssrfun fintype finfun seq ssralg generic_quotient.
From mathcomp Require Import tuple ring_quotient boolp.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Lemma struct_ext T U (f : T -> Prop) (g : forall t, (f t) -> U) (T1 T2 : T) (fT1 : f T1) (fT2 : f T2):
  T1 = T2 -> g T1 fT1 = g T2 fT2.
Proof.
  move=> eqT1T2; move: fT1 fT2.
  by rewrite eqT1T2=> fT1 fT2; rewrite (Prop_irrelevance fT1 fT2).
Qed. 

Section ZmodPredDef.

Variable (V : zmodType).
  
Structure addrPredT := {
  add_pred :> {pred V};
  _ : addr_closed add_pred
}.

Lemma addrPred_ext (S1 S2 : addrPredT) : (forall x, (x \in S1) = (x \in S2)) -> S1 = S2.
Proof.
  by case S1; case S2=> ? ? ? ? /funext; apply: struct_ext.
Qed.

Definition addr_pred2 : addrPredT -> pred V := @add_pred.
Coercion addr_pred2 : addrPredT >-> pred.

Structure opprPredT := {
  opp_pred :> {pred V};
  _ : oppr_closed opp_pred
}.

Structure zmodPredT := {
  zmod_pred :> addrPredT;
  _ : oppr_closed zmod_pred
}.

Definition MkzmodPredT (S : {pred V}) (zS : zmod_closed S) :=
  @Build_zmodPredT (Build_addrPredT zS) zS.

Lemma zmodPredT_ext (S1 S2 : zmodPredT) : (forall x, (x \in S1) = (x \in S2)) -> S1 = S2.
Proof.
  by case S1; case S2=> ? ? ? ? /addrPred_ext; apply: struct_ext.
Qed.

End ZmodPredDef.

Section RingPredDef.

Variable (R : ringType).

Structure mulrPredT := {
  mul_pred :> {pred R};
  _ : mulr_closed mul_pred
}.

Structure semiringPredT := {
  semiring_pred :> addrPredT R;
  _ : mulr_closed semiring_pred
}.

Structure smulrPredT := {
  smul_pred :> opprPredT R;
  _ : mulr_closed smul_pred
}.

Structure subringPredT := {
  subring_pred :> zmodPredT R;
  _ : mulr_closed subring_pred
}.

End RingPredDef.

Section UnitRingPredDef.

Variable (R : unitRingType).

Structure divrPredT := {
  div_pred :> mulrPredT R;
  _ : invr_closed div_pred
}.

Structure sdivrPredT := {
  sdiv_pred :> smulrPredT R;
  _ : invr_closed sdiv_pred
}.

End UnitRingPredDef.

Section Coercions.

Ltac done := case=> *; assumption.
Fact zmod_oppr R : forall (S : @zmodPredT R), oppr_closed S. Proof. by []. Qed.
Fact semiring_mulr R : forall (S : @semiringPredT R), mulr_closed S. Proof. by []. Qed.
Fact smul_mulr R : forall (S : @smulrPredT R), mulr_closed S. Proof. by []. Qed.
Fact subring_mulr R : forall (S : @subringPredT R), mulr_closed S. Proof. by []. Qed.
Fact subring_semiringr R : forall (S : @subringPredT R), mulr_closed S. Proof. by []. Qed.

Definition zmod_opp R (S : @zmodPredT R) := Build_opprPredT (@zmod_oppr R S).
Definition semiring_mul R (S : @semiringPredT R) := Build_mulrPredT (semiring_mulr S).
Definition smul_mul R (S : @smulrPredT R) := Build_mulrPredT (smul_mulr S).
Definition subring_mul R (S : @subringPredT R) := Build_mulrPredT (subring_mulr S).
Definition subring_semiring R (S : @subringPredT R) := Build_semiringPredT (subring_semiringr S).

Coercion zmod_opp : zmodPredT >-> opprPredT.
Canonical zmod_opp.
Coercion semiring_mul : semiringPredT >-> mulrPredT.
Canonical semiring_mul.
Coercion smul_mul : smulrPredT >-> mulrPredT.
Canonical smul_mul.
(*Coercion subring_mul : subringPredT >-> mulrPredT.
Canonical subring_mul.*)
Coercion subring_semiring : subringPredT >-> semiringPredT.
Canonical subring_semiring.
End Coercions.

Section AddrPredTTheory.

Variables (V : zmodType) (addS : addrPredT V).

Lemma rpredT0D : addr_closed addS.
Proof. by case addS. Qed.

Lemma rpredT0 : 0 \in addS.
Proof. by case: rpredT0D. Qed.

Lemma rpredTD : {in addS &, forall u v, u + v \in addS}.
Proof. by case: rpredT0D. Qed.

Lemma rpredT_sum I r (P : pred I) F :
  (forall i, P i -> F i \in addS) -> \sum_(i <- r | P i) F i \in addS.
Proof. by move=> IH; elim/big_ind: _; [apply: rpredT0 | apply: rpredTD |]. Qed.

Lemma rpredTMn n : {in addS, forall u, u *+ n \in addS}.
Proof. by move=> u Su; rewrite -(card_ord n) -sumr_const rpredT_sum. Qed.

End AddrPredTTheory.

Section OpprPredTTheory.


Variables (V : zmodType) (zmodS : opprPredT V).

Lemma rpredTNr : oppr_closed zmodS.
Proof. by case: zmodS. Qed.

Lemma rpredTN : {mono -%R: u / u \in zmodS}.
Proof. by move=> u; apply/idP/idP=> /rpredTNr; rewrite ?opprK; apply. Qed.


End OpprPredTTheory.

Section ZmodPredTTheory.

Variables (V : zmodType) (zmodS : zmodPredT V).

Lemma rpredTB : {in zmodS &, forall u v, u - v \in zmodS}.
Proof. by move=> u v Su Sv; rewrite /= rpredTD ?rpredTN. Qed.

Lemma rpredTBC u v : u - v \in zmodS = (v - u \in zmodS).
Proof. by rewrite -rpredTN opprB. Qed.

Lemma rpredTMNn n : {in zmodS, forall u, u *- n \in zmodS}.
Proof. by move=> u Su; rewrite /= rpredTN rpredTMn. Qed.

Lemma rpredTDr x y : x \in zmodS -> (y + x \in zmodS) = (y \in zmodS).
Proof.
move=> Sx; apply/idP/idP=> [Sxy | /rpredTD-> //].
by rewrite -(addrK x y) rpredTB.
Qed.

Lemma rpredTDl x y : x \in zmodS -> (x + y \in zmodS) = (y \in zmodS).
Proof. by rewrite addrC; apply: rpredTDr. Qed.

Lemma rpredTBr x y : x \in zmodS -> (y - x \in zmodS) = (y \in zmodS).
Proof. by rewrite -rpredTN; apply: rpredTDr. Qed.

Lemma rpredTBl x y : x \in zmodS -> (x - y \in zmodS) = (y \in zmodS).
Proof. by rewrite -(rpredTN _ y); apply: rpredTDl. Qed.

End ZmodPredTTheory.

Section RingPredT.

Variables (R : ringType).

Lemma rpredTMsign (zmodS : zmodPredT R) n x :
  ((-1) ^+ n * x \in zmodS) = (x \in zmodS).
Proof. by rewrite -signr_odd mulr_sign; case: ifP => // _; rewrite rpredTN. Qed.


Section Mul.

Variables (mulS : mulrPredT R).

Lemma rpredT1M : mulr_closed mulS.
Proof. by case mulS. Qed.

Lemma rpredT1 : 1 \in mulS.
Proof. by case: rpredT1M. Qed.

Lemma rpredTM : {in mulS &, forall u v, u * v \in mulS}.
Proof. by case: rpredT1M. Qed.

Lemma rpredT_prod I r (P : pred I) F :
  (forall i, P i -> F i \in mulS) -> \prod_(i <- r | P i) F i \in mulS.
Proof. by move=> IH; elim/big_ind: _; [apply: rpredT1 | apply: rpredTM |]. Qed.

Lemma rpredTX n : {in mulS, forall u, u ^+ n \in mulS}.
Proof. by move=> u Su; rewrite -(card_ord n) -prodr_const rpredT_prod. Qed.

End Mul.

Lemma rpredT_nat (rngS : semiringPredT R) n : n%:R \in rngS.
Proof. by rewrite rpredTMn ?rpredT1. Qed.

Lemma rpredTN1 (mulS : smulrPredT R) : -1 \in mulS.
Proof. by rewrite rpredTN rpredT1. Qed.

Lemma rpredT_sign (mulS : smulrPredT R) n :
  (-1) ^+ n \in mulS.
Proof. by rewrite rpredTX ?rpredTN1. Qed.


End RingPredT.


Section UnitRingPredT.

Variable R : unitRingType.

Section Div.

Variables (S : {pred R}) (divS : divrPredT R).

Lemma rpredTVr x : x \in divS -> x^-1 \in divS.
Proof. by case: divS x. Qed.

Lemma rpredTV x : (x^-1 \in divS) = (x \in divS).
Proof. by apply/idP/idP=> /rpredTVr; rewrite ?invrK. Qed.

Lemma rpredT_div : {in divS &, forall x y, x / y \in divS}.
Proof. by move=> x y Sx Sy; rewrite /= rpredTM ?rpredTV. Qed.

Lemma rpredTXN n : {in divS, forall x, x ^- n \in divS}.
Proof. by move=> x Sx; rewrite /= rpredTV rpredTX. Qed.

Lemma rpredTMl x y : x \in divS -> x \is a GRing.unit-> (x * y \in divS) = (y \in divS).
Proof.
move=> Sx Ux; apply/idP/idP=> [Sxy | /(rpredTM Sx)-> //].
by rewrite -(mulKr Ux y); rewrite rpredTM ?rpredTV.
Qed.

Lemma rpredTMr x y : x \in divS -> x \is a GRing.unit -> (y * x \in divS) = (y \in divS).
Proof.
move=> Sx Ux; apply/idP/idP=> [Sxy | /rpredTM-> //].
by rewrite -(mulrK Ux y); rewrite rpredT_div.
Qed.

Lemma rpredT_divr x y : x \in divS -> x \is a GRing.unit -> (y / x \in divS) = (y \in divS).
Proof. by rewrite -rpredTV -unitrV; apply: rpredTMr. Qed.

Lemma rpredT_divl x y : x \in divS -> x \is a GRing.unit -> (x / y \in divS) = (y \in divS).
Proof. by rewrite -(rpredTV y); apply: rpredTMl. Qed.

End Div.

Fact unitr_sdivr_closed : @sdivr_closed R GRing.unit.
Proof. by split=> [|x y Ux Uy]; rewrite ?unitrN1 // unitrMl ?unitrV. Qed.

Canonical unit_opprPredT := Build_opprPredT unitr_sdivr_closed.
Canonical unit_mulrPredT := Build_mulrPredT unitr_sdivr_closed.
Canonical unit_divrPredT := Build_divrPredT unitr_sdivr_closed.
Canonical unit_smulrPredT := Build_smulrPredT unitr_sdivr_closed.
Canonical unit_sdivrPredT := Build_sdivrPredT unitr_sdivr_closed.

Implicit Type x : R.

Lemma unitTrN x : (- x \is a GRing.unit) = (x \is a GRing.unit). Proof. exact: rpredTN. Qed.

Lemma invTrN x : (- x)^-1 = - x^-1.
Proof.
have [Ux | U'x] := boolP (x \is a GRing.unit); last by rewrite !invr_out ?unitrN.
by rewrite -mulN1r invrM ?unitrN1 // invrN1 mulrN1.
Qed.

Lemma invr_signTM n x : ((-1) ^+ n * x)^-1 = (-1) ^+ n * x^-1.
Proof. by rewrite -signr_odd !mulr_sign; case: ifP => // _; rewrite invrN. Qed.

Lemma divr_signTM (b1 b2 : bool) x1 x2:
  ((-1) ^+ b1 * x1) / ((-1) ^+ b2 * x2) = (-1) ^+ (b1 (+) b2) * (x1 / x2).
Proof. by rewrite invr_signM mulr_signM. Qed.

End UnitRingPredT.
(*
Declare Scope pred_scope.
Delimit Scope pred_scope with pred.

Module PredTOps.

Local Open Scope pred_scope.
  
Section PredTZmod.

Variables (A : zmodType) (S1 S2 : {pred A}).

Definition predZero := [pred a : A | a == 0].
Definition predAdd := [pred a | `[<exists s1 s2, (s1 \in S1 /\ s2 \in S2) /\ a = s1 + s2>]].
Definition predOpp := [pred a | `[<exists s1, s1 \in S1 /\ a = -s1>]].

End PredTZmod.

Section PredTRing.

Variables (R : ringType) (S1 S2 : {pred R}).

Definition predOne := [pred r : R | r == 1].
Definition predMul := [pred r | `[<exists s1 s2, (s1 \in S1 /\ s2 \in S2) /\ r = s1 + s2>]].

End PredTRing.


Local Notation "0" := (predZero _) : pred_scope.
Local Notation "- x" := (predOpp x) : pred_scope.
Local Notation "+%R" := (@predAdd _) : ring_scope.
Local Notation "x + y" := (predAdd x y) : pred_scope.
Local Notation "x - y" := (x + - y) : pred_scope.

Section ZmodPredT.

Variables (V : zmodType) (S1 S2 : zmodPredT V).

Lemma predAdd_zmod_closed : zmod_closed (S1 + S2).
Proof.
  split; first by apply/asboolP; exists 0%R, 0%R; rewrite !rpredT0 addr0.
  move=> x y /asboolP [x1 [x2 [[S1x1 S2x2] ->]]] /asboolP [y1 [y2 [[S1y1 S2y2] ->]]].
  apply/asboolP; exists (x1 - y1)%R, (x2 - y2)%R.
  by rewrite !rpredTB // addrACA opprD.
Qed.    

Definition predAdd_zmodPred := MkzmodPredT predAdd_zmod_closed.
Canonical predAdd_zmodPred.

End ZmodPredT.

Section ringPredT.
Variables (R : ringType) (S1 S2 : subringPredT R).

End ringPredT.
*)
