
From mathcomp Require Import ssreflect eqtype choice bigop ssreflect ssrbool ssrnat.
From mathcomp Require Import ssrfun fintype finfun seq ssralg generic_quotient.
From mathcomp Require Import tuple ring_quotient boolp ssrpred ideal subtypes.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section Functions.

Variables (A B : Type) (f : A -> B).

Definition image (S : pred A) : pred B := fun b => `[<exists a, a \in S /\ b = f a>].
Definition imageType (S : pred A) := { b | b \in image S}.
Lemma imageP S b : reflect (exists a, a \in S /\ b = f a) (b \in image S).
Proof. apply/asboolP. Qed.
Lemma imageTP S (b : imageType S) : exists a, a \in S /\ sval b = f a.
Proof. by apply/imageP/(svalP b). Qed.

Definition codomain := image predT.
Lemma codP b : reflect (exists a, b = f a) (b \in codomain).
Proof.
  apply: (iffP idP)=> [/imageP [a [_ ->]]| [a ->]]; first by exists a.
  by apply/imageP; exists a.
Qed.
Definition codType := imageType predT.
Lemma codTP (b : codType) : exists a, sval b = f a.
Proof. by apply/codP/(svalP b). Qed.

Definition surjective := forall b, exists a, f a = b.

Lemma bijP : injective f -> surjective -> bijective f.
Proof.
  move=> f_inj f_surj.
  pose f' b := projT1 (cid (f_surj b)).
  pose f'_ok b : f (f' b) = b := projT2 (cid (f_surj b)).
  have ff' : cancel f' f by exact: f'_ok.
  have f'f : cancel f f'. by move=> a; apply: f_inj.
  exact: (Bijective f'f ff').
Qed.

End Functions.

Notation "[ 'im' f 'of' S ]" := (image f S) (at level 0) : function_scope.
Notation "[ 'im' f ]" := (image f predT) (at level 0) : function_scope.
Notation "{ 'im' f S }" := (imageType f S) (at level 0) : function_scope.
Notation "[ 'cod' 'of' f ]" := (codomain f) (at level 0) : function_scope.
Notation "{ 'cod' f }" := (codType f) (at level 0) : function_scope.


Section ZmodAddf.

Variables (A B : zmodType) (ϕ : { additive A -> B}).

Lemma cod_zmod : zmod_closed [cod of ϕ].
Proof.
  split; first by apply/codP; exists 0; rewrite raddf0.
  move=> b1 b2 /codP [a1 ->] /codP [a2 ->].
  by apply/codP; exists (a1 - a2); rewrite raddfB.
Qed.

Canonical cod_zmodPred := @MkzmodPredT _ [cod of ϕ] cod_zmod.
Canonical cod_zmodType := SubTypes.zmod_subType cod_zmodPred.

End ZmodAddf.

Section RingMorphism.

Variables (R S : ringType) (ϕ : {rmorphism R -> S }).

Lemma cod_subring : mulr_closed [cod of ϕ].
Proof.
  split; first by apply/codP; exists 1; rewrite /= rmorph1.
  move=> s1 s2 /codP [r1 ->] /codP [r2 ->].
  by apply/codP; exists (r1 * r2); rewrite /= rmorphM.
Qed.
Print Canonical Projections.
Canonical cod_subringPred := @Build_subringPredT _ [cod of ϕ] cod_subring.
Canonical cod_subringType := SubTypes.zmod_subType cod_subringPred.

End RingMorphism.

Section IdealExamples.

Variables (R S : comRingType) (ϕ : {rmorphism R -> S }).
Definition ker_pred : {pred R} := [pred r | ϕ r == 0]. 
  
Lemma ker_ideal : ideal_theory ker_pred.
Proof.
  split; first by rewrite inE rmorph0.
  by move=> a x y; rewrite !inE rmorphD rmorphM=> /eqP -> /eqP ->; rewrite mulr0 addr0.
Qed.

Lemma ker_proper : proper_n1 ker_pred.
Proof.
  by rewrite /proper_n1 inE rmorph1 oner_neq0.
Qed.

Definition kerProperIdeal := @Build_proper_ideal _ (MkIdeal ker_ideal) ker_proper.

End IdealExamples.

Notation "{ 'ker' ϕ }" := (kerProperIdeal ϕ) : ideal_scope. 

Section KernelTheory.

Variables (R S : comRingType) (ϕ : {rmorphism R -> S }).

Lemma kerP r : reflect (ϕ r = 0) (r \in {ker ϕ}).
Proof. by apply/eqP. Qed.

Lemma ker_eq r s : (ϕ r == ϕ s) = (r - s \in {ker ϕ}).
Proof. by rewrite -subr_eq0 -rmorphB. Qed.
  
Lemma ker_eqP r s : reflect (ϕ r = ϕ s) ((r - s) \in {ker ϕ}).
Proof. by rewrite -ker_eq; apply/eqP. Qed.

End KernelTheory.

Section IdealApplication.

Local Open Scope ideal_scope.
Local Open Scope quotient_scope.
  
Variables (R S : comRingType) (ϕ : {rmorphism R -> S }).
Let ψ : R -> R / {ker ϕ} := \pi_(R / {ker ϕ}).

Fact η_ok (r : R / {ker ϕ}) : ϕ (repr r) \in [ cod of ϕ ].
Proof. by apply/codP; exists (repr r). Qed.

Let η : R / {ker ϕ} -> {cod ϕ} := fun r => Sub (ϕ (repr r)) (η_ok r).

Fact phi_eq r s : (ϕ r == ϕ s) = (ψ r == ψ s).
Proof.
  by rewrite ker_eq !piE.
Qed.

Fact phi_eqP r s : (ϕ r = ϕ s) <-> (ψ r = ψ s).
Proof.
  by split=> /eqP j; apply/eqP; rewrite ?phi_eq // -phi_eq.
Qed.

Lemma ηadd : additive η.
Proof.
  move=> a b; apply: val_inj; rewrite /= -rmorphB.
  by apply/phi_eqP; rewrite /ψ pi_addr pi_oppr !reprK.
Qed.

Definition η_additive := Additive ηadd.

Lemma ηmul : multiplicative η.
Proof.
  split=> [a b |]; apply: val_inj; first last.
    by rewrite /= -(rmorph1 ϕ); apply/phi_eqP; rewrite /ψ !piE reprK.
  by rewrite /= -rmorphM; apply/phi_eqP; rewrite /ψ pi_mulr !reprK.
Qed.

Lemma ηmorph : rmorphism η.
Proof. split; [apply/ηadd | apply/ηmul]. Qed.
Definition η_morphism := RMorphism ηmorph.

Lemma ηinj : bijective η.
Proof.
  apply/bijP.
  - move=> r1 r2 /(f_equal sval) /phi_eqP; by rewrite /ψ !reprK.
  - move=> s; case: (codTP s)=> r s_eq.
    exists (\pi r); apply: val_inj; rewrite /= s_eq.
    by apply/phi_eqP; rewrite /ψ reprK.
Qed.

End IdealApplication.

Section IdealIsomorphism.

Local Open Scope subtype_scope.
Variables (R : comRingType) (I : subringPred R) (J : proper_ideal R).

Let IT := { SubComRing I }.
Let IcapJpred : {pred IT} := [pred r | (sval r \in I) && (sval r \in J)].

Fact IJ_ideal_theory : ideal_theory IcapJpred.
Proof.
  split; first by rewrite inE !rpred0.
  move=> a u v /andP [Iu Ju] /andP [Iv Jv]; rewrite inE.
  by rewrite SubTypes.subP ideal_linear.
Qed.
Let IJideal := MkIdeal IJ_ideal_theory.

Fact IJn1 : proper_n1 IJideal.
Proof. by rewrite /proper_n1 inE prop_ideal1 andbC /=. Qed.

Let IcapJ := Build_proper_ideal IJn1.

Let LHS := IT / (IcapJ).

Let IplusJpred : {pred R} := [pred r | `[<exists a b, (a \in I /\ b \in J) /\ r = a + b>]].

Fact IpJadd : addr_closed IplusJpred.
Proof.
  split; first by apply/asboolP; exists 0, 0; rewrite !rpred0 add0r.
  move=> r1 r2 /asboolP [a1 [b1 [[Ia1 Jb1] ->]]] /asboolP [a2 [b2 [[Ia2 Jb2] ->]]].
  by apply/asboolP; exists (a1 + a2), (b1 + b2); rewrite !rpredD // addrACA.
Qed.

Fact IpJopp : oppr_closed IplusJpred.
Proof.
  move=> r /asboolP [a [b [[Ia Ib] ->]]]; apply/asboolP.
  by exists (-a), (-b); rewrite !rpredN -opprB opprK addrC.
Qed.

Fact IpJmul : mulr_closed IplusJpred.
Proof.
  split; first by apply/asboolP; exists 1, 0; rewrite rpred1 rpred0 addr0.
  move=> r1 r2 /asboolP [a1 [b1 [[Ia1 Jb1] ->]]] /asboolP [a2 [b2 [[Ia2 Jb2] ->]]].
  apply/asboolP; exists (a1 * a2), (a1 * b2 + (a2 + b2) * b1).
  by rewrite rpredM ?rpredD ?idealMr // mulrDl mulrDr addrA (mulrC b1).
Qed.

Let IpJzmod := @Build_zmodPred _ (Build_addrPred IpJadd) IpJopp.
Let IpJ := @Build_subringPred _ IpJzmod IpJmul.
Let IpJT := { SubComRing IpJ }.

Let Jpred : {pred IpJT} := [pred r | sval r \in J].
Fact Jideal_theory : ideal_theory Jpred.
Proof.
  split=> [| a u v]; rewrite !inE; first by exact: ideal0.
  by move=> Ju Jv; rewrite ideal_linear.
Qed.
Let Jideal := MkIdeal Jideal_theory.
Fact Jn1 : proper_n1 Jideal.
Proof. by rewrite /proper_n1 inE prop_ideal1. Qed.

Let Jsub := Build_proper_ideal Jn1.

Let RHS := IpJT / Jsub.
Fact f_ok (t : LHS) : sval (repr t) \in IpJ.
Proof.
  by apply/asboolP; exists (sval (repr t)), 0; rewrite (svalP (repr t)) ideal0 addr0.
Qed.
Let f : LHS -> RHS := fun t => \pi (Sub (sval (repr t)) (f_ok t)).

Structure equal_to T (x : T) := EqualTo {
   equal_val : T;
   _         : x = equal_val
}.
Lemma equal_toE (T : Type) (x : T) (m : equal_to x) : equal_val m = x.
Proof. by case: m. Qed.

Notation svalE := (@equal_toE _ _).

Canonical equal_to_sval T (P : {pred T}) (x : {x | x \in P} ) :=
  @EqualTo _ (sval x) (sval x) (erefl _).

Arguments EqualTo {T x equal_val}.

Fact f_add : additive f.
Proof.
  move=> x y; rewrite /f piE; apply/eqP.
  rewrite -Quotient.idealrBE inE /= -!SubTypes.svalB.
  have pi_eq : \pi_(LHS) (repr (x - y)) == \pi (repr x - repr y).
    by rewrite pi_addr pi_oppr !reprK.
  by move: (pi_eq); rewrite -Quotient.idealrBE inE=> /andP [_ ?].
Qed.

Fact f_mul : multiplicative f.
Proof.
  split=> [x y|]; apply/eqP; last first.
    rewrite -(pi_oner RHS) /f -Quotient.idealrBE.
    rewrite inE !SubK -(SubTypes.sval1 I) -SubTypes.svalB.
    have H : (repr (1 : LHS)) - 1 \in IcapJ by rewrite piE Quotient.idealrBE reprK. 
    by move: H; rewrite inE=> /andP [_ ?].
  rewrite /f -pi_mulr -Quotient.idealrBE inE !SubK -!SubTypes.svalM -SubTypes.svalB.
  have pi_eq : \pi_(LHS) (repr (x * y)) == \pi (repr x * repr y).
    by rewrite pi_mulr !reprK.
  by move: pi_eq; rewrite -Quotient.idealrBE inE=> /andP [_ ?].
Qed.

Fact f_morph : rmorphism f.
Proof. split; [ exact: f_add | exact: f_mul]. Qed.

Definition f_morphism := RMorphism f_morph.

Fact f_inj : injective f.
Proof.
  move=> x y /eqP fxy.
  apply/eqP; rewrite -[x]reprK -[y]reprK -Quotient.idealrBE.
  apply/andP; split; first by exact: SubTypes.subP.
  by rewrite -Quotient.idealrBE inE /= -SubTypes.svalB in fxy.
Qed.

Fact f_surj : surjective f.
Proof.
  move=> xbar; move: (svalP (repr xbar))=> /asboolP [a [b [[Ia Jb] xbar_eq]]].
  exists (\pi (Sub a Ia)); apply/eqP; rewrite /f -[xbar]reprK -Quotient.idealrBE inE !SubK.
  have a_sub : a = sval (Sub a Ia) by [].
  rewrite xbar_eq {2}a_sub -[b]opprK opprB addrC -addrA addrC idealB //.
  rewrite addrC -SubTypes.svalB.
  have H : \pi_(LHS) (repr (\pi_(LHS) (Sub a Ia))) == \pi (Sub a Ia) by rewrite reprK.
  by move: H; rewrite -Quotient.idealrBE inE=> /andP [_ ?].
Qed.
Fact f_bij : bijective f. Proof. exact: bijP f_inj f_surj. Qed.

End IdealIsomorphism.
