From mathcomp Require Import ssreflect eqtype choice bigop ssreflect ssrbool ssrnat.
From mathcomp Require Import ssrfun seq ssralg generic_quotient ring_quotient.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope quotient_scope.
Local Open Scope seq_scope.

Section IdealDef.

Structure idealr (R : ringType) (S : {pred R}) := MkIdeal {
  idealr_zmod :> zmodPred S;
  idealr_mul_cls : forall a, {in S, forall u, a * u \in S}
}.

Structure proper_idealr (R : ringType) (S : {pred R}) := MkProperIdeal {
  proper_idealr_ideal :> idealr S;
  proper_idealr_proper : 1 \notin S
}.

Structure prime_idealr (R : ringType) (S : {pred R}) := MkPrimeIdeal {
  prime_idealr_ideal :> proper_idealr S;
  prime_idealr_closed : forall u v, u * v \in S -> (u \in S) || (v \in S)
}.

Section IdealTheory.
Variables (R : ringType) (I : {pred R})
          (idealrI : idealr I) (kI : keyed_pred idealrI).

Lemma idealMr a u : u \in kI -> a * u \in kI.
Proof.
by case: idealrI kI=> ? /= hI [? hkI]; rewrite !hkI; apply: hI.
Qed.

Lemma idealr0 : 0 \in kI. Proof. exact: rpred0. Qed.
End IdealTheory.

Section ProperIdealTheory.

Variables (R : ringType) (I : {pred R})
          (propidealrI : proper_idealr I) (kI : keyed_pred propidealrI).

Lemma propidealr1 : 1 \in kI = false.
Proof. by apply: negPf; case: propidealrI kI => [_ ?] /= [_ ->]. Qed.

End ProperIdealTheory.

Section PrimeIdealTheory.

Variables (R : comRingType) (I : {pred R})
          (pidealrI : prime_idealr I) (kI : keyed_pred pidealrI).

Lemma prime_idealrM u v : (u * v \in kI) = (u \in kI) || (v \in kI).
Proof.
apply/idP/idP; last by case/orP => /idealMr hI; rewrite // mulrC.
by case: pidealrI kI=> ? /= hI [] /= ? hkI; rewrite !hkI; apply: hI.
Qed.

End PrimeIdealTheory.

End IdealDef.

Section ZmodQuotient.
Variables (R : zmodType) (I : {pred R})
          (zmodI : zmodPred I) (kI : keyed_pred zmodI).

Definition equiv (x y : R) := (x - y) \in kI.

Lemma equivE x y : (equiv x y) = (x - y \in kI). Proof. by []. Qed.

Lemma equiv_is_equiv : equiv_class_of equiv.
Proof.
split=> [x|x y|y x z]; rewrite !equivE ?subrr ?rpred0 //.
   by rewrite -opprB rpredN.
by move=> *; rewrite -[x](addrNK y) -addrA rpredD.
Qed.

Canonical equiv_equiv := EquivRelPack equiv_is_equiv.
Canonical equiv_encModRel := defaultEncModRel equiv.

Definition type := {eq_quot equiv}.
Definition type_of of phant R := type.

Canonical rquot_quotType := [quotType of type].
Canonical rquot_eqType := [eqType of type].
Canonical rquot_choiceType := [choiceType of type].
Canonical rquot_eqQuotType := [eqQuotType equiv of type].

Lemma idealrBE x y : (x - y) \in kI = (x == y %[mod type]).
Proof. by rewrite piE equivE. Qed.

Lemma idealrDE x y : (x + y) \in kI = (x == - y %[mod type]).
Proof. by rewrite -idealrBE opprK. Qed.

Definition zero : type := lift_cst type 0.
Definition add := lift_op2 type +%R.
Definition opp := lift_op1 type -%R.

Canonical pi_zero_morph := PiConst zero.

Lemma pi_opp : {morph \pi : x / - x >-> opp x}.
Proof.
move=> x; unlock opp; apply/eqP; rewrite piE equivE.
by rewrite -opprD rpredN idealrDE opprK reprK.
Qed.

Canonical pi_opp_morph := PiMorph1 pi_opp.

Lemma pi_add : {morph \pi : x y / x + y >-> add x y}.
Proof.
move=> x y /=; unlock add; apply/eqP; rewrite piE equivE.
rewrite opprD addrAC addrA -addrA.
by rewrite rpredD // (idealrBE, idealrDE) ?pi_opp ?reprK.
Qed.
Canonical pi_add_morph := PiMorph2 pi_add.

Lemma addqA: associative add.
Proof. by move=> x y z; rewrite -[x]reprK -[y]reprK -[z]reprK !piE addrA. Qed.

Lemma addqC: commutative add.
Proof. by move=> x y; rewrite -[x]reprK -[y]reprK !piE addrC. Qed.

Lemma add0q: left_id zero add.
Proof. by move=> x; rewrite -[x]reprK !piE add0r. Qed.

Lemma addNq: left_inverse zero opp add.
Proof. by move=> x; rewrite -[x]reprK !piE addNr. Qed.

Definition rquot_zmodMixin := ZmodMixin addqA addqC add0q addNq.
Canonical rquot_zmodType := Eval hnf in ZmodType type rquot_zmodMixin.

Definition rquot_zmodQuotMixin := ZmodQuotMixin type (lock _) pi_opp pi_add.
Canonical rquot_zmodQuotType := ZmodQuotType 0 -%R +%R type rquot_zmodQuotMixin.

End ZmodQuotient.

Notation "{quot I }" := (@type_of _ _ _ I (Phant _)).


Section RingQuotient.

Variables (R : comRingType) (I : {pred R})
          (propidealI : proper_idealr I) (kI : keyed_pred propidealI).

Local Notation type := {quot kI}.

Definition one: type := lift_cst type 1.
Definition mul := lift_op2 type *%R.

Canonical pi_one_morph := PiConst one.

Lemma pi_mul: {morph \pi : x y / x * y >-> mul x y}.
Proof.
move=> x y; unlock mul; apply/eqP; rewrite piE equivE.
rewrite -[_ * _](addrNK (x * repr (\pi_type y))) -mulrBr.
rewrite -addrA -mulrBl rpredD //.
  by rewrite idealMr // idealrDE opprK reprK.
by rewrite mulrC idealMr // idealrDE opprK reprK.
Qed.
Canonical pi_mul_morph := PiMorph2 pi_mul.

Lemma mulqA: associative mul.
Proof. by move=> x y z; rewrite -[x]reprK -[y]reprK -[z]reprK !piE mulrA. Qed.

Lemma mulqC: commutative mul.
Proof. by move=> x y; rewrite -[x]reprK -[y]reprK !piE mulrC. Qed.

Lemma mul1q: left_id one mul.
Proof. by move=> x; rewrite -[x]reprK !piE mul1r. Qed.

Lemma mulq_addl: left_distributive mul +%R.
Proof.
move=> x y z; rewrite -[x]reprK -[y]reprK -[z]reprK.
by apply/eqP; rewrite piE /= mulrDl equiv_refl.
Qed.

Lemma nonzero1q: one != 0.
Proof. by rewrite piE equivE subr0 propidealr1. Qed.

Definition rquot_comRingMixin :=
  ComRingMixin mulqA mulqC mul1q mulq_addl nonzero1q.

Canonical rquot_ringType    := Eval hnf in RingType type rquot_comRingMixin.
Canonical rquot_comRingType := Eval hnf in ComRingType type mulqC.

Definition rquot_ringQuotMixin := RingQuotMixin type (lock _) pi_mul.
Canonical rquot_ringQuotType := RingQuotType 1 *%R type rquot_ringQuotMixin.

End RingQuotient.


Section IDomainQuotient.

Variables (R : comRingType) (I : {pred R})
          (pidealI : prime_idealr I) (kI : keyed_pred pidealI).

Lemma rquot_IdomainAxiom (x y : {quot kI}): x * y = 0 -> (x == 0) || (y == 0).
Proof.
by move=> /eqP; rewrite -[x]reprK -[y]reprK !piE !equivE !subr0 prime_idealrM.
Qed.

End IDomainQuotient.


Section IdealGen.

Variables (R : comRingType) (Λ : Type) (a_λ : Λ -> R).

Definition gen_ideal (I : {pred R}) := forall r,
    r \in I <-> exists lxs : seq (Λ * R), r = \sum_(i <- lxs) (i.2 * a_λ i.1).

Lemma gen_ideal_addr I : gen_ideal I -> addrPred I.
Proof.
  move=> genI; split; first by [].
  split; first by apply/genI; exists nil; rewrite big_nil.
  move=> x y /genI [x_gen ->] /genI [y_gen ->]; apply/genI.
  by exists (x_gen ++ y_gen); rewrite big_cat.
Qed.
  
Lemma gen_ideal_zmod I : gen_ideal I -> zmodPred I.
Proof.
  move=> genI; split; first by exact: gen_ideal_addr.
  move=> x /genI [x_gen ->]; apply/genI; exists [seq (p.1, -p.2) | p <- x_gen].
  rewrite (big_morph -%R (id1 := 0) (op1 := +%R)); last by exact: oppr0.
  by rewrite big_map; apply: eq_bigr => i _; rewrite mulNr.
  by move=> a b; rewrite -{1}[b]opprK opprB addrC.
Qed.

Lemma gen_ideal_idealr I : gen_ideal I -> idealr I.
Proof.
  move=> genI; split; first by exact: gen_ideal_zmod.
  move=> r x /genI [x_gen ->]; apply/genI; exists [seq (p.1, r * p.2) | p <- x_gen].
  by rewrite big_distrr big_map; apply: eq_bigr => i _ /=; rewrite mulrA.
Qed.

Variables (I : {pred R}) (genI : gen_ideal I)
          (kI : keyed_pred (gen_ideal_idealr genI)).

Lemma gen_ideal_contains : forall λ, a_λ λ \in kI.
Proof.
  case kI=> [? hkI] λ; rewrite !hkI; apply/genI.
  by exists [:: (λ, 1)]; rewrite big_cons big_nil addr0 mul1r.
Qed.
  
Lemma gen_ideal_min : forall J (idealJ : idealr J) (kJ : keyed_pred idealJ), (forall λ, a_λ λ \in kJ) -> {subset kI <= kJ}.
Proof.
  case kI=> [? hkI] J idealJ kJ a_λ_in_J x.
  rewrite !hkI=> /genI [x_gen ->].
  apply: (big_rec (fun y => y \in kJ)); first by apply: idealr0.
  move=> lxs y _ y_in_J; apply: rpredD; last by [].
  by apply: idealMr.
Qed.
    
End IdealGen.

