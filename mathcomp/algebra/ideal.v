(* -*- company-coq-local-symbols: (("<~>" . ?↭) ("\mathfrak{b}" . ?𝔞)); -*- *)

From mathcomp Require Import ssreflect eqtype choice bigop ssreflect ssrbool ssrnat.
From mathcomp Require Import ssrfun fintype finfun seq ssralg generic_quotient.
From mathcomp Require Import tuple ring_quotient.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope. 
Local Open Scope quotient_scope.
Local Open Scope seq_scope.

Axiom classic : forall P, decidable P.

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

Structure maximal_idealr (R : comRingType) (S : {pred R}) := MkMaximalIdeal {
  maximal_idealr_proper : proper_idealr S;
  maximal_idealr_max : forall T, proper_idealr T -> {subset T <= S}
}.

  
Section IdealEq.
Variables (R : ringType) (I J : {pred R}).

Lemma eq_ideal : I =i J -> idealr I -> idealr J.
Proof.
  move=> H [[[? [z_in add_cls]] opp_cls] mul_cls].
  split; first split; first split; first by [].
  split; first by rewrite -!H.
  by move=> u v; rewrite -!H; apply: add_cls.
  by move=> x; rewrite -!H; apply opp_cls.
  by move=> a u; rewrite -!H; apply mul_cls.
Qed.

End IdealEq.

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

Lemma prop_idealr1 : 1 \in kI = false.
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

(*
Section MaximalIdealTheory.

Variables (R : ringType) (I : {pred R})
          (midealrI : maximal_idealr I) (kI : keyed_pred midealrI).

Lemma max_idealr : forall T, proper_idealr T -> {subset T <= kI}.
Proof.
  case: midealrI kI => [? maxI] /= [? hkI] T Tpropideal a a_in_T.
  by rewrite !hkI; apply: (maxI T).
Qed.  

Lemma max_proper_idealr : proper_idealr I.
Proof.
  by case: midealrI=> ? _.
Qed.

End MaximalIdealTheory.
*)
End IdealDef.

Section GenIdeal.

Variables (R : ringType) (Λ : Type) (as' : Λ -> R).
Definition gen_pred r := exists (n: nat) (λs : n.-tuple Λ) (xs : n.-tuple R),
    r = \sum_i (tnth xs i * as' (tnth λs i)).
Definition genI : {pred R} := fun r => classic (gen_pred r).


Lemma gen_addr : addrPred genI.
Proof.
  split; first by [].
  split; first by apply/sumboolP; exists 0%nat, [tuple], [tuple]; rewrite big_ord0.
  move=> r s /sumboolP [rn [rλs [rxs ->]]] /sumboolP [sn [sλs [sxs ->]]]; apply/sumboolP.
  have size_rsλ : (size (rλs ++ sλs) == (rn + sn)%nat) by apply: cat_tupleP.
  have size_rsx : (size (rxs ++ sxs) == (rn + sn)%nat) by apply: cat_tupleP.
  exists (rn + sn)%nat, (Tuple size_rsλ), (Tuple size_rsx).
  rewrite big_split_ord; congr(_ + _).
    apply: eq_bigr=> i _; have i_lt_rn : i < rn by [].
    by congr(_ * _); rewrite {2}/tnth nth_cat size_tuple i_lt_rn -tnth_nth.
  apply: eq_bigr=> i _.
  have rn_i_rn : (rn + i < rn = false) by rewrite ltnNge leq_addr.
  congr(_ * _); rewrite {2}/tnth nth_cat size_tuple /= rn_i_rn.
    rewrite (tnth_nth (tnth_default (Tuple size_rsx) (rshift rn i))).
    by congr (nth _ _ _); rewrite -{2}[rn]addn0 subnDl subn0.
  rewrite (tnth_nth (tnth_default (Tuple size_rsλ) (rshift rn i))).
  by congr (as' (nth _ _ _)); rewrite -{2}[rn]addn0 subnDl subn0.
Qed.

Lemma gen_zmod : zmodPred genI.
Proof.
  split; first by exact: gen_addr.
  move=> r /sumboolP [rn [rλs [rxs ->]]]; apply/sumboolP.
  exists rn, rλs, [tuple -(tnth rxs i) | i < rn].
  rewrite (big_morph -%R (id1 := 0) (op1 := +%R)); last by exact: oppr0.
    by apply: eq_bigr=> i _; rewrite tnth_map mulNr tnth_ord_tuple.
  by move=> x y; rewrite -{1}[y]opprK opprB addrC.
Qed.

Lemma gen_idealr : idealr genI.
  split; first by exact: gen_zmod.
  move=> a r /sumboolP [rn [rλs [rxs ->]]]; apply/sumboolP.
  exists rn, rλs, [tuple a * (tnth rxs i) | i < rn]; rewrite big_distrr.
  by apply: eq_bigr=> i _ /=; rewrite tnth_map tnth_ord_tuple mulrA.
Qed.

Variable (kI : keyed_pred gen_idealr).

Lemma gen_contains : forall λ, as' λ \in kI.
Proof.
  case kI=> [? hkI] λ; rewrite !hkI; apply/sumboolP.
  by exists 1%nat, [tuple λ], [tuple 1]; rewrite big_ord_recl big_ord0 addr0 !tnth0 mul1r. 
Qed.
  
Lemma gen_ideal_min : forall J (idealJ : idealr J) (kJ : keyed_pred idealJ), (forall λ, as' λ \in kJ) -> {subset kI <= kJ}.
Proof.
  case kI=> [? hkI] J idealJ kJ a_λ_in_J x.
  rewrite !hkI=> /sumboolP [rn [rλs [rxs ->]]].
  apply: (big_rec (fun y => y \in kJ)); first by apply: idealr0.
  move=> lxs y _ y_in_J; apply: rpredD; last by [].
  by apply: idealMr.
Qed.

End GenIdeal.

Section FinGenIdeal.

Variables (R : ringType) (n : nat) (a : n.-tuple R).
Definition fingen_pred r := exists x : n.-tuple R, r = \sum_(i < n) tnth x i * tnth a i.
Definition fingenI : {pred R} := fun r => classic (fingen_pred r).

Let as' : 'I_n -> R := [ffun i => tnth a i].

Lemma gen_fingen r : gen_pred as' r -> fingen_pred r.
Proof.
  move=> [rn [rλs [rxs ->]]].
  exists [tuple (\sum_(j < rn | (tnth rλs j) == i) tnth rxs j) | i < n].
  rewrite (partition_big (fun i => tnth rλs i) predT) /=; last by [].
  apply: eq_bigr=> i _; rewrite tnth_map big_distrl tnth_ord_tuple.
  by apply: eq_bigr=> j /eqP ->; rewrite /as' ffunE.
Qed.

Lemma fingen_gen r : fingen_pred r -> gen_pred as' r.
Proof.
  move=> [x ->]; exists n, (ord_tuple n), [tuple (tnth x i) | i < n].
  by apply: eq_bigr=> i _; rewrite /as' tnth_map ffunE tnth_ord_tuple.
Qed.  

Lemma fingen_idealr : idealr fingenI.
  apply: (eq_ideal (I := genI as')).
    move=> r; apply/sumboolP/sumboolP; first by apply: gen_fingen.
    by apply: fingen_gen.
  by apply: gen_idealr.    
Qed.

Definition kfingen_ideal := keyed_pred fingen_idealr.

End FinGenIdeal.

Section PrincipalIdeal.

Variables (R : ringType) (a : R).
Definition principalI : {pred R} := fingenI [tuple a].
Definition principal_idealr : idealr principalI := fingen_idealr [tuple a].

Lemma ideal_principal_ex r : r \in principalI ->
  exists x, r = x * a.
Proof.
  move=> /sumboolP [t ->].
  by exists (tnth t ord0); rewrite big_ord_recl big_ord0 addr0 tnth0.
Qed.

Lemma ideal_ex_principal r : (exists x, r = x * a) -> r \in principalI.
Proof.
  move=> [x ->]; apply/sumboolP.
  by exists [tuple x]; rewrite big_ord_recl big_ord0 !tnth0 addr0.
Qed.

Lemma ideal_principal_in : a \in principalI.
Proof.
  by apply: ideal_ex_principal; exists 1; rewrite mul1r.
Qed.
End PrincipalIdeal.

Notation "(' a )" := (principalI a).


Section IdealGenIdeal.

Variables (R : ringType) (Λ : Type) (𝔞s : Λ -> {pred R})
          (ideals𝔞 : forall λ, idealr (𝔞s λ)) (k𝔞s : forall λ, keyed_pred (ideals𝔞 λ)).

Definition idealgen_pred r := exists n (λs : n.-tuple Λ) as' xs,
    (forall i, (tnth as' i) \in k𝔞s (tnth λs i)) /\ (r == \sum_i (tnth xs i) * (tnth as' i)).
Definition idealgenI : {pred R} := fun r => classic (idealgen_pred r).

Inductive Λ' : Type :=
  Lambda' λ r : r \in (k𝔞s λ) -> Λ'.
Let as' λ' := match λ' with | Lambda' λ r r_in_I_λ => r end.

Lemma gen_gen_ideal r : gen_pred as' r -> idealgen_pred r.
Proof.
  move=> [rn [rλs [rxs ->]]].
  exists rn, [tuple let (λ, _, _) := (tnth rλs i) in λ | i < rn],
    [tuple let (_, x, _) := (tnth rλs i) in x | i < rn], rxs; split.
    by move=> i; rewrite !tnth_map tnth_ord_tuple; case (tnth rλs i).
  by apply/eqP; apply: eq_bigr=> i _; rewrite tnth_map tnth_ord_tuple.
Qed.

Lemma gen_ideal_gen r : idealgen_pred r -> gen_pred as' r.
Proof.
  move=> [rn [rλs [ras [rxs [ras_in_𝔞s /eqP ->]]]]].
  exists rn, [tuple (Lambda' (ras_in_𝔞s i)) | i < rn], rxs.
  apply: eq_bigr=> i _; by rewrite tnth_map tnth_ord_tuple.
Qed.

Lemma gen_ideal_idealr : idealr idealgenI.
Proof.
  apply: (eq_ideal (I := genI as')).
    move=> r; apply/sumboolP/sumboolP; first by apply: gen_gen_ideal.
    by apply: gen_ideal_gen.
  by apply: gen_idealr.    
Qed.
  
End IdealGenIdeal.

Section IdealOps.

Variables (R : ringType) (I J : {pred R})
          (idealI : idealr I) (kI : keyed_pred idealI)
          (idealJ : idealr J) (kJ : keyed_pred idealJ).

Definition addi_prop r := exists a b, (a \in I /\ b \in J /\ r = a + b).
Definition addi : {pred R} := fun r => classic (addi_prop r).

Lemma addi_idealr : idealr addi.
  case idealI=> [[[_ [H0_in_I I_predD]] I_predNr] I_idealMr].
  case idealJ=> [[[_ [H0_in_J J_predD]] J_predNr] J_idealMr].
  split; first split; first split; first by [].
  - split; first apply/sumboolP.
      exists 0, 0; split; first by [].
      split; first by [].
      by rewrite addr0.
    move=> x y /sumboolP [xa [xb [xa_in [xb_in ->]]]].
    move=> /sumboolP [ya [yb [ya_in [yb_in ->]]]]; apply/sumboolP.
    exists (xa + ya), (xb + yb); split; first by apply: I_predD.
    split; first by apply: J_predD.
    by rewrite (addrC xa) addrA -(addrA xb) (addrC xb) addrA.
  - move=> x /sumboolP [xa [xb [xa_in [xb_in ->]]]]; apply /sumboolP.
    exists (-xa), (-xb); split; first by apply: I_predNr.
    split; first by apply: J_predNr.
    by apply: addr0_eq; rewrite addrC (addrC xa) subrKA addNr.
  - move=> a x /sumboolP [xa [xb [xa_in [xb_in ->]]]]; apply /sumboolP.
    exists (a * xa), (a * xb); split; first by apply: I_idealMr.
    split; first by apply: J_idealMr.
    by rewrite mulrDr.
Qed.

Lemma addi_inl x : x \in I -> x \in addi.
Proof.
  case idealJ=> [[[_ [H0_in_J J_predD]] J_predNr] J_idealMr].
  move=> H; apply/sumboolP.
  exists x, 0; split; first by [].
  split; first by [].
  by rewrite addr0.
Qed.

Lemma addi_inr x : x \in J -> x \in addi.
Proof.
  case idealI=> [[[_ [H0_in_I I_predD]] I_predNr] I_idealMr].
  move=> H; apply/sumboolP.
  exists 0, x; split; first by [].
  split; first by [].
  by rewrite add0r.
Qed.


Lemma addi_ex : forall x, x \in addi -> exists a b, (a \in kI /\ b \in kJ /\ x = a + b).
Proof.
  case: kI kJ=> [? hkI] [? hkJ] x /sumboolP [xa [xb [xa_in [xb_in ->]]]].
  by exists xa, xb; rewrite !hkI !hkJ.
Qed.
  
End IdealOps.

Declare Scope ideal_scope.
Open Scope ideal_scope.

Notation "I +i J" := (addi I J) (at level 0) : ideal_scope.

Section MaximalIdealTheory.
  
Lemma maximal_prime_idealr : forall (R : comRingType) (S : {pred R}), maximal_idealr S -> prime_idealr S.
Proof.
  move=> R S [properS maxS]; split=> [| x y xy_in_S]; first by [].
  apply: contraT; rewrite negb_or=> /andP [x_notin_S /negbTE y_notin_S].
  set (T := S +i ('x)); case: (1 \in T) /idP=>
  [/sumboolP [a [? [a_in_S [/ideal_principal_ex [b -> H1_eq_abx]]]]] |/idP H1_notin_T].
    case: properS=> [[[[? [? SpredD]] ?] SidealMr] ?].
    rewrite -[y]mul1r H1_eq_abx mulrDl -mulrA mulrC in y_notin_S.
    apply: (contraFT _ y_notin_S)=> ?.
    apply: SpredD; first by apply: SidealMr.
    by apply: SidealMr.
  have properT : proper_idealr T.
    split; last by apply: H1_notin_T.
    apply addi_idealr; first by apply: properS.
    apply principal_idealr.
  have contra := maxS T properT x.
  have x_in_T : x \in T.
    apply: addi_inr; first by apply: properS.
    by apply: ideal_principal_in.
  have x_in_S := contra x_in_T.
  by rewrite x_in_S in x_notin_S.
Qed.

Coercion maximal_prime_idealr : maximal_idealr >-> prime_idealr.

Variables (R : comRingType) (I : {pred R})
          (midealrI : maximal_idealr I) (kI : keyed_pred midealrI).

Lemma max_idealr : forall T, proper_idealr T -> {subset T <= kI}.
Proof.
  case: midealrI kI => [? maxI] /= [? hkI] T Tpropideal a a_in_T.
  by rewrite !hkI; apply: (maxI T).
Qed.  

Lemma max_proper_idealr : proper_idealr I.
Proof.
  by case: midealrI=> ? _.
Qed.


End MaximalIdealTheory.


Module Quotient.

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
Proof. by rewrite piE equivE subr0 prop_idealr1. Qed.

Definition rquot_comRingMixin :=
  ComRingMixin mulqA mulqC mul1q mulq_addl nonzero1q.

Canonical rquot_ringType    := Eval hnf in RingType type rquot_comRingMixin.
Canonical rquot_comRingType := Eval hnf in ComRingType type mulqC.

Definition rquot_ringQuotMixin := RingQuotMixin type (lock _) pi_mul.
Canonical rquot_ringQuotType := RingQuotType 1 *%R type rquot_ringQuotMixin.

End RingQuotient.

Section comUnitRingQuotient.

Variables (R : comRingType) (I : {pred R})
          (propidealI : proper_idealr I) (kI : keyed_pred propidealI).

Local Notation type := {quot kI}.

Definition unit : pred {quot kI} := fun x => classic (exists x'', x'' * x == 1).

Lemma inv_exists (x : {quot kI}) : exists x',
    if (x \in unit) then (x' * x == 1) else x' == x.
Proof.
  case: (x \in unit) /idP=> [/sumboolP [x' x'x_eq_1] | x_nonunit]; first by exists x'.
  exists x; by rewrite /=.
Qed.  

Definition inv_sig (x : {quot kI}) := sigW (inv_exists x).
Definition inv_fun_sig := all_tag inv_sig.

Definition inv : {quot kI} -> {quot kI}.
Proof.
  move: inv_fun_sig => [f _]; exact: f.
Defined.

Lemma mulqVx : {in unit, left_inverse 1 inv *%R}.
Proof.
  rewrite /inv; move: inv_fun_sig=> [f Hf].
  move=> x x_unit; move: (Hf x).
  by rewrite x_unit=> /eqP.
Qed.

Lemma unitqPl : forall x y, y * x = 1 -> unit x.
Proof.
  move=> x y yx_eq_1; apply/sumboolP.
  by exists y; apply/eqP.
Qed.

Lemma invq0id : {in [predC unit], inv =1 id}.
Proof.
  rewrite /inv; move: inv_fun_sig=> [f Hf].
  move=> x /negbTE /= x_nonunit; move: (Hf x).
  by rewrite x_nonunit=> /eqP.
Qed.

Definition rquot_comUnitRingMixin := ComUnitRingMixin mulqVx unitqPl invq0id.

Canonical rquot_UnitRingType := Eval hnf in UnitRingType type rquot_comUnitRingMixin.
Canonical rquot_comUnitRingType := Eval hnf in
 [comUnitRingType of type].

End comUnitRingQuotient.

Section IDomainQuotient.

Variables (R : comRingType) (I : {pred R})
          (pidealI : prime_idealr I) (kI : keyed_pred pidealI).

Local Notation type := {quot kI}.

  
Lemma rquot_IdomainAxiom (x y : {quot kI}): x * y = 0 -> (x == 0) || (y == 0).
Proof.
by move=> /eqP; rewrite -[x]reprK -[y]reprK !piE !equivE !subr0 prime_idealrM.
Qed.

Canonical rquot_idomainType := Eval hnf in IdomainType type rquot_IdomainAxiom.

End IDomainQuotient.

Section FieldQuotient.

Variables (R : comRingType) (I : {pred R})
          (midealI : maximal_idealr I) (kI : keyed_pred midealI).

Local Notation type := {quot kI}.

Lemma rquot_FieldAxiom (x : {quot kI}): (x != 0) -> x \is a GRing.unit.
Proof.
  case: (x == 0) /idP=> [x_eq_0 | x_neq_0 _]; first by [].
  apply/sumboolP; set J := (I +i ('(repr x))).
  case: (1 \in J) /idP=> [/sumboolP [a [y [a_in [/ideal_principal_ex [b ->] H1_eq_a_b]]]] | /idP H1_notin].
    exists (\pi b); rewrite -[x]reprK !piE !Quotient.equivE.
    rewrite /= H1_eq_a_b (addrC a) -{1}[b * repr x]add0r addrKA add0r rpredN.
    by case kI=> [? hkI]; rewrite hkI.
  have J_proper : proper_idealr J.
    split; first apply: addi_idealr.
    - by apply: midealI.
    - by apply: principal_idealr.
    apply: H1_notin.
  have J_leq_I := max_idealr kI J_proper (x := repr x).
  have x_in_J : repr x \in J.
    apply: addi_inr; first by apply: midealI.
    by apply: ideal_ex_principal; exists 1; by rewrite mul1r.
  have x_in_I := J_leq_I x_in_J.
  by rewrite -[x]reprK !piE !Quotient.equivE subr0 x_in_I in x_neq_0.
Qed.

Canonical rquot_fieldType := Eval hnf in FieldType type rquot_FieldAxiom.

End FieldQuotient.

End Quotient.

Notation "{ideal_quot I }" := (@Quotient.type_of _ _ _ I (Phant _)).
Notation "x == y %[mod_ideal I ]" :=
  (x == y %[mod {ideal_quot I}]) : quotient_scope.
Notation "x = y %[mod_ideal I ]" :=
  (x = y %[mod {ideal_quot I}]) : quotient_scope.
Notation "x != y %[mod_ideal I ]" :=
  (x != y %[mod {ideal_quot I}]) : quotient_scope.
Notation "x <> y %[mod_ideal I ]" :=
  (x <> y %[mod {ideal_quot I}]) : quotient_scope.

Canonical Quotient.rquot_eqType.
Canonical Quotient.rquot_choiceType.
Canonical Quotient.rquot_zmodType.
Canonical Quotient.rquot_ringType.
Canonical Quotient.rquot_comRingType.
Canonical Quotient.rquot_quotType.
Canonical Quotient.rquot_eqQuotType.
Canonical Quotient.rquot_zmodQuotType.
Canonical Quotient.rquot_ringQuotType.


(*
Section IdealOps.


Variables (R : ringType) (I J : {pred R})
          (idealI : idealr I) (kI : keyed_pred idealI)
          (idealJ : idealr J) (kJ : keyed_pred idealJ).

Definition addi_prop r := exists ab, ((ab.1 \in kI) && (ab.2 \in kJ) && (r == ab.1 + ab.2)).
Definition addi : {pred R} := fun r => classic (addi_prop r).

Lemma addi_addr : addrPred addi.
Proof.
  split; first by []; split.
    apply/sumboolP; exists (0, 0); apply/andP; split; last by rewrite addr0.
    apply/andP; split; by exact: idealr0.
  move=> x y /sumboolP [[xa xb] /andP [/andP [? ?]] /eqP ->].
  move=> /sumboolP [[ya yb] /andP [/andP [? ?]] /eqP ->]; apply /sumboolP.
  exists ((xa + ya), (xb + yb)); apply/andP; split.
    by apply/andP; split; apply: rpredD.
  by apply/eqP; rewrite /= (addrC xa); rewrite addrA -(addrA xb) (addrC xb) addrA.
Qed.

Lemma addi_zmod : zmodPred addi.
Proof.
  split; first by exact: addi_addr.
  move=> x /sumboolP [[xa xb] /andP [/andP [? ?]] /eqP ->]; apply/sumboolP.
  exists ((-xa), (-xb)); apply/andP; split.
    by apply/andP; split; exact: rpredNr.
  by apply/eqP; apply: addr0_eq; rewrite addrC (addrC xa) subrKA addNr.
Qed.

Lemma addi_idealr : idealr addi.
Proof.
  split; first by exact: addi_zmod.
  move=> a x /sumboolP [[xa xb] /andP [/andP [? ?]] /eqP ->]; apply/sumboolP.
  exists ((a * xa), (a * xb)); apply/andP; split.
    apply/andP; split; by exact: idealMr.
  by apply/eqP; rewrite mulrDr.
Qed.

Definition keyed_addi := keyed_ideal_default addi_idealr.

Lemma addi_ex x : x \in keyed_addi -> addi_prop x.
Proof.
  case: keyed_addi=> [? hkIJ]; rewrite hkIJ=> x_in.
  apply/(sumboolP (classic _)); exact x_in.
Qed.


  

Definition muli_prop r := exists abs, all (fun ab => (ab.1 \in kI) && (ab.2 \in kJ)) abs
     /\ r = \sum_(i <- abs) i.1 * i.2.
Definition muli : {pred R} := fun r => classic (muli_prop r).

Lemma muli_addr : addrPred muli.
Proof.
  split; first by []; split.
    apply/sumboolP; exists nil; split; first by rewrite all_nil.
    by rewrite big_nil.
  move=> x y /sumboolP [xab [xab_in ->]] /sumboolP [yab [yab_in ->]].
  apply/sumboolP; exists (xab ++ yab); split; first by rewrite all_cat xab_in yab_in.
  by rewrite big_cat.
Qed.

Lemma muli_zmod : zmodPred muli.
Proof.
  split; first by exact: muli_addr.
  move=> x /sumboolP [xab [xab_in ->]]; apply/sumboolP.
  exists [seq (-ab.1, ab.2) | ab <- xab]; split; move: xab_in=> /all_nthP xab_in.
    apply/(all_nthP (0, 0))=> i i_leq_sz; rewrite size_map in i_leq_sz.
    rewrite (nth_map (0, 0)) //.
    move: xab_in=> /(_ (0, 0) i i_leq_sz) xabi_in; move: xabi_in.
    case: (xab`_i)=> [xai xbi] /= => /andP [xai_in xbi_in]; apply/andP.
    by split; rewrite ?rpredNr //.
  rewrite big_map -mulrN1 big_distrl /=.
  by apply: eq_bigr=> [[xa xb] _]; rewrite mulrN1 mulNr.
Qed.    

Lemma muli_idealr : idealr muli.
Proof.
  split; first by exact muli_zmod.
  move=> a x /sumboolP [xab [xab_in ->]]; apply/sumboolP.
  exists [seq (a * ab.1, ab.2) | ab <- xab]; split; move: xab_in=> /all_nthP xab_in.
    apply/(all_nthP (0, 0))=> i i_leq_sz; rewrite size_map in i_leq_sz.
    rewrite (nth_map (0, 0)) //.
    move: xab_in=> /(_ (0, 0) i i_leq_sz) xabi_in; move: xabi_in.
    case: (xab`_i)=> [xai xbi] /= => /andP [xai_in xbi_in]; apply/andP.
    by split; rewrite ?idealMr //.
  by rewrite big_map big_distrr /=; apply: eq_bigr=> [[xa xb] _]; rewrite mulrA.
Qed.

Definition keyed_muli := keyed_ideal_default muli_idealr.

Lemma muli_ex x : x \in keyed_muli -> muli_prop x.
Proof.
  case: keyed_muli=> [? hkIJ]; rewrite hkIJ=> x_in.
  apply/(sumboolP (classic _)); exact x_in.
Qed.
*)
End IdealOps.

Declare Scope ideal_scope.
Open Scope ideal_scope.

Notation "kI + kJ" := (keyed_addi kI kJ).
(*
Notation "kI * kJ" := (keyed_muli kI kJ).
 *)
