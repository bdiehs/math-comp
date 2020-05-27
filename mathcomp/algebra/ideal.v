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

Axiom classic : forall P, decidable P.  

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

End FinGenIdeal.

Section PrincipalIdeal.

Variables (R : ringType) (a : R).
Definition principalI : {pred R} := fingenI [tuple a].
Definition principal_idealI : idealr principalI := fingen_idealr [tuple a].

End PrincipalIdeal.

Section IdealGenIdeal.

Variables (R : ringType) (Λ : Type) (𝔞s : Λ -> {pred R})
          (ideals𝔞s : forall λ, idealr (𝔞s λ)).

Definition idealgen_pred r := exists n (λs : n.-tuple Λ) as' xs,
    (forall i, (tnth as' i) \in 𝔞s (tnth λs i)) /\ (r == \sum_i (tnth xs i) * (tnth as' i)).
Definition idealgenI : {pred R} := fun r => classic (idealgen_pred r).

Inductive Λ' : Type :=
  Lambda' λ r : r \in (𝔞s λ) -> Λ'.
Let as' λ' := match λ' with | Lambda' λ r r_in_I_λ => r end.

Lemma gen_gen_ideal r : gen_pred as' r -> idealgen_pred r.
Proof.
  move=> [rn [rλs [rxs ->]]].
  exists rn, [tuple let (λ, _, _) := (tnth rλs i) in λ | i < rn],
    [tuple let (_, x, _) := (tnth rλs i) in x | i < rn], rxs; split.
  move=> i; rewrite !tnth_map tnth_ord_tuple; by case (tnth rλs i).
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

Section IdealFinGenIdeal.

Variables (R : ringType) (n : nat) (𝔞s : n.-tuple {pred R})
          (ideals𝔞 : forall i, idealr (tnth 𝔞s i)).

Definition idealfingen_pred r := exists a : n.-tuple R,
    (forall i, tnth a i \in tnth 𝔞s i) /\ r = \sum_i tnth a i.
Definition idealfingenI : {pred R} := fun r => classic (idealfingen_pred r).

Let 𝔞s' : 'I_n -> {pred R} := [ffun i => tnth 𝔞s i].

Lemma idealgen_idealfingen r : idealgen_pred 𝔞s' r -> idealfingen_pred r.
Proof.
  move=> [rn [rλs [ras [rxs [ras_in_𝔞s /eqP ->]]]]].
  exists [tuple (\sum_(j | tnth rλs j == i) tnth rxs j * tnth ras j) | i < n]; split.
    move=> i; rewrite !tnth_map tnth_ord_tuple.
    case (ideals𝔞 i)=> [[[_ [? ?]] _] mul_cls].
    elim/big_ind : _; rewrite //.
    move=> /= j /eqP λj_eq_i; move: (ras_in_𝔞s j) mul_cls.
    by rewrite -!λj_eq_i /𝔞s' ffunE=> aj_in_𝔞j mul_cls; apply: mul_cls.
  rewrite (partition_big (fun i => tnth rλs i) predT) /=; last by [].
  by apply eq_bigr=> i _; rewrite !tnth_map tnth_ord_tuple.
Qed.

Lemma idealfingen_idealgen r :  idealfingen_pred r -> idealgen_pred 𝔞s' r.
Proof.
  move=> [a [as_in_𝔞s ->]]; exists n, (ord_tuple n), a, [tuple 1 | i < n]; split.
    by move=> i; rewrite /𝔞s' ffunE tnth_ord_tuple.
  apply/eqP; apply: eq_bigr=> i _; by rewrite tnth_map mul1r.
Qed.

Lemma idealfingen_idealr : idealr idealfingenI.
Proof.
  apply: (eq_ideal (I := idealgenI 𝔞s')).
    move=> r; apply/sumboolP/sumboolP; first by apply: idealgen_idealfingen.
    by apply: idealfingen_idealgen.
  by apply: gen_ideal_idealr.    
Qed.





(*

Section GenIdeal.

Variables (R : ringType) (Λ : Type) (a_λ : Λ -> R).
Definition gen_pred r := (exists lxs : seq (Λ * R), r = \sum_(i <- lxs) (i.2 * a_λ i.1)).
Definition genI : {pred R} := fun r => classic (gen_pred r).

Lemma gen_addr : addrPred genI.
Proof.
  split; first by [].
  split; first by apply/sumboolP; exists nil; rewrite big_nil.
  move=> x y /sumboolP [x_gen ->] /sumboolP [y_gen ->]; apply/sumboolP.
  by exists (x_gen ++ y_gen); rewrite big_cat.
Qed.

Lemma gen_zmod : zmodPred genI.
Proof.
  split; first by exact: gen_addr.
  move=> x /sumboolP [x_gen ->]; apply/sumboolP; exists [seq (p.1, -p.2) | p <- x_gen].
  rewrite (big_morph -%R (id1 := 0) (op1 := +%R)); last by exact: oppr0.
    by rewrite big_map; apply: eq_bigr => i _; rewrite mulNr.
  by move=> a b; rewrite -{1}[b]opprK opprB addrC.
Qed.

Lemma gen_idealr : idealr genI.
  split; first by exact: gen_zmod.
  move=> r x /sumboolP [x_gen ->]; apply /sumboolP; exists [seq (p.1, r * p.2) | p <- x_gen].
  by rewrite big_distrr big_map; apply: eq_bigr => i _ /=; rewrite mulrA.
Qed.

Variable (kI : keyed_pred gen_idealr).

Lemma gen_contains : forall λ, a_λ λ \in kI.
Proof.
  case kI=> [? hkI] λ; rewrite !hkI; apply/sumboolP.
  by exists [:: (λ, 1)]; rewrite big_cons big_nil addr0 mul1r.
Qed.
  
Lemma gen_ideal_min : forall J (idealJ : idealr J) (kJ : keyed_pred idealJ), (forall λ, a_λ λ \in kJ) -> {subset kI <= kJ}.
Proof.
  case kI=> [? hkI] J idealJ kJ a_λ_in_J x.
  rewrite !hkI=> /sumboolP [x_gen ->].
  apply: (big_rec (fun y => y \in kJ)); first by apply: idealr0.
  move=> lxs y _ y_in_J; apply: rpredD; last by [].
  by apply: idealMr.
Qed.

End GenIdeal.

Section FinGenIdeal.

Variables (R : ringType) (n : nat) (a : n.-tuple R).
Definition fingen_pred r := exists x : n.-tuple R, r = \sum_(i < n) tnth x i * tnth a i.
Definition fingenI : {pred R} := fun r => classic (fingen_pred r).

Let a' : 'I_n -> R := [ffun i => tnth a i].

Lemma gen_fingen r : gen_pred a' r -> fingen_pred r.
Proof.
  move=> [r_gen ->]; exists [tuple (\sum_(j <- r_gen | j.1 == i) j.2)| i < n].
  rewrite big_tnth
          (partition_big (fun i => (tnth (in_tuple r_gen) i).1) predT); last by [].
  apply: eq_bigr=> i _; rewrite tnth_map [in RHS]big_tnth big_distrl tnth_ord_tuple.
  by apply: eq_bigr=> j /andP [_ /eqP ->]; rewrite /a' ffunE.
Qed.

Lemma fingen_gen r : fingen_pred r -> gen_pred a' r.
Proof.
  move=> [x ->]; exists [seq (i, tnth x i) | i <- ord_tuple n].
  rewrite big_map big_tuple /=; apply: eq_bigr=> i _.
  by rewrite /a' ffunE tnth_ord_tuple.
Qed.

Lemma fingen_idealr : idealr fingenI.
  apply: (eq_ideal (I := genI a')).
    move=> r; apply/sumboolP/sumboolP; first by apply: gen_fingen.
    by apply: fingen_gen.
  by apply: gen_idealr.    
Qed.

End FinGenIdeal.

Section PrincipalIdeal.

Variables (R : ringType) (a : R).
Definition principalI : {pred R} := fingenI [tuple a].
Definition principal_idealI : idealr principalI := fingen_idealr [tuple a].

End PrincipalIdeal.

Section IdealGenIdeal.

Variables (R : ringType) (Λ : Type) (I_λ : Λ -> {pred R})
          (idealsI_λ : forall λ, idealr (I_λ λ)).

Definition idealgen_pred r := exists laxs : seq (Λ * R * R),
    all (fun i => i.1.2 \in I_λ i.1.1) laxs  && (r == \sum_(i <- laxs) (i.2 * i.1.2)).

Let I : {pred R} := fun r => classic (idealgen_pred r).

Inductive Λ' : Type :=
  Lambda λ r: r \in (I_λ λ) -> Λ'.

Let a_λ' λ' := match λ' with | Lambda λ r r_in_I_λ => r end.

Lemma gen_gen_ideal r : gen_pred a_λ' r -> idealgen_pred r.
Proof.
  move=> [lxs ->]; exists [seq (let (λ, x, H) := lx.1 : Λ' in (λ, x, lx.2)) | lx <- lxs].
  apply/andP; split.
    elim: lxs; first by rewrite all_nil.
    move=> [[λ r' r'_in_I_λ] x] lxs all_lxs /=; apply/andP; split; by [].
  by rewrite big_map; apply/eqP; apply: eq_bigr; move=> [[λ r' r'_in_I_λ] x] _ /=.
Qed.

Lemma gen_ideal_gen r : idealgen_pred r -> gen_pred a_λ' r.
Proof.
  move=> [laxs /andP [laxs_in /eqP ->]].
  elim: laxs laxs_in; first by move=> _; exists nil; rewrite !big_nil.
  move=> lax laxs IHlaxs /andP [lax_in all_laxs]; move: IHlaxs=> /(_ all_laxs) [lxs H].
  by exists [:: (Lambda lax_in, lax.2) & lxs]; rewrite !big_cons; congr(_ + _).
Qed.       

Lemma gen_ideal_idealr : idealr I.
Proof.
  apply: (eq_ideal (I := genI a_λ')).
    move=> r; apply/sumboolP/sumboolP; first by apply: gen_gen_ideal.
    by apply: gen_ideal_gen.
  by apply: gen_idealr.    
Qed.
  
End IdealGenIdeal.

Section IdealFinGenIdeal.

Variables (R : ringType) (n : nat) (𝔞s : n.-tuple {pred R})
          (ideals𝔞 : all (fun 𝔞 => classic (idealr 𝔞)) 𝔞s).

Definition idealfingen_pred r := exists x a : n.-tuple R,
    (forall i, tnth a i \in tnth 𝔞s i) /\ r = \sum_(i < n) tnth x i * tnth a i.
Definition idealfingenI : {pred R} := fun r => classic (idealfingen_pred r).

Let 𝔞s' : 'I_n -> {pred R} := [ffun i => tnth 𝔞s i].

Lemma idealgen_idealfingen r : idealgen_pred 𝔞s' r -> idealfingen_pred r.
Proof.
move=> [r_gen /andP [/all_nthP r_gen_in /eqP ->]].
  exists [tuple (\sum_(j <- r_gen | j.1.1 == i) j.1.2) | i < n],
    [tuple (\sum_(j <- r_gen | j.1.1 == i) j.2) | i < n].
  split.
  move=> i. rewrite tnth_map.
  rewrite (big_morph (fun x => x \in tnth 𝔞s i) (id1 := true) (op1 := andb)).
  rewrite big_all_cond. apply/all_nthP=> j j_leq_r_size. apply/implyP=> j_eq_i.
  
  
  move: r_gen_in=> (_ (0, 0, 0)).

  rewrite /tnth. apply: r_gen_in.
  

Definition fingen_pred r := exists x : n.-tuple R, r = \sum_(i < n) tnth x i * tnth a i.
Definition fingenI : {pred R} := fun r => classic (fingen_pred r).

Let a' : 'I_n -> R := [ffun i => tnth a i].

Lemma gen_fingen r : gen_pred a' r -> fingen_pred r.
Proof.
  move=> [r_gen ->]; exists [tuple (\sum_(j <- r_gen | j.1 == i) j.2)| i < n].
  rewrite big_tnth
          (partition_big (fun i => (tnth (in_tuple r_gen) i).1) predT); last by [].
  apply: eq_bigr=> i _; rewrite tnth_map [in RHS]big_tnth big_distrl tnth_ord_tuple.
  by apply: eq_bigr=> j /andP [_ /eqP ->]; rewrite /a' ffunE.
Qed.

Lemma fingen_gen r : fingen_pred r -> gen_pred a' r.
Proof.
  move=> [x ->]; exists [seq (i, tnth x i) | i <- ord_tuple n].
  rewrite big_map big_tuple /=; apply: eq_bigr=> i _.
  by rewrite /a' ffunE tnth_ord_tuple.
Qed.

Lemma fingen_idealr : idealr fingenI.
  apply: (eq_ideal (I := genI a')).
    move=> r; apply/sumboolP/sumboolP; first by apply: gen_fingen.
    by apply: fingen_gen.
  by apply: gen_idealr.    
Qed.

End FinGenIdeal.

*)
