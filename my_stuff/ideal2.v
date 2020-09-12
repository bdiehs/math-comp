
From mathcomp Require Import ssreflect eqtype choice bigop ssreflect ssrbool ssrnat.
From mathcomp Require Import ssrfun fintype finfun seq ssralg generic_quotient.
From mathcomp Require Import tuple ring_quotient boolp.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.



Section IdealDef.

Structure idealr_theory (R : ringType) (S : {pred R}) := MkIdealTheory {
  _ : 0 \in S;
  _ : {in S &, forall x y, x - y \in S};
  _ : forall a, {in S, forall u, a * u \in S}
}.

Structure idealr (R : ringType) := MkIdeal {
  idealr_pred :> {pred R};
  _ : idealr_theory idealr_pred
}.

Structure proper_idealr (R : ringType) := MkProperIdeal {
  proper_pred :> idealr R;
  proper_one_notin : 1 \notin proper_pred
}.

Structure prime_idealr (R : ringType) := MkPrimeIdeal {
  prime_pred :> proper_idealr R;  
  prime_cls : forall u v, u * v \in prime_pred -> (u \in prime_pred) || (v \in prime_pred)
}.

Structure maximal_idealr (R : comRingType) := MkMaximalIdeal {
  maximal_pred : proper_idealr R;
  maximal_max : forall (T : proper_idealr R), {subset maximal_pred <= T} -> maximal_pred = T
}.

End IdealDef.

Section IdealTheory.
Variables (R : ringType) (I : idealr R).

Lemma ideal_ext (J : idealr R) : (forall x, (x \in I) = (x \in J)) -> I = J.
Proof.
  move: I J=> [I' idealI'] [J' idealJ'] IJ_ext.
  have IJ_eq : I' = J' by apply: funext; apply: IJ_ext.
  clear IJ_ext; move: IJ_eq idealI' idealJ'=> -> P1 P2.
  by f_equal; apply: Prop_irrelevance.
Qed.

Lemma ideal0 : 0 \in I.
Proof. by case I=> I' [? _ _] /=.  Qed.

Lemma idealB : {in I &, forall x y, x - y \in I}.
Proof. by case I=> I' [_ ? _] /=.  Qed.

Lemma idealMr : forall a, {in I, forall u, a * u \in I}.
Proof.
  by case I=> I' [_ _ ?] /=.
Qed.

Lemma idealNr : {in I, forall x, - x \in I} .
Proof.
  by move=> x Ix; rewrite -[-x]add0r; apply idealB; first exact: ideal0.
Qed.

Lemma idealN : {mono -%R: u / u \in I}.
  by move=> u; apply/idP/idP=> /idealNr; rewrite ?opprK.
Qed.

Lemma idealD : {in I &, forall x y, x + y \in I}.
Proof.
  by move=> x y Ix Iy; rewrite -[y]opprK; apply idealB; last by apply: idealNr.
Qed.

Lemma ideal_sum T r (P : pred T) F:
  (forall i, P i -> F i \in I) -> \sum_(i <- r | P i) F i \in I.
Proof.
  by move=> IH; elim/big_ind: _; [apply: ideal0 | apply: idealD |].
Qed.

Lemma ideal_linear T r (P : pred T) F G:
  (forall i, P i -> F i \in I) -> \sum_(i <- r | P i) G i * F i \in I.
Proof.
  by move=> IFP; apply: ideal_sum=> i /IFP IFi; apply: idealMr.
Qed.

Lemma idealMn n : {in I, forall x, x *+ n \in I}.
Proof.
  by move=> x Iu; rewrite -(card_ord n) -sumr_const ideal_sum.
Qed.

Lemma idealBC u v : u - v \in I = (v - u \in I).
Proof. by rewrite -idealN opprB. Qed.

Lemma idealMNn n : {in I, forall u, u *- n \in I}.
Proof. by move=> u Su; rewrite /= idealN idealMn. Qed.

Lemma idealDr x y : x \in I -> (y + x \in I) = (y \in I).
Proof.
move=> Sx; apply/idP/idP=> [Sxy | /idealD-> //].
by rewrite -(addrK x y) idealB.
Qed.

Lemma idealDl x y : x \in I -> (x + y \in I) = (y \in I).
Proof. by rewrite addrC; apply: idealDr. Qed.

Lemma idealBr x y : x \in I -> (y - x \in I) = (y \in I).
Proof. by rewrite -(idealN x); apply: idealDr. Qed.

Lemma idealBl x y : x \in I -> (x - y \in I) = (y \in I).
Proof. by rewrite -(idealN y); apply: idealDl. Qed.
  
End IdealTheory.

Section ProperIdealTheory.

Variables (R : ringType) (I : proper_idealr R).

Lemma prop_idealr1 : 1 \in I = false.
Proof.
  by apply: negPf; case I=> I' ? /=.
Qed.
End ProperIdealTheory.


Section PrimeIdealTheory.

Variables (R : comRingType) (I : prime_idealr R).

Lemma prime_idealrM u v : (u * v \in I) = (u \in I) || (v \in I).
Proof.
  apply/idP/idP; last by by case/orP => /idealMr; rewrite // mulrC.
  by case I => I' I_prime_cls /=; apply: I_prime_cls.
Qed.

End PrimeIdealTheory.

Section GenIdeal.
  
Variables (R : ringType) (A : {pred R}).

Let I r := `[<exists n (a x : R ^ n), (forall i, (a i \in A)) /\ r = \sum_(i < n) (x i) * (a i)>].

Lemma genIdeal_min : forall (J : idealr R), {subset A <= J} -> {subset I <= J}.
Proof.
  move=> J sAJ r /asboolP [n [a [x [Aa ->]]]].
  by apply: ideal_sum=> i _; rewrite idealMr // sAJ // Aa.
Qed.

Lemma genIdeal_theory : idealr_theory I.
Proof.
  split.
  - apply/asboolP; exists 0%nat, [ffun _ => 0], [ffun _ => 0]; split=> [i|]; first by case i.
    by rewrite big_ord0.
  - move=> r1 r2 /asboolP [n1 [a1 [x1 [Aa1 ->]]]] /asboolP [n2 [a2 [x2 [Aa2 ->]]]].
    apply/asboolP; exists (n1 + n2)%nat.
    exists [ffun j : 'I_(n1 + n2) => match (split j) with | inl j => a1 j | inr j => a2 j end].
    exists [ffun j : 'I_(n1 + n2) => match (split j) with | inl j => x1 j | inr j => - x2 j end].
    split=> [i|]; first by rewrite ffunE; case (split i).
    rewrite big_split_ord /=; congr (_ + _); rewrite -?sumrN; apply: eq_bigr=> i _; rewrite !ffunE.
      have i_split : lshift n2 i = unsplit (inl i) by [].
      by rewrite !i_split unsplitK.
    have i_split : rshift n1 i = unsplit (inr i) by [].
    by rewrite !i_split unsplitK -mulNr.
  - move=> b u /asboolP [n [a [x [Aa ->]]]]; apply/asboolP.
    exists n, [ffun i => a i], [ffun i => b * x i]; split; first by move=> i; rewrite ffunE.
    rewrite big_distrr /=; apply: eq_bigr=> i _; by rewrite !ffunE mulrA.
Qed.

Definition genIdeal := MkIdeal genIdeal_theory.

Lemma genIdeal_in : forall a, a \in A -> a \in genIdeal.
Proof.
  move=> a Aa; apply/asboolP; exists 1%nat, [ffun _ => a], [ffun _ => 1]; split.
    by move=> i; rewrite ffunE.
  by rewrite big_ord_recl big_ord0 !ffunE mul1r addr0.
Qed.

End GenIdeal.

Section FinGenIdeal.

Variables (R : ringType) (n : nat) (a : R ^ n).

Let I r := `[<exists x : R ^ n, r = \sum_(i < n) x i * a i>].
Let A' r := `[<exists i, r = a i>].

Lemma fingen_gen r : r \in I -> r \in genIdeal A'.
Proof.
  move=> /asboolP [x ->]; apply/asboolP.
  by exists n, a, x; split=> [i|]; first by apply/asboolP; exists i. 
Qed.

Lemma gen_fingen r : r \in genIdeal A' -> r \in I.
Proof.
  move=> /asboolP [n' [a' [x' [Aa' ->]]]]; apply/asboolP.
  have iex i' : exists i, a' i' = a i by move: (Aa' i')=> /asboolP.
  pose f i' := projT1 (cid (iex i')).
  pose a'af i' : a' i' = a (f i') := projT2 (cid (iex i')).
  exists [ffun i => \sum_(i' < n' | i == f i') x' i'].
  rewrite (eq_bigr (fun i => \sum_(i' < n' | i == f i') (x' i' * a i))); last first.
    by move=> i _; rewrite ffunE big_distrl //=.
  rewrite (exchange_big_dep (fun _ => true)) /=; last by  move=> i j _ _.
  by apply: eq_bigr=> i' _; rewrite big_pred1_eq a'af.
Qed.

Lemma eq_gen_fingen : genIdeal A' = I :> {pred R}.
Proof.
  apply funext=> r; apply/idP/idP; [apply gen_fingen| apply fingen_gen].
Qed.

Lemma fingenIdeal_theory : idealr_theory I.
Proof.
  by rewrite -eq_gen_fingen; apply: genIdeal_theory.
Qed.

Definition fingenIdeal := MkIdeal fingenIdeal_theory.

Lemma fingenIdeal_in : forall i, a i \in fingenIdeal.
Proof.
  move=> i; rewrite /= -eq_gen_fingen genIdeal_in //.
  by apply/asboolP; exists i.
Qed.

End FinGenIdeal.

Section PrincipalIdeal.

Variables (R : ringType) (a : R).

Definition principalIdeal := fingenIdeal [ffun i : 'I_1 => a].

Lemma principalP r : reflect (exists x, r = x * a) (r \in principalIdeal).
Proof.
  apply: (iffP idP)=> [/asboolP [x ->]| [x ->]].
    by exists (x ord0); rewrite big_ord_recl big_ord0 !ffunE addr0.
  by apply/asboolP; exists [ffun _ => x]; rewrite big_ord_recl big_ord0 !ffunE addr0.     
Qed.

Lemma principal_in : a \in principalIdeal.
Proof.
  by apply/principalP; exists 1; rewrite mul1r.
Qed.

End PrincipalIdeal.

Notation "(' a )" := (principalIdeal a).

Section FinIdealGenIdeal.

Variables (R : ringType) (n : nat) (𝔞 : (idealr R) ^ n).

Let I r := `[<exists a : R ^ n, (forall i, a i \in 𝔞 i) /\ r = \sum_(i < n) a i>].
Let A' r := `[<exists i, r \in 𝔞 i>].

Lemma finidealgen_gen r : r \in I -> r \in genIdeal A'.
Proof.
  move=> /asboolP [a [𝔞a ->]]; apply/asboolP.
  exists n, a, [ffun _ => 1]; split=> [i|]; first by apply/asboolP; exists i.
  by apply: eq_bigr=> i _; rewrite ffunE mul1r.
Qed.

Lemma gen_finidealgen r : r \in genIdeal A' -> r \in I.
Proof.
  move=> /asboolP [n' [a' [x' [Aa' ->]]]]; apply/asboolP.
  have iex i' : exists i, a' i' \in 𝔞 i by move: (Aa' i')=> /asboolP.
  pose f i' := projT1 (cid (iex i')).
  pose a'𝔞f i' : a' i' \in 𝔞 (f i') := projT2 (cid (iex i')).
  exists [ffun i => \sum_(i' < n' | i == f i') x' i' * a' i']; split.
    by move=> i; rewrite ffunE ideal_linear // => i' /eqP ->.
  rewrite (eq_bigr (fun i => \sum_(i' < n' | i == f i') x' i' * a' i')); last first.
    by move=> i _; rewrite ffunE. 
  rewrite (exchange_big_dep (fun _ => true)) /=; last by move=> i j _ _.
  by apply: eq_bigr=> i' _; rewrite big_pred1_eq.
Qed.

Lemma eq_gen_finidealgen : genIdeal A' = I :> {pred R}.
Proof.
  apply funext=> r; apply/idP/idP; [apply gen_finidealgen| apply finidealgen_gen].
Qed.

Lemma finidealgenIdeal_theory : idealr_theory I.
Proof.
  by rewrite -eq_gen_finidealgen; apply: genIdeal_theory.
Qed.

Definition finidealgenIdeal := MkIdeal finidealgenIdeal_theory.

Lemma finidealgenIdeal_in : forall r, (exists i, r \in 𝔞 i) -> r \in finidealgenIdeal.
Proof.
  move=> r [i 𝔞ir]; rewrite /= -eq_gen_finidealgen genIdeal_in //.
  by apply/asboolP; exists i.
Qed.

End FinIdealGenIdeal.


Section IdealOps.

Variables (R : ringType) (I J : idealr R).

Definition zero (r: R) := r == 0.

Lemma zero_ideal_theory : idealr_theory zero.
Proof.
  split.
  - by apply/eqP.
  - by move=> x y /eqP -> /eqP ->; rewrite subr0; apply/eqP.
  - by move=> a x /eqP ->; rewrite mulr0; apply/eqP.
Qed.

Definition zeroIdeal := MkIdeal zero_ideal_theory.

Lemma zeroiP r : reflect (r = 0) (r \in zeroIdeal).
Proof.
  apply: eqP.
Qed.
Let plus r := `[<exists a b, (a \in I /\ b \in J) /\ r = a + b>].

Lemma addI_ideal_theory : idealr_theory plus.
Proof.
  split.
  - by apply/asboolP; exists 0, 0; rewrite !ideal0 add0r.
  - move=> x y /asboolP [xa [xb [[Ixa Ixb] ->]]] /asboolP [ya [yb [[Jya Jyb] ->]]].
    apply/asboolP; exists (xa - ya), (xb - yb); split; first by split; apply: idealB.
    apply/eqP; rewrite subr_eq; apply/eqP.
    by rewrite -addrA (addrC ya) subrKA (addrC xb) subrKA.
  - move=> a x /asboolP [xa [xb [[xa_in xb_in] ->]]]; apply/asboolP.
    exists (a * xa), (a * xb); split; first by split; apply: idealMr.
    by rewrite mulrDr.
Qed.
    
Definition addIdeal := MkIdeal addI_ideal_theory.

Lemma addi_inl x : x \in I -> x \in addIdeal.
Proof.
  move=> H; apply/asboolP.
  by exists x, 0; rewrite ideal0 addr0.
Qed.

Lemma addi_inr x : x \in J -> x \in addIdeal.
Proof.
  move=> H; apply/asboolP.
  by exists 0, x; rewrite ideal0 add0r.
Qed.

Lemma addiP r : reflect (exists a b, (a \in I /\ b \in J) /\ r = a + b) (r \in addIdeal).
Proof.
  apply: asboolP.
Qed.
  
Definition one (r : R) := true.

Lemma one_ideal_theory : idealr_theory one.
Proof. by []. Qed.

Definition oneIdeal := MkIdeal one_ideal_theory.

Definition mulIdeal := genIdeal (fun r => `[<exists a b, (a \in I /\ b \in J) /\ r = a * b>]).

Lemma muli_in : {in I & J, forall x y, x * y \in mulIdeal}.
Proof.
  by move=> x y Ix Jy; apply: genIdeal_in; apply/asboolP; exists x, y.
Qed.

Lemma muliP r : reflect (exists n (a b : R ^ n), ((forall i, a i \in I) /\ (forall i, b i \in J)) /\ r = \sum_(i < n) a i * b i) (r \in mulIdeal).
Proof.
  apply: (iffP idP).
    move=> /asboolP [n [ab [x [abplus ->]]]].
    pose a i := projT1 (cid (asboolW (abplus i))).
    pose a_ok i : exists b, (a i \in I /\ b \in J) /\ ab i = a i * b :=
      projT2 (cid (asboolW (abplus i))).
    pose b i := projT1 (cid (a_ok i)).
    pose b_ok i : (a i \in I /\ b i \in J) /\ ab i = a i * b i := projT2 (cid (a_ok i)).
    exists n, [ffun i => x i * a i], [ffun i => b i]; split.
      by split; move=> i; rewrite !ffunE ?idealMr; first split; rewrite //; apply b_ok.
    apply: eq_bigr=> i _; rewrite !ffunE -mulrA; congr(_ * _); apply b_ok.
  move=> [n [a [b [[Ia Jb] ->]]]]; apply/asboolP.
  exists n, [ffun i => a i * b i], [ffun _ => 1]; split.
    by move=> i; apply/asboolP; exists (a i), (b i); rewrite ffunE.
  by apply: eq_bigr=> i _; rewrite !ffunE mul1r.
Qed.

End IdealOps.


Declare Scope ideal_scope.
Open Scope ideal_scope.

Notation "I +i J" := (addIdeal I J) (at level 0) : ideal_scope.
Notation "I *i J" := (mulIdeal I J) (at level 0) : ideal_scope.

Opaque zeroIdeal addIdeal mulIdeal.

Section IdealOpsTheory.

Variables (R : comRingType).

Lemma addiA : associative (@addIdeal R).
Proof.
  move=> I1 I2 I3; apply: ideal_ext=> x; apply/idP/idP.
    move=> /asboolP [a [_ [[Ia /asboolP [b [c [[Ib Ic] ->]]]] ->]]].
    apply/asboolP; exists (a + b), c; split; first split; rewrite ?addrA //.
    by apply/asboolP; exists a, b.
  move=> /asboolP [? [c [[/asboolP [a [b [[Ia Ib] ->]] Ic] ->]]]].
  apply/asboolP; exists a, (b + c); split; first split; rewrite ?addrA //.
  by apply/asboolP; exists b, c.
Qed.

Lemma add0i : left_id (@zeroIdeal R) (@addIdeal R).
Proof.
  move=> I; apply: ideal_ext=> x; apply/idP/idP.
    by move=> /asboolP [a [b [[/eqP ->] Ib ->]]]; rewrite add0r.
  by move=> Ix; apply/asboolP; exists 0, x; rewrite ?ideal0 ?add0r //.
Qed.

Lemma addi0 : right_id (@zeroIdeal R) (@addIdeal R).
Proof.
  move=> I; apply: ideal_ext=> x; apply/idP/idP.
    by move=> /asboolP [a [b [[Ix /eqP ->] ->]]]; rewrite addr0.
  by move=> Ix; apply/asboolP; exists x, 0; rewrite ?ideal0 ?addr0 //.
Qed.

Definition addi_law := Monoid.Law addiA add0i addi0.

Lemma addiC : commutative addi_law.
Proof.
  move=> I1 I2; apply: ideal_ext=> x; apply/idP/idP;
    by move/asboolP=> [a [b [[Ia Ib] ->]]]; apply/asboolP; exists b, a; rewrite addrC.
Qed.


Definition addi_com_law := Monoid.ComLaw addiC.
  
Opaque mulIdeal.
Lemma mul0i : left_zero (@zeroIdeal R) (@mulIdeal R).
Proof.
  move=> I; apply: ideal_ext=> x; apply/idP/idP.
    move/muliP=> [n [a [b [[azero _] ->]]]]; apply: ideal_sum=> i _.
    by move: (azero i)=> /zeroiP ->; rewrite mul0r ideal0.
  move=> /eqP ->; apply: ideal0.
Qed.

Lemma muli0 : right_zero (@zeroIdeal R) (@mulIdeal R).
Proof.
  move=> I; apply: ideal_ext=> x; apply/idP/idP.
    move/muliP=> [n [a [b [[_ bzero] ->]]]]; apply: ideal_sum=> i _.
    by move: (bzero i)=> /zeroiP ->; rewrite mulr0 ideal0.
  move=> /eqP ->; apply: ideal0.
Qed.

Definition muli_mul_law := Monoid.MulLaw mul0i muli0.

Lemma muliDl : left_distributive (@mulIdeal R) addi_com_law.
Proof.
  move=> I1 I2 I3; apply: ideal_ext=> r; apply/idP/idP.
    move=> /muliP [n [ab [c [[Iab Ic] ->]]]].
    apply: ideal_sum=> i _; apply/addiP.
    move: (Iab i)=> /addiP [a [b [[Ia Ib] ->]]].
    by exists (a * c i), (b * c i); split; rewrite ?muli_in ?mulrDl //=.
  move=> /addiP [ac [bc [[/muliP [n [a [c [[Ia Ic] ->]]]] /muliP [m [b [d [[Ib Id] ->]]]]] ->]]].  by apply: idealD; apply: ideal_sum=> i _; rewrite ?muli_in //; [rewrite addi_inl | rewrite addi_inr].
Qed. 

Lemma muliDr : right_distributive (@mulIdeal R) addi_com_law.
Proof.
  move=> I1 I2 I3; apply: ideal_ext=> r; apply/idP/idP.
    move=> /muliP [n [a [bc [[Ia Ibc] ->]]]].
    apply: ideal_sum=> i _; apply/addiP.
    move: (Ibc i)=> /addiP [b [c [[Ib Ic] ->]]].
    by exists (a i * b), (a i * c); split; rewrite ?muli_in ?mulrDr //=.
  move=> /addiP [ac [bc [[/muliP [n [a [c [[Ia Ic] ->]]]] /muliP [m [b [d [[Ib Id] ->]]]]] ->]]].  by apply: idealD; apply: ideal_sum=> i _; rewrite ?muli_in //; [rewrite addi_inl | rewrite addi_inr].
Qed. 


Definition addi_add_law := Monoid.AddLaw muliDl muliDr.

End IdealOpsTheory.

Section MaximalIdealTheory.

Variables (R : comRingType) (midealI : maximal_idealr R).

Let I := maximal_pred midealI.

Lemma maximalS : forall (J : proper_idealr R), {subset I <= J} -> I = J.
Proof.
  by rewrite /I; case midealI=> [? Imax] /=; apply: Imax.
Qed.

Lemma maximal_nI1 : forall x, x \notin I -> 1 \in (I +i ('x)).
Proof.
  move=> x; apply: contraR=> nJ1; set (J := MkProperIdeal nJ1).
  by rewrite (@maximalS J (addi_inl _)); apply/addi_inr/principal_in.
Qed.

Lemma maximal_nI1_ex : forall x, x \notin I -> exists a b, a \in I /\ 1 = a + b * x.
Proof.
  move=> x /maximal_nI1 /asboolP [a [_ [[Ia /principalP [b ->] H1_eq]]]].
  by exists a, b; split.
Qed.
    
Lemma maximal_prime : forall u v, u * v \in I -> (u \in I) || (v \in I).
Proof.
  move=> x y; apply: contraLR; rewrite negb_or.
  move=> /andP [/maximal_nI1_ex [a [b [Ia H1_eq]]]]; apply: contra=> Ixy.
  by rewrite -[y] mul1r H1_eq mulrDl -mulrA mulrC; apply: idealD; apply idealMr.
Qed.

Definition maximal_prime_ideal := MkPrimeIdeal maximal_prime.


End MaximalIdealTheory.

Coercion maximal_prime_ideal : maximal_idealr >-> prime_idealr.

Local Open Scope quotient_scope.


Module Quotient.

Section ZmodQuotient.
Variables (R : ringType) (I : idealr R).

Definition equiv (x y : R) := (x - y) \in I.

Lemma equivE x y : (equiv x y) = (x - y \in I). Proof. by []. Qed.

Lemma equiv_is_equiv : equiv_class_of equiv.
Proof.
split=> [x|x y|y x z]; rewrite !equivE ?subrr ?ideal0 //.
   by rewrite -opprB idealN.
by move=> *; rewrite -[x](addrNK y) -addrA idealD.
Qed.

Canonical equiv_equiv := EquivRelPack equiv_is_equiv.
Canonical equiv_encModRel := defaultEncModRel equiv.

Definition type := {eq_quot equiv}.
Definition type_of of phant R := type.

Canonical rquot_quotType := [quotType of type].
Canonical rquot_eqType := [eqType of type].
Canonical rquot_choiceType := [choiceType of type].
Canonical rquot_eqQuotType := [eqQuotType equiv of type].

Lemma idealrBE x y : (x - y) \in I = (x == y %[mod type]).
Proof. by rewrite piE equivE. Qed.

Lemma idealrDE x y : (x + y) \in I = (x == - y %[mod type]).
Proof. by rewrite -idealrBE opprK. Qed.

Definition zero : type := lift_cst type 0.
Definition add := lift_op2 type +%R.
Definition opp := lift_op1 type -%R.

Canonical pi_zero_morph := PiConst zero.

Lemma pi_opp : {morph \pi : x / - x >-> opp x}.
Proof.
move=> x; unlock opp; apply/eqP; rewrite piE equivE.
by rewrite -opprD idealN idealrDE opprK reprK.
Qed.

Canonical pi_opp_morph := PiMorph1 pi_opp.

Lemma pi_add : {morph \pi : x y / x + y >-> add x y}.
Proof.
move=> x y /=; unlock add; apply/eqP; rewrite piE equivE.
rewrite opprD addrAC addrA -addrA.
by rewrite idealD // (idealrBE, idealrDE) ?pi_opp ?reprK.
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

Notation "{quot I }" := (@type_of _ I (Phant _)).

Section RingQuotient.

Variables (R : comRingType) (I : proper_idealr R).

Local Notation type := {quot I}.

Definition one: type := lift_cst type 1.
Definition mul := lift_op2 type *%R.

Canonical pi_one_morph := PiConst one.

Lemma pi_mul: {morph \pi : x y / x * y >-> mul x y}.
Proof.
move=> x y; unlock mul; apply/eqP; rewrite piE equivE.
rewrite -[_ * _](addrNK (x * repr (\pi_type y))) -mulrBr.
rewrite -addrA -mulrBl idealD //.
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

Variables (R : comRingType) (I : proper_idealr R).

Local Notation type := {quot I}.

Definition unit (x : {quot I}) := `[<exists x'', x'' * x = 1>].

Lemma inv_exists (x : {quot I}) : exists x',
    if (x \in unit) then (x' * x = 1) else x' = x.
Proof.
  case: (x \in unit) /idP=> [/asboolP [x' <-]| nxunit]; first by exists x'.
  by exists x.
Qed.  
Definition inv (x : {quot I}) : {quot I} := projT1 (cid (inv_exists x)).
Definition inv_ok x : if (x \in unit) then ((inv x) * x = 1) else inv x = x :=
  projT2 (cid (inv_exists x)).

Lemma mulqVx : {in unit, left_inverse 1 inv *%R}.
Proof.
  by move=> x x_unit; move: (inv_ok x); rewrite x_unit.
Qed.

Lemma unitqPl : forall x y, y * x = 1 -> unit x.
Proof.
  by move=> x y yx1; apply/asboolP; exists y.
Qed.

Lemma invq0id : {in [predC unit], inv =1 id}.
Proof.
  by move=> x /negbTE /= nxunit; move: (inv_ok x); rewrite nxunit.
Qed.

Definition rquot_comUnitRingMixin := ComUnitRingMixin mulqVx unitqPl invq0id.

Canonical rquot_UnitRingType := Eval hnf in UnitRingType type rquot_comUnitRingMixin.
Canonical rquot_comUnitRingType := Eval hnf in
 [comUnitRingType of type].

End comUnitRingQuotient.

Section IDomainQuotient.

Variables (R : comRingType) (I : prime_idealr R).

Local Notation type := {quot I}.
  
Lemma rquot_IdomainAxiom (x y : {quot I}): x * y = 0 -> (x == 0) || (y == 0).
Proof.
  by move=> /eqP; rewrite -[x]reprK -[y]reprK !piE !equivE !subr0 prime_idealrM.
Qed.

Canonical rquot_idomainType := Eval hnf in IdomainType type rquot_IdomainAxiom.

End IDomainQuotient.

Section FieldQuotient.

Variables (R : comRingType) (I : maximal_idealr R).

Local Notation type := {quot I}.

Lemma rquot_FieldAxiom (x : {quot I}): (x != 0) -> x \is a GRing.unit.
Proof.
  rewrite -[x]reprK !piE !equivE subr0=> /maximal_nI1_ex [a [b [Ia [eq1abx]]]].
  by apply/asboolP; exists (\pi b); apply/eqP; rewrite !piE !equivE eq1abx idealBC addrK.
Qed.

Canonical rquot_fieldType := Eval hnf in FieldType type rquot_FieldAxiom.

End FieldQuotient.

End Quotient.

Notation "{ideal_quot I }" := (@Quotient.type_of _ I (Phant _)).
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
Section PairIdealDef.

Variables (R1 R2 : comRingType) (I1 : idealr R1) (I2 : idealr R2).

Let I p := (p.1 \in I1) && (p.2 \in I2).

Theorem pairI_ideal_theory : idealr_theory I.
Proof.
  split; first by apply/andP; split; apply: ideal0.
  - move=> x y /andP [Ix1 Ix2] /andP [Iy1 Iy2].
    by apply/andP; split; apply idealB.
  - by move=> a x /andP [Ix1 Ix2]; apply/andP; split; apply: idealMr.
Qed.

Definition pairIdeal := MkIdeal pairI_ideal_theory.

End PairIdealDef.

Section PairIdealTheory.

Variables (R1 R2 : comRingType) (I : idealr (pair_ringType R1 R2)).

Definition Il0 a := (a, 0) \in I.

Lemma pairl0_ideal_theory : idealr_theory Il0.
Proof.
  split. by apply: ideal0.
  - move=> x y Ix Iy; have Ixy := (idealB Ix Iy).
    by rewrite /GRing.add /GRing.opp /= /add_pair /opp_pair /= subr0 in Ixy.
  - move=> a x Ix. have Iax := (idealMr (a, 0) Ix).
    by rewrite /GRing.mul /= /mul_pair /= mulr0 in Iax.
Qed.

Definition pairl0Ideal := MkIdeal pairl0_ideal_theory.

Definition Ir0 b := (0, b) \in I.

Lemma pairr0_ideal_theory : idealr_theory Ir0.
Proof.
  split. by apply: ideal0.
  - move=> x y Ix Iy; have Ixy := (idealB Ix Iy).
    by rewrite /GRing.add /GRing.opp /= /add_pair /opp_pair /= subr0 in Ixy.
  - move=> a x Ix. have Iax := (idealMr (0, a) Ix).
    by rewrite /GRing.mul /= /mul_pair /= mulr0 in Iax.
Qed.

Definition pairr0Ideal := MkIdeal pairr0_ideal_theory.


Theorem idealr_pair : exists I1 I2, I =i pairIdeal I1 I2.
Proof.
  exists pairl0Ideal, pairr0Ideal=> [[x1 x2]].
    apply/idP/idP=> [Ix | /andP [Ix1 Ix2]].
    have Ix1 := idealMr (1, 0) Ix; have Ix2 := idealMr (0, 1) Ix.
    rewrite /GRing.mul /= /mul_pair /= !mul1r !mul0r in Ix1, Ix2.
    by apply/andP; split.
  have Ix12 := idealD (I := I) Ix1 Ix2.
  by rewrite /GRing.add /= /add_pair /= add0r addr0 in Ix12.
Qed.

End PairIdealTheory.
*)

Section Noetherian.

Definition isNoetherian1 (R : comRingType) := forall (I : idealr R),
    exists n (a : R ^ n), I = fingenIdeal a.

Definition isNoetherian2 (R : comRingType) := forall (I : nat -> idealr R),
    (forall n, {subset I n <= I n.+1}) -> exists n, forall m, m >= n -> I m = I n.

Definition isNoetherian3 (R : comRingType) :=
  forall (S : {pred (idealr R)}) I0 (_ : I0 \in S),
  exists I_max, I_max \in S /\ forall I, I \in S -> {subset I_max <= I} -> I = I_max.

Definition isNoetherian := isNoetherian1.

Lemma noetherian12 (R : comRingType) : isNoetherian1 R -> isNoetherian2 R.
Proof.
  move=> nR I I_incr.
  set I' := genIdeal (fun r => `[<exists n, r \in I n>]).
  move: (nR I')=> [n [a I'a]].
  have Is_mono p q (leq_pq : p <= q) : {subset I p <= I q}.
    apply: (homo_leq _ _ I_incr leq_pq); first by move=> x; apply: sub_refl.
    by move=> I2 I1 I3 I21 I32 x I1x; apply: I32; apply: I21.
  have Ia : forall i, exists m, a i \in I m.
    move=> i; move: (fingenIdeal_in a i); rewrite -I'a=> /asboolP [m [b [x [Ib ->]]]].
    pose Ibf i := projT1 (cid (asboolW (Ib i))).
    pose Ibf_ok i : b i \in I (Ibf i) := projT2 (cid (asboolW (Ib i))).
    exists (\max_(j < m) Ibf j); apply: ideal_sum=> j _.
    by apply: (Is_mono (Ibf j) _ (leq_bigmax _)); apply: idealMr.
  pose Iaf i := projT1 (cid (Ia i)).
  pose Iaf_ok i : a i \in I (Iaf i) := projT2 (cid (Ia i)).
  exists (\max_(i < n) Iaf i)=> m mmax; apply: ideal_ext=> r; apply/idP/idP=> [Imr | Ir].
    have Ir : r \in I' by apply/genIdeal_in/asboolP; exists m.
    move: Ir; rewrite I'a=> /asboolP [x ->]; apply: ideal_sum=> i _.
    by apply/idealMr/(Is_mono (Iaf i) _ (leq_bigmax _)).
  by apply: (Is_mono _ _ mmax).
Qed.

(*

Lemma noetherian23 (R : comRingType) : isNoetherian2 R -> isNoetherian3 R.
Proof.
  move=> nR S I0 SI0; apply/existsPN=> Hcontra.
  have next : forall (Isig : {I: idealr R | I \in S}), exists I'sig : {I | I \in S},
      let I := sval Isig in let I' := sval I'sig in
      {subset I <= I'} /\ I' <> I.
    move=> [I SI]; move: (Hcontra I)=> /and_asboolP.
    rewrite negb_and=> /orP[/asboolP nSI |] // /existsp_asboolPn.
    move=> [I' /not_implyP].
    => /and_asboolP.
    rewrite negb_and.
  move=> [I SI]; move: (Hcontra I)=> /and_asboolP.
    rewrite negb_and=> /orP[/asboolP nSI |] // /existsp_asboolPn.
    move=>[I' /Nimply [SI' /contrapT I'ltI]]; exists (Sub I' SI').
  set Is_sig := fix f (n : nat) : {I| I \in S} := match n with
            | 0 => (Sub I0 SI0)
            | n.+1 => sval (cid (next (f n)))
            end.
  set Is := fun n => sval (Is_sig n).
  apply: (contrap (fun (_ : True) => (nR Is))); rewrite // Nimply /Is /=; split=> [n x | ].
    by apply (svalP (cid (next _))).
  apply/forallNP=> n; apply/existsNP; exists n.+1=> /(_ (leqnSn _)) /=.
  by apply (svalP (cid (next _))).
Qed.

Lemma noetherian31 (R : comRingType) : isNoetherian3 R -> isNoetherian1 R.
Proof.
  move=> nR I.
  set S : {pred idealr R} := fun J => `[<(exists n (a: n.-tuple R), J = fingenIdeal a) /\ {subset J <= I}>].
  have S0 : zeroIdeal R \in S. (*TODO: this should be fast using a lemma*)
    apply/asboolP; split; last by move=> _ /eqP ->; apply: ideal0.
    exists 0%nat, [tuple]; apply ideal_ext=> x; apply/idP/idP.
      move=> /eqP ->; apply: ideal0.
    move=> /asboolP [xs ->]; rewrite big_ord0; apply: ideal0.
  move: nR=> /(_ S _ S0) [_ [/asboolP [[n [a ->]] Ia] amax]].
  case: `[<I = fingenIdeal a>] /asboolP=> [-> |]; first by exists n, a.
  move=> /(contrap (@ideal_ext _ _ _)) /existsNP=> [[x]].
  case Ix: (x \in I); case ax: (x \in fingenIdeal a)=> // _.
    set Ia' := fingenIdeal [tuple of x :: a].
    have SIa' : Ia' \in S. (*Second goal TODO*)
      apply/asboolP; split; first by exists (n.+1), [tuple of x :: a].
      move=> r /asboolP [rs ->]; rewrite big_ord_recl tnth0; apply: idealD. 
        by apply: idealMr.
      case: (tupleP rs)=> r0 rs'; apply: Ia; apply/asboolP.
      by exists rs'; apply: eq_bigr=> i _; rewrite !tnthS.
    apply: contrapR (amax Ia' SIa')=> _; split=> [r /asboolP [rs ->] | Ia_eq].
      apply/asboolP; exists [tuple of 0::rs].
      by rewrite big_ord_recl tnth0 mul0r add0r; apply: eq_bigr=> i _; rewrite !tnthS. 
    have Ia'x := (fingen_in [tuple of x::a] ord0).
    by rewrite tnth0 -/Ia' Ia_eq ax in Ia'x.
  by have Ix' := (Ia x ax); rewrite Ix in Ix'.
Qed. 



*)




































    








    





    

    

    
