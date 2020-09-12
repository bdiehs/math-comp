
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
(*
Section idk.

Context {n m : nat} {T : Type}.

Variables (f1 : T ^ n) (f2 : T ^ m) (t:T) (A B : T -> Prop).
Hypothesis AH : forall j, A (f1 j).
Hypothesis BH : forall j, B (f1 j).


Definition smth : 'I_(n + m) -> T :=
  fun i => match (split i) with
        | inl j => f1 j
        | inr j => f2 j
        end.

Lemma idk : forall i, A (smth i) \/ B (smth i). 
Proof.
  move=> i. case (splitP i).
*)  



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










































    








    





    

    

    
