
From mathcomp Require Import ssreflect eqtype choice bigop ssreflect ssrbool ssrnat.
From mathcomp Require Import ssrfun fintype finfun seq ssralg generic_quotient.
From mathcomp Require Import tuple ring_quotient boolp ssrpred.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section IdealDef.
    
Definition ideal_mul_closed (R : ringType) (S : {pred R}) :=  forall a, {in S, forall u, a * u \in S}.
Definition proper_n1 (R : ringType) (S : {pred R}) := 1 \notin S.
Definition prime_closed (R : ringType) (S : {pred R}) := forall u v, u * v \in S -> (u \in S) || (v \in S).
Definition ideal_theory (R : ringType) (S : {pred R}) := 
  0 \in S /\ forall a, {in S &, forall u v, a * u + v \in S}.

Structure ideal (R : ringType) := {
  ideal_pred :> zmodPredT R;
  _ : ideal_mul_closed ideal_pred
}.

Structure proper_ideal (R : ringType) := {
  proper_pred :> ideal R;
  _ : proper_n1 proper_pred
}.

Structure prime_ideal (R : ringType) := {
  prime_pred :> proper_ideal R;  
  _ : prime_closed prime_pred
}.

Definition is_maximal (R : comRingType) (S : proper_ideal R) :=
  forall (T : proper_ideal R), {subset S <= T} -> S = T.

Structure maximal_ideal (R : comRingType) := {
  maximal_pred : proper_ideal R;
  maximal_max : is_maximal maximal_pred
}.

Section BuildIdeal.

Variables (R : ringType) (S : {pred R}) (Scls : ideal_theory S).

Lemma ideal_closedA : addr_closed S.
Proof.
  split; first by apply Scls.
  by move=> u v Su Sv; rewrite -[u]mul1r; apply Scls.
Qed.

Definition ideal_addrPred := Build_addrPredT ideal_closedA.
Canonical ideal_addrPred.

Lemma ideal_closedN : oppr_closed S.
Proof.
  move=> u Su. rewrite -[-u]addr0 -[u]mul1r -mulNr.
  by apply Scls; [| apply: rpredT0].
Qed.

Definition ideal_zmodPred := Build_zmodPredT ideal_closedN.
Canonical ideal_zmodPred.

Lemma ideal_closedMr : ideal_mul_closed S.
Proof.
  move=> u v Sv. rewrite -[u * v]addr0.
  by apply Scls; [| apply: rpredT0].
Qed.

Definition MkIdeal := Build_ideal ideal_closedMr.
Canonical MkIdeal.

End BuildIdeal.

End IdealDef.  

Section IdealTheory.
Variables (R : ringType) (I : ideal R).

Lemma ideal_ext (S1 S2 : ideal R) : (forall x, (x \in S1) = (x \in S2)) -> S1 = S2.
Proof.
  by case S1; case S2=> ? ? ? ? /zmodPredT_ext; apply: struct_ext.
Qed.

Lemma ideal0 : 0 \in I.
Proof. exact: rpredT0. Qed.

Lemma idealB : {in I &, forall x y, x - y \in I}.
Proof. exact: rpredTB. Qed.

Lemma idealMr : forall a, {in I, forall u, a * u \in I}.
Proof. by case I=> I' ? /=. Qed.

Lemma idealNr : {in I, forall x, - x \in I} .
Proof. exact: rpredTNr. Qed.

Lemma idealN : {mono -%R: u / u \in I}.
Proof. exact: rpredTN. Qed.

Lemma idealD : {in I &, forall x y, x + y \in I}.
Proof. exact: rpredTD. Qed.

Lemma ideal_linear : forall a, {in I &, forall u v, a * u + v \in I}.
Proof. by move=> a u v Iu Iv; rewrite idealD ?idealMr. Qed.

Lemma idealT : ideal_theory I.
Proof. by split; [exact: ideal0 | exact: ideal_linear]. Qed.

Lemma ideal_sum T r (P : pred T) F:
  (forall i, P i -> F i \in I) -> \sum_(i <- r | P i) F i \in I.
Proof. exact: rpredT_sum. Qed.

Lemma ideal_linear_sum T r (P : pred T) F G:
  (forall i, P i -> F i \in I) -> \sum_(i <- r | P i) G i * F i \in I.
Proof.
  by move=> IFP; apply: ideal_sum=> i /IFP IFi; apply: idealMr.
Qed.

Lemma idealMn n : {in I, forall x, x *+ n \in I}.
Proof. exact: rpredTMn. Qed.

Lemma idealBC u v : u - v \in I = (v - u \in I).
Proof. exact: rpredTBC. Qed.

Lemma idealMNn n : {in I, forall u, u *- n \in I}.
Proof. exact: rpredTMNn. Qed.

Lemma idealDr x y : x \in I -> (y + x \in I) = (y \in I).
Proof. exact: rpredTDr. Qed.

Lemma idealDl x y : x \in I -> (x + y \in I) = (y \in I).
Proof. exact: rpredTDl. Qed.

Lemma idealBr x y : x \in I -> (y - x \in I) = (y \in I).
Proof. exact: rpredTBr. Qed.

Lemma idealBl x y : x \in I -> (x - y \in I) = (y \in I).
Proof. exact: rpredTBl. Qed. 

End IdealTheory.


Section ProperIdealTheory.

Variables (R : ringType) (I : proper_ideal R).

Lemma prop_ideal1 : 1 \in I = false.
Proof.
  by apply: negPf; case I=> I' ? /=.
Qed.
End ProperIdealTheory.


Section PrimeIdealTheory.

Variables (R : comRingType) (I : prime_ideal R).

Lemma prime_idealM u v : (u * v \in I) = (u \in I) || (v \in I).
Proof.
  apply/idP/idP; last by by case/orP => /idealMr; rewrite // mulrC.
  by case I => I' I'_cls /=; apply: I'_cls.
Qed.

End PrimeIdealTheory.


Section GenIdeal.
  
Variables (R : ringType) (A : {pred R}).

Let I r := `[<exists n (a x : R ^ n), (forall i, (a i \in A)) /\ r = \sum_(i < n) (x i) * (a i)>].

Lemma genIdeal_min : forall (J : ideal R), {subset A <= J} -> {subset I <= J}.
Proof.
  move=> J sAJ r /asboolP [n [a [x [Aa ->]]]].
  by apply: ideal_sum=> i _; rewrite idealMr // sAJ // Aa.
Qed.

Local Open Scope fun_scope.

Lemma genIdeal_theory : ideal_theory I.
Proof.
  split.
  - apply/asboolP; exists 0%nat, [ffun _ => 0], [ffun _ => 0]; split=> [i|]; first by case i.
    by rewrite big_ord0.
  - move=> b r1 r2 /asboolP [n1 [a1 [x1 [Aa1 ->]]]] /asboolP [n2 [a2 [x2 [Aa2 ->]]]].
    apply/asboolP; exists (n1 + n2)%nat, (a1 +++ a2), ([ffun i => b * (x1 i)] +++ x2).
    split=> [i|]; first by case: (finindex_catP a1 a2 i); move=> [j ->].
    rewrite big_split_ord /=; congr (_ + _); rewrite ?big_distrr /=; apply: eq_bigr=> i _.
      by rewrite !finindex_leftP ffunE mulrA.
    by rewrite !finindex_rightP.
Qed.

Definition genIdeal := MkIdeal genIdeal_theory.

End GenIdeal.

Declare Scope ideal_scope.
Notation "<< A >>" := (genIdeal A) : ideal_scope.

Section GenIdealTheory.

Variables (R : ringType).
Local Open Scope ideal_scope.

Lemma genIdeal_in (A : {pred R}) : forall a, a \in A -> a \in << A >>.
Proof.
  move=> a Aa; apply/asboolP; exists 1%nat, [ffun _ => a], [ffun _ => 1]; split.
    by move=> i; rewrite ffunE.
  by rewrite big_ord_recl big_ord0 !ffunE mul1r addr0.
Qed.

Lemma genIdeal_subset (A B : {pred R}) : {subset A <= B} -> {subset << A >> <= << B >>}. 
Proof.
  move=> sAB r /asboolP [n [a [x [Aa ->]]]].
  by apply: ideal_sum=> i _; apply/idealMr/genIdeal_in/sAB/Aa.
Qed.

End GenIdealTheory.

  
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

Lemma fingenIdeal_theory : ideal_theory I.
Proof.
  by rewrite -eq_gen_fingen; apply: genIdeal_theory.
Qed.

Definition fingenIdeal := MkIdeal fingenIdeal_theory.

End FinGenIdeal.

Notation "<<'( A )>>" := (fingenIdeal A) : ideal_scope.


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

Notation "'( a )" := (principalIdeal a) : ideal_scope.


Section FinGenIdealTheory.

Variables (R : ringType).
Local Open Scope ideal_scope.
Lemma fingenIdeal_in n (a : R ^ n) : forall i, a i \in <<'(a)>>.
Proof.
  move=> i; rewrite /= -eq_gen_fingen genIdeal_in //.
  by apply/asboolP; exists i.
Qed.

(*TODO: this could make use of genIdeal_subset*)
Lemma fingenIdeal_subset_tl n (a : R ^ n) t : {subset <<'(a)>> <= <<'(a:::t)>>}.
Proof.
  move=> r /asboolP [x ->]; apply: ideal_sum=> i _; apply: idealMr.
  by rewrite -(finindex_tlP _ t) fingenIdeal_in.
Qed.

Lemma fingenIdeal_subset_hd n (a : R ^ n) t : {subset '(t) <= <<'(a:::t)>>}.
Proof.
  move=> r /asboolP [x ->]; apply: ideal_sum=> i _; apply: idealMr.
  by rewrite ffunE -{1}(finindex_hdP a t) fingenIdeal_in.
Qed.

Lemma fingenIdeal_subset_left n m (a : R ^ n) (b : R ^ m) :
  {subset <<'(a)>> <= <<'(a +++ b)>>}.
Proof.
  move=> r /asboolP [x ->]; apply: ideal_sum=> i _; apply: idealMr.
  by rewrite -(finindex_leftP a b) fingenIdeal_in.
Qed.

Lemma fingenIdeal_subset_right n m (a : R ^ n) (b : R ^ m) :
  {subset <<'(b)>> <= <<'(a +++ b)>>}.
Proof.
  move=> r /asboolP [x ->]; apply: ideal_sum=> i _; apply: idealMr.
  by rewrite -(finindex_rightP a b) fingenIdeal_in.
Qed.

End FinGenIdealTheory.

Section FinIdealGenIdeal.

Variables (R : ringType) (n : nat) (𝔞 : (ideal R) ^ n).

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
    by move=> i; rewrite ffunE ideal_linear_sum // => i' /eqP ->.
  rewrite (eq_bigr (fun i => \sum_(i' < n' | i == f i') x' i' * a' i')); last first.
    by move=> i _; rewrite ffunE. 
  rewrite (exchange_big_dep (fun _ => true)) /=; last by move=> i j _ _.
  by apply: eq_bigr=> i' _; rewrite big_pred1_eq.
Qed.

Lemma eq_gen_finidealgen : genIdeal A' = I :> {pred R}.
Proof.
  apply funext=> r; apply/idP/idP; [apply gen_finidealgen| apply finidealgen_gen].
Qed.

Lemma finidealgenIdeal_theory : ideal_theory I.
Proof.
  by rewrite -eq_gen_finidealgen; apply: genIdeal_theory.
Qed.

Definition finidealgenIdeal := MkIdeal finidealgenIdeal_theory.


End FinIdealGenIdeal.

Notation "<<( 𝔞 )>>" := (finidealgenIdeal 𝔞) : ideal_scope.

Section FinIdealGenIdealTheory.

Variables (R : ringType).
Local Open Scope ideal_scope.

Lemma finidealgenIdeal_in n (𝔞 : (ideal R) ^ n) : forall r, (exists i, r \in 𝔞 i) -> r \in <<( 𝔞 )>>.
Proof.
  move=> r [i 𝔞ir]; rewrite /= -eq_gen_finidealgen genIdeal_in //.
  by apply/asboolP; exists i.
Qed.

(*TODO: this could also make use of genIdeal_subset*)
Lemma finIdealgenIdeal_subset_tl n (𝔞 : (ideal R) ^ n) I :
  {subset <<( 𝔞 )>> <= <<( 𝔞:::I )>>}.
Proof.
  move=> r /asboolP [a [𝔞a ->]]; apply: ideal_sum=> i _.
  by apply: finidealgenIdeal_in; exists (lift ord0 i); rewrite finindex_tlP.
Qed.

Lemma finIdealgenIdeal_subset_hd n (𝔞 : (ideal R) ^ n) (I : ideal R) :
  {subset I <= <<( 𝔞:::I )>>}.
Proof.
  move=> r Ir; apply: finidealgenIdeal_in.
  by exists ord0; rewrite finindex_hdP.
Qed.

Lemma finIdealgenIdeal_subset_left n m (𝔞 : (ideal R) ^ n) (𝔟 : (ideal R) ^ m)  :
  {subset <<(𝔞)>> <= <<(𝔞 +++ 𝔟)>>}.
Proof.
  move=> r /asboolP [a [𝔞a ->]]; apply: ideal_sum=> i _.
  by apply: finidealgenIdeal_in; exists (lshift m i); rewrite finindex_leftP.
Qed.

Lemma finIdealgenIdeal_subset_right n m (𝔞 : (ideal R) ^ n) (𝔟 : (ideal R) ^ m)  :
  {subset <<(𝔟)>> <= <<(𝔞 +++ 𝔟)>>}.
Proof.
  move=> r /asboolP [b [𝔟b ->]]; apply: ideal_sum=> i _.
  by apply: finidealgenIdeal_in; exists (rshift n i); rewrite finindex_rightP.
Qed.

End FinIdealGenIdealTheory.


Section IdealOps.
Local Open Scope ideal_scope.

Variables (R : ringType) (I J : ideal R).

Definition zero (r: R) := r == 0.

Lemma zero_ideal_theory : ideal_theory zero.
Proof.
  split; first by apply/eqP.
  by move=> a x y /eqP -> /eqP ->; rewrite mulr0 addr0; apply/eqP.
Qed.

Definition zeroIdeal := MkIdeal zero_ideal_theory.

Lemma zeroiP r : reflect (r = 0) (r \in zeroIdeal).
Proof.
  apply: eqP.
Qed.
Definition plus r := `[<exists a b, (a \in I /\ b \in J) /\ r = a + b>].
  
Lemma addI_ideal_theory : ideal_theory plus.
Proof.
  split; first by apply/asboolP; exists 0, 0; rewrite !ideal0 add0r.
  - move=> r x y /asboolP [xa [xb [[Ixa Ixb] ->]]] /asboolP [ya [yb [[Jya Jyb] ->]]].
    apply/asboolP; exists (r * xa + ya), (r * xb + yb); split; last by rewrite addrACA mulrDr.
    by rewrite !ideal_linear.
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

Lemma one_ideal_theory : ideal_theory one.
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

Definition cap : {pred R} := [ pred r | (r \in I) && (r \in J)].

Lemma cap_ideal_theory : ideal_theory cap.
Proof.
  split; first by rewrite /cap inE !ideal0.
  move=> a u v /andP [Iu Ju] /andP [Iv Jv].
  by rewrite /cap inE !ideal_linear.
Qed.
Definition capIdeal := MkIdeal cap_ideal_theory.


End IdealOps.

Declare Scope ideal_scope.
Open Scope ideal_scope.

Notation "I +i J" := (addIdeal I J) (at level 0) : ideal_scope.
Notation "I *i J" := (mulIdeal I J) (at level 0) : ideal_scope.
Notation "I \capi J" := (capIdeal I J) (at level 0) : ideal_scope.

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

Variables (R : comRingType) (midealI : maximal_ideal R).

Let I := maximal_pred midealI.

Lemma maximalS : forall (J : proper_ideal R), {subset I <= J} -> I = J.
Proof.
  by rewrite /I; case midealI=> [? Imax] /=; apply: Imax.
Qed.

Lemma maximal_nI1 : forall x, x \notin I -> 1 \in (I +i '(x)).
Proof.
  move=> x; apply: contraR=> nJ1; set (J := Build_proper_ideal nJ1).
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

Definition maximal_prime_ideal := Build_prime_ideal maximal_prime.

End MaximalIdealTheory.


Coercion maximal_prime_ideal : maximal_ideal >-> prime_ideal.

Local Open Scope quotient_scope.


Module Quotient.

Section ZmodQuotient.
Variables (R : ringType) (I : ideal R).

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

Variables (R : comRingType) (I : proper_ideal R).

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
Proof. by rewrite piE equivE subr0 prop_ideal1. Qed.

Definition rquot_comRingMixin :=
  ComRingMixin mulqA mulqC mul1q mulq_addl nonzero1q.

Canonical rquot_ringType    := Eval hnf in RingType type rquot_comRingMixin.
Canonical rquot_comRingType := Eval hnf in ComRingType type mulqC.

Definition rquot_ringQuotMixin := RingQuotMixin type (lock _) pi_mul.
Canonical rquot_ringQuotType := RingQuotType 1 *%R type rquot_ringQuotMixin.

End RingQuotient.

Section comUnitRingQuotient.

Variables (R : comUnitRingType) (I : proper_ideal R).

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

Lemma pi_unit : forall x, x \in GRing.unit -> \pi x \in unit.
Proof.
  move=> x /unitrP [x' [x'x _]].
  by apply/asboolP; exists (\pi x'); rewrite piE x'x pi_oner.
Qed.

Lemma pi_inv : forall x, x \in GRing.unit -> \pi x^-1 = inv (\pi x).
Proof.
  move=> x ux; pose x_ok := (inv_ok (\pi x)).
  move: (pi_unit ux) x_ok=> -> ixx.
  by rewrite -(mul1r (\pi x^-1 : type)) -ixx -mulrA piE divrr // pi_oner mulr1.
Qed.

Definition rquot_comUnitRingMixin := ComUnitRingMixin mulqVx unitqPl invq0id.

Canonical rquot_UnitRingType := Eval hnf in UnitRingType type rquot_comUnitRingMixin.
Canonical rquot_comUnitRingType := Eval hnf in
 [comUnitRingType of type].

End comUnitRingQuotient.

Section IDomainQuotient.

Variables (R : comUnitRingType) (I : prime_ideal R).

Local Notation type := {quot I}.
  
Lemma rquot_IdomainAxiom (x y : type): x * y = 0 -> (x == 0) || (y == 0).
Proof.
  by move=> /eqP; rewrite -[x]reprK -[y]reprK !piE !equivE !subr0 prime_idealM.
Qed.

Canonical rquot_idomainType := Eval hnf in IdomainType type rquot_IdomainAxiom.

End IDomainQuotient.

Section FieldQuotient.

Variables (R : comUnitRingType) (I : maximal_ideal R).

Local Notation type := {quot I}.

Lemma rquot_FieldAxiom (x : {quot I}): (x != 0) -> x \is a GRing.unit.
Proof.
  rewrite -[x]reprK !piE !equivE subr0=> /maximal_nI1_ex [a [b [Ia eq1abx]]].
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
Notation "R / I" := (@Quotient.rquot_ringQuotType R I) : ideal_scope.

Canonical Quotient.rquot_eqType.
Canonical Quotient.rquot_choiceType.
Canonical Quotient.rquot_zmodType.
Canonical Quotient.rquot_ringType.
Canonical Quotient.rquot_comRingType.
Canonical Quotient.rquot_comUnitRingType.
Canonical Quotient.rquot_UnitRingType.
Canonical Quotient.rquot_fieldType.
Canonical Quotient.rquot_quotType.
Canonical Quotient.rquot_eqQuotType.
Canonical Quotient.rquot_zmodQuotType.
Canonical Quotient.rquot_ringQuotType.

