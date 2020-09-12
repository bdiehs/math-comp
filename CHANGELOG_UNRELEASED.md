# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- Added contraposition lemmas involving propositions: `contra_not`, `contraPnot`, `contraTnot`, `contraNnot`, `contraPT`, `contra_notT`, `contra_notN`, `contraPN`, `contraFnot`, `contraPF` and `contra_notF` in ssrbool.v and `contraPeq`, `contra_not_eq`, `contraPneq`, and `contra_neq_not` in eqtype.v
- Contraposition lemmas involving inequalities:
  + in `order.v`:
    `comparable_contraTle`, `comparable_contraTlt`, `comparable_contraNle`, `comparable_contraNlt`, `comparable_contraFle`, `comparable_contraFlt`,
    `contra_leT`, `contra_ltT`, `contra_leN`, `contra_ltN`, `contra_leF`, `contra_ltF`,
    `comparable_contra_leq_le`, `comparable_contra_leq_lt`, `comparable_contra_ltn_le`, `comparable_contra_ltn_lt`,
    `contra_le_leq`, `contra_le_ltn`, `contra_lt_leq`, `contra_lt_ltn`,
    `comparable_contra_le`, `comparable_contra_le_lt`, `comparable_contra_lt_le`, `comparable_contra_lt`,
    `contraTle`, `contraTlt`, `contraNle`, `contraNlt`, `contraFle`, `contraFlt`,
    `contra_leq_le`, `contra_leq_lt`, `contra_ltn_le`, `contra_ltn_lt`,
    `contra_le`, `contra_le_lt`, `contra_lt_le`, `contra_lt`,
    `contra_le_not`, `contra_lt_not`,
    `comparable_contraPle`, `comparable_contraPlt`, `comparable_contra_not_le`, `comparable_contra_not_lt`,
    `contraPle`, `contraPlt`, `contra_not_le`, `contra_not_lt`
  + in `ssrnat.v`:
    `contraTleq`, `contraTltn`, `contraNleq`, `contraNltn`, `contraFleq`, `contraFltn`,
    `contra_leqT`, `contra_ltnT`, `contra_leqN`, `contra_ltnN`, `contra_leqF`, `contra_ltnF`,
    `contra_leq`, `contra_ltn`, `contra_leq_ltn`, `contra_ltn_leq`,
    `contraPleq`, `contraPltn`, `contra_not_leq`, `contra_not_ltn`, `contra_leq_not`, `contra_ltn_not`
- in `ssralg.v`, new lemma `sumr_const_nat` and `iter_addr_0`
- in `ssrnum.v`, new lemma `ler_sum_nat`

- in `seq.v`, new lemmas: `take_uniq`, `drop_uniq`
- in `fintype.v`, new lemmas: `card_geqP`, `card_gt1P`, `card_gt2P`,
  `card_le1_eqP` (generalizes `fintype_le1P`),
- in `finset.v`, neq lemmas: `set_enum`, `cards_eqP`, `cards2P`
- in `fingraph.v`, new lemmas: `fcard_gt0P`, `fcard_gt1P`
- in `finset.v`, new lemmas: `properC`, `properCr`, `properCl`
- in `ssrnat.v`, new lemmas: `subn_minl`, `subn_maxl`
- in `ssrnat.v`, new lemma: `oddS`


- Added a factory `distrLatticePOrderMixin` in order.v to build a
  `distrLatticeType` from a `porderType`.

- in `bigop.v` new lemma `sig_big_dep`, analogous to `pair_big_dep`
  but with an additional dependency in the index types `I` and `J`.
- in `fintype.v` adds lemma `split_ordP`, a variant of `splitP` which
  introduces ordinal equalities between the index and
  `lshift`/`rshift`, rather than equalities in `nat`, which in some
  proofs makes the reasoning easier (cf `matrix.v`), especially
  together with the new lemma `eq_shift` (which is a multi-rule for new
  lemmas `eq_lshift`, `eq_rshift`, `eq_lrshift` and `eq_rlshift`).

- in `matrix.v` new definitions `is_diag_mx` and `is_trig_mx`
  characterizing respectively diagonal and lower triangular matrices.
  We provide the new lemmas `row_diag_mx`, `is_diag_mxP`, `diag_mxP`,
  `diag_mx_is_diag`, `mx0_is_diag`, `is_trig_mxP`,
  `is_diag_mx_is_trig`, `diag_mx_trig`, `mx0_is_trig`,
  `scalar_mx_is_diag`, `is_scalar_mx_is_diag`, `scalar_mx_is_trig` and
  `is_scalar_mx_is_trig`.
- in `matrix.v`, new lemmas `matrix_eq0`, `matrix0Pn`, `rV0Pn` and
  `cV0Pn` to characterize nonzero matrices and find a nonzero
  coefficient.
- in `mxalgebra.v`, completed the theory of `pinvmx` in corner cases,
  using lemmas: `mulmxVp`, `mulmxKp`, `pinvmxE`, `mulVpmx`,
  `pinvmx_free`, and `pinvmx_full`.

- in `poly.v`, new lemma `commr_horner`.
- in `seq.v`, new lemma `mkseqP` to abstract a sequence `s` with
  `mkseq f n`, where `f` and `n` are fresh variables.

- in `seq.v`, new high-order predicate `allrel r s` which
  asserts that a relation `r` holds on all pairs of elements of `s`, and
  + lemmas `allrel_map`, `allrelP` and `allrel0`.
  + lemmas `allrel1`, `allrel2` and `allrel_cons`,
    under assumptions of reflexivity and symmetry of `r`.
- in `mxpoly.v`, new lemmas `mxminpoly_minP` and `dvd_mxminpoly`.
- in `mxalgebra.v` new lemmas `row_base0`, `sub_kermx`, `kermx0` and
  `mulmx_free_eq0`.
- in `bigop.v` new lemma `reindex_omap` generalizes `reindex_onto`
  to the case where the inverse function to `h` is partial (i.e. with
  codomain `option J`, to cope with a potentially empty `J`.

- in `bigop.v` new lemma `bigD1_ord` takes out an element in the
  middle of a `\big_(i < n)` and reindexes the remainder using `lift`.

- in `fintype.v` new lemmas `eq_liftF` and `lift_eqF`.

- in `matrix.v` new predicate `mxOver S` qualified with `\is a`, and
  + new lemmas: `mxOverP`, `mxOverS`, `mxOver_const`, `mxOver_constE`,
    `thinmxOver`, `flatmxOver`, `mxOver_scalar`, `mxOver_scalarE`,
    `mxOverZ`, `mxOverM`, `mxOver_diag`, `mxOver_diagE`.
  + new canonical structures:
    * `mxOver S` is closed under addition if `S` is.
    * `mxOver S` is closed under negation if `S` is.
    * `mxOver S` is a sub Z-module if `S` is.
    * `mxOver S` is a semiring for square matrices if `S` is.
    * `mxOver S` is a subring for square matrices if `S` is.
- in `matrix.v` new lemmas about `map_mx`: `map_mx_id`, `map_mx_comp`,
  `eq_in_map_mx`, `eq_map_mx` and `map_mx_id_in`.
- in `matrix.v`, new lemmas `row_usubmx`, `row_dsubmx`, `col_lsubmx`,
  and `col_rsubmx`.
- in `seq.v` new lemmas `find_ltn`, `has_take`, `has_take_leq`,
  `index_ltn`, `in_take`, `in_take_leq`, `split_find_nth`,
  `split_find` and `nth_rcons_cat_find`.

- in `matrix.v` new lemma `mul_rVP`.

- in `matrix.v`:
  + new inductions lemmas: `row_ind`, `col_ind`, `mx_ind`, `sqmx_ind`,
    `ringmx_ind`, `trigmx_ind`, `trigsqmx_ind`, `diagmx_ind`,
    `diagsqmx_ind`.
  + missing lemma `trmx_eq0`
  + new lemmas about diagonal and triangular matrices: `mx11_is_diag`,
    `mx11_is_trig`, `diag_mx_row`, `is_diag_mxEtrig`, `is_diag_trmx`,
    `ursubmx_trig`, `dlsubmx_diag`, `ulsubmx_trig`, `drsubmx_trig`,
    `ulsubmx_diag`, `drsubmx_diag`, `is_trig_block_mx`,
    `is_diag_block_mx`, and `det_trig`.

- in `mxpoly.v` new lemmas `horner_mx_diag`, `char_poly_trig`,
   `root_mxminpoly`, and `mxminpoly_diag`
- in `mxalgebra.v`, new lemma `sub_sums_genmxP` (generalizes `sub_sumsmxP`).

- in `bigop.v` new lemma `big_uncond`. The ideal name is `big_rmcond`
  but it has just been deprecated from its previous meaning (see
  Changed section) so as to reuse it in next mathcomp release.

- in `bigop.v` new lemma `big_uncond_in` is a new alias of
  `big_rmcond_in` for the sake of uniformity, but it is already
  deprecated and will be removed two releases from now.

### Changed

- in ssrbool.v, use `Reserved Notation` for `[rel _ _ : _ | _]` to avoid warnings with coq-8.12
- in `ssrAC.v`, fix `non-reversible-notation` warnings

- In the definition of structures in order.v, displays are removed from
  parameters of mixins and fields of classes internally and now only appear in
  parameters of structures. Consequently, each mixin is now parameterized by a
  class rather than a structure, and the corresponding factory parameterized by
  a structure is provided to replace the use of the mixin. These factories have
  the same names as in the mixins before this change except that `bLatticeMixin`
  and `tbLatticeMixin` have been renamed to `bottomMixin` and `topMixin`
  respectively.

- The `dual_*` notations such as `dual_le` in order.v are now qualified with the
  `Order` module.

- Lemma `big_rmcond` is deprecated and has been renamed
  `big_rmcomd_in` (and aliased `big_uncond_in`, see Added). The
  variant which does not require an `eqType` is currently named
  `big_uncond` (cf Added) but it will be renamed `big_mkcond` in the
  next release.


### Renamed

- `big_rmcond` -> `big_rmcond_in` (cf Changed section)

### Removed

### Infrastructure

### Misc
