import CentralBinomialLean.Counting
import CentralBinomialLean.SmallPrimes
import Mathlib.Data.Finset.Card

/-!
# Large-prime deficit and surplus classification

This file formalizes the local predicate equivalences used in Section 6 of
`../erdos728.pdf`.
-/

namespace CentralBinomialLean

namespace Erdos728

attribute [local instance] Classical.propDecidable

/-- Generic finite compensation lemma. If one `P`-only point `d` is
compensated by one `Q`-only point `s`, and all other `P` points are `Q` points,
then the number of `P` points is at most the number of `Q` points. -/
theorem compensated_card_filter_le
    {α : Type*} [DecidableEq α] {S : Finset α} {P Q : α → Prop}
    [DecidablePred P] [DecidablePred Q] {d s : α}
    (hdS : d ∈ S) (hsS : s ∈ S)
    (hPd : P d) (hnPs : ¬ P s) (hQs : Q s)
    (hrest : ∀ x ∈ S, x ≠ d → P x → Q x) :
    (S.filter P).card ≤ (S.filter Q).card := by
  let SP := S.filter P
  let SQ := S.filter Q
  have hdSP : d ∈ SP := by simp [SP, hdS, hPd]
  have hsSQ : s ∈ SQ := by simp [SQ, hsS, hQs]
  have hsub : SP.erase d ⊆ SQ.erase s := by
    intro x hx
    simp only [Finset.mem_erase] at hx ⊢
    have hxne_d : x ≠ d := hx.1
    have hxSP : x ∈ SP := hx.2
    have hxSP' : x ∈ S ∧ P x := by simpa [SP] using hxSP
    have hxS : x ∈ S := hxSP'.1
    have hxP : P x := hxSP'.2
    have hxQ : Q x := hrest x hxS hxne_d hxP
    have hxne_s : x ≠ s := by
      intro hxs
      exact hnPs (hxs ▸ hxP)
    exact ⟨hxne_s, by simp [SQ, hxS, hxQ]⟩
  have hcardErase : (SP.erase d).card ≤ (SQ.erase s).card := Finset.card_le_card hsub
  have hdEq : (SP.erase d).card + 1 = SP.card := Finset.card_erase_add_one hdSP
  have hsEq : (SQ.erase s).card + 1 = SQ.card := Finset.card_erase_add_one hsSQ
  calc
    SP.card = (SP.erase d).card + 1 := hdEq.symm
    _ ≤ (SQ.erase s).card + 1 := Nat.add_le_add_right hcardErase 1
    _ = SQ.card := hsEq

/-- At level `p`, a deficit residue is exactly a lower carry with no central
carry. -/
theorem deficitResidue_iff_lowerCarry_and_not_centralCarry
    {A k p : Nat} (hp : 0 < p) :
    deficitResidue k p (A % p) ↔ lowerCarry A k p ∧ ¬ centralCarry A p := by
  unfold deficitResidue lowerCarry centralCarry
  have hA : A % p < p := Nat.mod_lt A hp
  have hk : k % p < p := Nat.mod_lt k hp
  omega

/-- At a higher modulus `q` with `k < q`, a surplus residue is exactly a
central carry with no lower carry. -/
theorem surplusResidue_iff_centralCarry_and_not_lowerCarry
    {A k q : Nat} (hq : 0 < q) (hkq : k < q) :
    surplusResidue k q (A % q) ↔ centralCarry A q ∧ ¬ lowerCarry A k q := by
  unfold surplusResidue lowerCarry centralCarry
  have hA : A % q < q := Nat.mod_lt A hq
  have hkmod : k % q = k := Nat.mod_eq_of_lt hkq
  rw [hkmod]
  omega

/-- If there is no deficit at level `p`, then the lower carry indicator is
dominated by the central carry indicator at that level. -/
theorem lowerCarry_le_centralCarry_of_not_deficitResidue
    {A k p : Nat} (hp : 0 < p)
    (hnot : ¬ deficitResidue k p (A % p)) :
    lowerCarry A k p → centralCarry A p := by
  intro hlow
  by_contra hcentral
  exact hnot ((deficitResidue_iff_lowerCarry_and_not_centralCarry hp).mpr
    ⟨hlow, hcentral⟩)

/-- A surplus residue gives the compensating central carry and excludes the
corresponding lower carry. -/
theorem centralCarry_and_not_lowerCarry_of_surplusResidue
    {A k q : Nat} (hq : 0 < q) (hkq : k < q)
    (hsurplus : surplusResidue k q (A % q)) :
    centralCarry A q ∧ ¬ lowerCarry A k q :=
  (surplusResidue_iff_centralCarry_and_not_lowerCarry hq hkq).mp hsurplus

/-- If level `1` has no deficit and every later level is pointwise dominated,
then the finite Kummer carry count is dominated. -/
theorem bounded_carry_count_le_of_no_level_one_deficit
    {A k p b : Nat} (hp : 0 < p)
    (hnot : ¬ deficitResidue k p (A % p))
    (hrest :
      ∀ j ∈ Finset.Ico 1 b, j ≠ 1 →
        lowerCarry A k (p ^ j) → centralCarry A (p ^ j)) :
    ((Finset.Ico 1 b).filter fun j => lowerCarry A k (p ^ j)).card
      ≤ ((Finset.Ico 1 b).filter fun j => centralCarry A (p ^ j)).card := by
  apply bounded_carry_count_le_of_pointwise
  intro j hj hlow
  by_cases hj1 : j = 1
  · subst j
    simpa using lowerCarry_le_centralCarry_of_not_deficitResidue hp hnot
      (by simpa using hlow)
  · exact hrest j hj hj1 hlow

/-- A level-`1` deficit is compensated by one later surplus, provided all
other levels are pointwise dominated. -/
theorem bounded_carry_count_le_of_level_one_compensation
    {A k p b js : Nat} (hp : 0 < p)
    (h1mem : 1 ∈ Finset.Ico 1 b) (hjsmem : js ∈ Finset.Ico 1 b)
    (hdef : deficitResidue k p (A % p))
    (hsurplus : surplusResidue k (p ^ js) (A % (p ^ js)))
    (hkpow : k < p ^ js)
    (hrest :
      ∀ j ∈ Finset.Ico 1 b, j ≠ 1 →
        lowerCarry A k (p ^ j) → centralCarry A (p ^ j)) :
    ((Finset.Ico 1 b).filter fun j => lowerCarry A k (p ^ j)).card
      ≤ ((Finset.Ico 1 b).filter fun j => centralCarry A (p ^ j)).card := by
  have hdefCarries :=
    (deficitResidue_iff_lowerCarry_and_not_centralCarry (A := A) (k := k) hp).mp hdef
  have hqpos : 0 < p ^ js := Nat.pow_pos hp
  have hsurplusCarries :=
    centralCarry_and_not_lowerCarry_of_surplusResidue
      (A := A) (k := k) hqpos hkpow hsurplus
  apply compensated_card_filter_le
    (S := Finset.Ico 1 b)
    (P := fun j => lowerCarry A k (p ^ j))
    (Q := fun j => centralCarry A (p ^ j))
    (d := 1) (s := js)
  · exact h1mem
  · exact hjsmem
  · simpa using hdefCarries.1
  · exact hsurplusCarries.2
  · exact hsurplusCarries.1
  · exact hrest

/-- If every non-level-`1` modulus in a Kummer window is above `2k`, Lemma 5
gives pointwise domination at all non-level-`1` levels. -/
theorem later_levels_domination_of_two_mul_lt
    {A k p b : Nat}
    (hlater : ∀ j ∈ Finset.Ico 1 b, j ≠ 1 → 2 * k < p ^ j) :
    ∀ j ∈ Finset.Ico 1 b, j ≠ 1 →
      lowerCarry A k (p ^ j) → centralCarry A (p ^ j) := by
  intro j hj hj1
  exact lowerCarry_le_centralCarry_of_two_mul_lt (hlater j hj hj1)

/-- Medium-prime no-deficit wrapper: if all later levels are above `2k`, then
absence of a level-`1` deficit gives carry-count domination. -/
theorem bounded_carry_count_le_medium_no_deficit
    {A k p b : Nat} (hp : 0 < p)
    (hnot : ¬ deficitResidue k p (A % p))
    (hlater : ∀ j ∈ Finset.Ico 1 b, j ≠ 1 → 2 * k < p ^ j) :
    ((Finset.Ico 1 b).filter fun j => lowerCarry A k (p ^ j)).card
      ≤ ((Finset.Ico 1 b).filter fun j => centralCarry A (p ^ j)).card :=
  bounded_carry_count_le_of_no_level_one_deficit hp hnot
    (later_levels_domination_of_two_mul_lt hlater)

/-- Medium-prime compensation wrapper: if all later levels are above `2k`,
then a level-`1` deficit is offset by any later surplus in the same Kummer
window. -/
theorem bounded_carry_count_le_medium_compensated
    {A k p b js : Nat} (hp : 0 < p)
    (h1mem : 1 ∈ Finset.Ico 1 b) (hjsmem : js ∈ Finset.Ico 1 b)
    (hdef : deficitResidue k p (A % p))
    (hsurplus : surplusResidue k (p ^ js) (A % (p ^ js)))
    (hkpow : k < p ^ js)
    (hlater : ∀ j ∈ Finset.Ico 1 b, j ≠ 1 → 2 * k < p ^ j) :
    ((Finset.Ico 1 b).filter fun j => lowerCarry A k (p ^ j)).card
      ≤ ((Finset.Ico 1 b).filter fun j => centralCarry A (p ^ j)).card :=
  bounded_carry_count_le_of_level_one_compensation hp h1mem hjsmem
    hdef hsurplus hkpow (later_levels_domination_of_two_mul_lt hlater)

/-- In the medium-prime range `2k < p^2`, all non-level-`1` powers in a
Kummer window are above `2k`. -/
theorem later_levels_two_mul_lt_of_lt_sq
    {k p b : Nat} (hp : 2 ≤ p) (hp2 : 2 * k < p ^ 2) :
    ∀ j ∈ Finset.Ico 1 b, j ≠ 1 → 2 * k < p ^ j := by
  intro j hj hj1
  have hj_ge : 2 ≤ j := by
    simp only [Finset.mem_Ico] at hj
    omega
  exact lt_of_lt_of_le hp2 (Nat.pow_le_pow_right (by omega : 0 < p) hj_ge)

/-- Medium-prime no-deficit wrapper specialized to the usual condition
`2k < p^2`. -/
theorem bounded_carry_count_le_medium_no_deficit_of_lt_sq
    {A k p b : Nat} (hp : 2 ≤ p)
    (hp2 : 2 * k < p ^ 2)
    (hnot : ¬ deficitResidue k p (A % p)) :
    ((Finset.Ico 1 b).filter fun j => lowerCarry A k (p ^ j)).card
      ≤ ((Finset.Ico 1 b).filter fun j => centralCarry A (p ^ j)).card :=
  bounded_carry_count_le_medium_no_deficit (by omega : 0 < p) hnot
    (later_levels_two_mul_lt_of_lt_sq hp hp2)

/-- Medium-prime compensation wrapper specialized to the usual condition
`2k < p^2`. -/
theorem bounded_carry_count_le_medium_compensated_of_lt_sq
    {A k p b js : Nat} (hp : 2 ≤ p)
    (hp2 : 2 * k < p ^ 2)
    (h1mem : 1 ∈ Finset.Ico 1 b) (hjsmem : js ∈ Finset.Ico 1 b)
    (hdef : deficitResidue k p (A % p))
    (hsurplus : surplusResidue k (p ^ js) (A % (p ^ js)))
    (hkpow : k < p ^ js) :
    ((Finset.Ico 1 b).filter fun j => lowerCarry A k (p ^ j)).card
      ≤ ((Finset.Ico 1 b).filter fun j => centralCarry A (p ^ j)).card :=
  bounded_carry_count_le_medium_compensated (by omega : 0 < p)
    h1mem hjsmem hdef hsurplus hkpow
    (later_levels_two_mul_lt_of_lt_sq hp hp2)

/-- Medium-prime carry-count domination in the form used by the global
construction: either level `1` has no deficit, or some digit in the Kummer
window supplies a compensating surplus. -/
theorem bounded_carry_count_le_medium_good_of_lt_sq
    {A k p b : Nat} (hp : 2 ≤ p)
    (hp2 : 2 * k < p ^ 2)
    (h1mem : 1 ∈ Finset.Ico 1 b)
    (hgood :
      ¬ deficitResidue k p (A % p) ∨
        ∃ js ∈ Finset.Ico 1 b,
          deficitResidue k p (A % p) ∧
          surplusResidue k (p ^ js) (A % (p ^ js)) ∧
          k < p ^ js) :
    ((Finset.Ico 1 b).filter fun j => lowerCarry A k (p ^ j)).card
      ≤ ((Finset.Ico 1 b).filter fun j => centralCarry A (p ^ j)).card := by
  rcases hgood with hnot | hcomp
  · exact bounded_carry_count_le_medium_no_deficit_of_lt_sq hp hp2 hnot
  · rcases hcomp with ⟨js, hjsmem, hdef, hsurplus, hkpow⟩
    exact bounded_carry_count_le_medium_compensated_of_lt_sq hp hp2
      h1mem hjsmem hdef hsurplus hkpow

/-- Semantic bad residues modulo `p^J`: a level-1 deficit and no higher
surplus at levels `2, ..., J`. -/
noncomputable def semanticBadResidues (k p J : Nat) : Finset Nat :=
  (Finset.range (p ^ J)).filter fun x =>
    deficitResidue k p (x % p) ∧
      ∀ j ∈ Finset.Icc 2 J, ¬ surplusResidue k (p ^ j) (x % (p ^ j))

/-- Base case for bounding semantic bad residues: at `J = 2`, semantic bad
residues inject into the second-level lift set. -/
theorem semanticBadResidues_card_le_two
    {k p : Nat} (hp : 0 < p) :
    (semanticBadResidues k p 2).card ≤ (p / 2) * p := by
  have hsub : semanticBadResidues k p 2 ⊆ deficitSecondLevelLifts k p := by
    intro x hx
    unfold semanticBadResidues at hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    have hxlt : x < p * p := by simpa [pow_two] using hx.1
    have hdef : deficitResidue k p (x % p) := hx.2.1
    exact mem_deficitSecondLevelLifts_of_deficit hp hxlt hdef
  calc
    (semanticBadResidues k p 2).card
        ≤ (deficitSecondLevelLifts k p).card := Finset.card_le_card hsub
    _ ≤ (p / 2) * p := deficitSecondLevelLifts_card_le k p hp

/-- Semantic bad residues are contained in the recursively counted geometric
bad-residue tree. -/
theorem semanticBadResidues_subset_iterAvoidingLiftResidues
    {k p J : Nat} (hp : 0 < p) (hJ : 2 ≤ J) :
    semanticBadResidues k p J ⊆
      iterAvoidingLiftResidues k p (J - 2) (p * p) (deficitSecondLevelLifts k p) := by
  intro x hx
  unfold semanticBadResidues at hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx
  have hxltJ : x < p ^ J := hx.1
  have hdef : deficitResidue k p (x % p) := hx.2.1
  have hnosurplus :
      ∀ j ∈ Finset.Icc 2 J, ¬ surplusResidue k (p ^ j) (x % (p ^ j)) :=
    hx.2.2
  have hp2pos : 0 < p * p := Nat.mul_pos hp hp
  have hxltTree : x < p ^ (J - 2) * (p * p) := by
    have hpow : p ^ (J - 2) * (p * p) = p ^ J := by
      calc
        p ^ (J - 2) * (p * p) = p ^ (J - 2) * p ^ 2 := by rw [pow_two]
        _ = p ^ ((J - 2) + 2) := by rw [← pow_add]
        _ = p ^ J := by rw [Nat.sub_add_cancel hJ]
    simpa [hpow] using hxltJ
  have hbase : x % (p * p) ∈ deficitSecondLevelLifts k p := by
    have hxmodlt : x % (p * p) < p * p := Nat.mod_lt x hp2pos
    have hp_dvd_p2 : p ∣ p * p := dvd_mul_right p p
    have hmodp : (x % (p * p)) % p = x % p := Nat.mod_mod_of_dvd x hp_dvd_p2
    exact mem_deficitSecondLevelLifts_of_deficit hp hxmodlt
      (by simpa [hmodp] using hdef)
  have havoid : ∀ r ∈ Finset.Icc 1 (J - 2),
      ¬ surplusResidue k (p ^ r * (p * p)) (x % (p ^ r * (p * p))) := by
    intro r hr
    have hr_bounds : 1 ≤ r ∧ r ≤ J - 2 := by
      simpa [Finset.mem_Icc] using hr
    have hjmem : r + 2 ∈ Finset.Icc 2 J := by
      simp only [Finset.mem_Icc]
      constructor <;> omega
    have hno := hnosurplus (r + 2) hjmem
    have hpow : p ^ (r + 2) = p ^ r * (p * p) := by
      calc
        p ^ (r + 2) = p ^ r * p ^ 2 := by rw [pow_add]
        _ = p ^ r * (p * p) := by rw [pow_two]
    simpa [hpow] using hno
  exact mem_iterAvoidingLiftResidues_of_avoids hp hp2pos hxltTree hbase havoid

/-- Cardinal bound for the semantic bad-residue set, via the geometric
lifting count. -/
theorem semanticBadResidues_card_le_geometric
    {k p J : Nat} (hp : 0 < p) (hJ : 2 ≤ J) (hbig : 2 * k < p * p) :
    (semanticBadResidues k p J).card
      ≤ (p / 2) * p * (p / 2 + 2) ^ (J - 2) := by
  calc
    (semanticBadResidues k p J).card
        ≤ (iterAvoidingLiftResidues k p (J - 2) (p * p)
            (deficitSecondLevelLifts k p)).card :=
          Finset.card_le_card (semanticBadResidues_subset_iterAvoidingLiftResidues hp hJ)
    _ ≤ (p / 2) * p * (p / 2 + 2) ^ (J - 2) :=
          geometric_badResidues_card_le hp hbig

/-- Semantic bad-residue count with the `3/4` decay factor. -/
theorem semanticBadResidues_card_le_three_quarters
    {k p J : Nat} (hp : 8 ≤ p) (hJ : 2 ≤ J) (hbig : 2 * k < p * p) :
    (semanticBadResidues k p J).card
      ≤ (p / 2) * p * ((3 * p) / 4) ^ (J - 2) := by
  have hp_pos : 0 < p := by omega
  calc
    (semanticBadResidues k p J).card
        ≤ (iterAvoidingLiftResidues k p (J - 2) (p * p)
            (deficitSecondLevelLifts k p)).card :=
          Finset.card_le_card
            (semanticBadResidues_subset_iterAvoidingLiftResidues hp_pos hJ)
    _ ≤ (p / 2) * p * ((3 * p) / 4) ^ (J - 2) :=
          geometric_badResidues_card_le_three_quarters hp hbig

/-- Values in `[lo, hi)` whose residue modulo `p^J` lies in the semantic
bad-residue set. -/
noncomputable def semanticBadPreimageInIco
    (lo hi k p J : Nat) : Finset Nat :=
  residueSetPreimageInIco lo hi (p ^ J) (semanticBadResidues k p J)

/-- Interval count for semantic bad residues using the geometric bound. -/
theorem semanticBadPreimageInIco_card_le_geometric
    {lo hi k p J : Nat} (hp : 0 < p) (hJ : 2 ≤ J) (hbig : 2 * k < p * p) :
    (semanticBadPreimageInIco lo hi k p J).card
      ≤ ((p / 2) * p * (p / 2 + 2) ^ (J - 2))
          * ((hi - lo) / (p ^ J) + 1) := by
  calc
    (semanticBadPreimageInIco lo hi k p J).card
        ≤ (semanticBadResidues k p J).card
            * ((hi - lo) / (p ^ J) + 1) := by
          simpa [semanticBadPreimageInIco] using
            residueSetPreimageInIco_card_le
              (lo := lo) (hi := hi) (q := p ^ J)
              (B := semanticBadResidues k p J)
    _ ≤ ((p / 2) * p * (p / 2 + 2) ^ (J - 2))
          * ((hi - lo) / (p ^ J) + 1) :=
        Nat.mul_le_mul_right _
          (semanticBadResidues_card_le_geometric hp hJ hbig)

/-- Interval count for semantic bad residues using the integer `3/4` decay
factor. -/
theorem semanticBadPreimageInIco_card_le_three_quarters
    {lo hi k p J : Nat} (hp : 8 ≤ p) (hJ : 2 ≤ J) (hbig : 2 * k < p * p) :
    (semanticBadPreimageInIco lo hi k p J).card
      ≤ ((p / 2) * p * ((3 * p) / 4) ^ (J - 2))
          * ((hi - lo) / (p ^ J) + 1) := by
  calc
    (semanticBadPreimageInIco lo hi k p J).card
        ≤ (semanticBadResidues k p J).card
            * ((hi - lo) / (p ^ J) + 1) := by
          simpa [semanticBadPreimageInIco] using
            residueSetPreimageInIco_card_le
              (lo := lo) (hi := hi) (q := p ^ J)
              (B := semanticBadResidues k p J)
    _ ≤ ((p / 2) * p * ((3 * p) / 4) ^ (J - 2))
          * ((hi - lo) / (p ^ J) + 1) :=
        Nat.mul_le_mul_right _
          (semanticBadResidues_card_le_three_quarters hp hJ hbig)

/-- Finite-prime semantic bad-residue avoidance from exact bad-residue
cardinalities. -/
theorem exists_mem_Ico_avoiding_semanticBadResidues
    (P : Finset Nat) {lo hi k J : Nat}
    (hcard :
      ∑ p ∈ P, (semanticBadResidues k p J).card
        * ((hi - lo) / (p ^ J) + 1) < hi - lo) :
    ∃ A ∈ Finset.Ico lo hi,
      ∀ p ∈ P, A % (p ^ J) ∉ semanticBadResidues k p J :=
  exists_mem_Ico_avoiding_residueSets
    (I := P) (lo := lo) (hi := hi)
    (q := fun p => p ^ J)
    (B := fun p => semanticBadResidues k p J)
    hcard

/-- Finite-prime semantic bad-residue avoidance from the geometric
bad-residue estimate. -/
theorem exists_mem_Ico_avoiding_semanticBadResidues_of_geometric_sum
    (P : Finset Nat) {lo hi k J : Nat}
    (hp : ∀ p ∈ P, 0 < p)
    (hJ : 2 ≤ J)
    (hbig : ∀ p ∈ P, 2 * k < p * p)
    (hcard :
      ∑ p ∈ P,
        ((p / 2) * p * (p / 2 + 2) ^ (J - 2))
          * ((hi - lo) / (p ^ J) + 1) < hi - lo) :
    ∃ A ∈ Finset.Ico lo hi,
      ∀ p ∈ P, A % (p ^ J) ∉ semanticBadResidues k p J := by
  apply exists_mem_Ico_avoiding_semanticBadResidues P
  have hsum :
      ∑ p ∈ P, (semanticBadResidues k p J).card
          * ((hi - lo) / (p ^ J) + 1)
        ≤ ∑ p ∈ P,
          ((p / 2) * p * (p / 2 + 2) ^ (J - 2))
            * ((hi - lo) / (p ^ J) + 1) := by
    apply Finset.sum_le_sum
    intro p hpP
    exact Nat.mul_le_mul_right _
      (semanticBadResidues_card_le_geometric (hp p hpP) hJ (hbig p hpP))
  exact lt_of_le_of_lt hsum hcard

/-- Finite-prime semantic bad-residue avoidance from the integer `3/4`
decay estimate. -/
theorem exists_mem_Ico_avoiding_semanticBadResidues_of_three_quarters_sum
    (P : Finset Nat) {lo hi k J : Nat}
    (hp : ∀ p ∈ P, 8 ≤ p)
    (hJ : 2 ≤ J)
    (hbig : ∀ p ∈ P, 2 * k < p * p)
    (hcard :
      ∑ p ∈ P,
        ((p / 2) * p * ((3 * p) / 4) ^ (J - 2))
          * ((hi - lo) / (p ^ J) + 1) < hi - lo) :
    ∃ A ∈ Finset.Ico lo hi,
      ∀ p ∈ P, A % (p ^ J) ∉ semanticBadResidues k p J := by
  apply exists_mem_Ico_avoiding_semanticBadResidues P
  have hsum :
      ∑ p ∈ P, (semanticBadResidues k p J).card
          * ((hi - lo) / (p ^ J) + 1)
        ≤ ∑ p ∈ P,
          ((p / 2) * p * ((3 * p) / 4) ^ (J - 2))
            * ((hi - lo) / (p ^ J) + 1) := by
    apply Finset.sum_le_sum
    intro p hpP
    exact Nat.mul_le_mul_right _
      (semanticBadResidues_card_le_three_quarters (hp p hpP) hJ (hbig p hpP))
  exact lt_of_le_of_lt hsum hcard

/-- Arithmetic-progression version of the finite-prime semantic
bad-residue avoidance theorem. This is the counting shape needed after fixing
the small-prime congruence class `A = offset + scale * t`. -/
theorem exists_mem_range_avoiding_semanticBadResidues_of_three_quarters_sum
    (P : Finset Nat) {offset scale N k J : Nat}
    (hcop : ∀ p ∈ P, Nat.Coprime scale (p ^ J))
    (hp : ∀ p ∈ P, 8 ≤ p)
    (hJ : 2 ≤ J)
    (hbig : ∀ p ∈ P, 2 * k < p * p)
    (hcard :
      ∑ p ∈ P,
        ((p / 2) * p * ((3 * p) / 4) ^ (J - 2))
          * (N / (p ^ J) + 1) < N) :
    ∃ t ∈ Finset.range N,
      ∀ p ∈ P, (offset + scale * t) % (p ^ J) ∉ semanticBadResidues k p J := by
  apply exists_mem_range_avoiding_scaledResidueSets
    (I := P) (offset := offset) (scale := scale) (N := N)
    (q := fun p => p ^ J)
    (B := fun p => semanticBadResidues k p J)
    hcop
  have hsum :
      ∑ p ∈ P, (semanticBadResidues k p J).card * (N / (p ^ J) + 1)
        ≤ ∑ p ∈ P,
          ((p / 2) * p * ((3 * p) / 4) ^ (J - 2))
            * (N / (p ^ J) + 1) := by
    apply Finset.sum_le_sum
    intro p hpP
    exact Nat.mul_le_mul_right _
      (semanticBadResidues_card_le_three_quarters (hp p hpP) hJ (hbig p hpP))
  exact lt_of_le_of_lt hsum hcard

theorem k_lt_pow_of_two_mul_lt_sq
    {k p j : Nat} (hp : 2 ≤ p) (hp2 : 2 * k < p ^ 2) (hj : 2 ≤ j) :
    k < p ^ j := by
  have hklt2 : k < p ^ 2 := by omega
  exact lt_of_lt_of_le hklt2 (Nat.pow_le_pow_right (by omega : 0 < p) hj)

/-- If `A mod p^J` avoids the semantic bad set, then `A` is medium-good:
there is either no level-1 deficit, or some higher level in `2..J` supplies a
compensating surplus. -/
theorem medium_good_of_not_mem_semanticBadResidues
    {A k p b J : Nat} (hp : 2 ≤ p) (hp2 : 2 * k < p ^ 2) (hJ : 2 ≤ J)
    (hwindow : ∀ j ∈ Finset.Icc 2 J, j ∈ Finset.Ico 1 b)
    (hnot : A % (p ^ J) ∉ semanticBadResidues k p J) :
    ¬ deficitResidue k p (A % p) ∨
      ∃ js ∈ Finset.Ico 1 b,
        deficitResidue k p (A % p) ∧
        surplusResidue k (p ^ js) (A % (p ^ js)) ∧
        k < p ^ js := by
  classical
  by_cases hdef : deficitResidue k p (A % p)
  · right
    by_cases hex :
        ∃ js ∈ Finset.Icc 2 J, surplusResidue k (p ^ js) (A % (p ^ js))
    · rcases hex with ⟨js, hjsIcc, hsurplus⟩
      have hjs_ge : 2 ≤ js := by
        simp only [Finset.mem_Icc] at hjsIcc
        exact hjsIcc.1
      exact ⟨js, hwindow js hjsIcc, hdef, hsurplus,
        k_lt_pow_of_two_mul_lt_sq hp hp2 hjs_ge⟩
    · exfalso
      apply hnot
      unfold semanticBadResidues
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · exact Nat.mod_lt A (Nat.pow_pos (by omega : 0 < p) : 0 < p ^ J)
      constructor
      · have hpdvd : p ∣ p ^ J := by
          simpa [pow_one] using Nat.pow_dvd_pow p (by omega : 1 ≤ J)
        have hmodp : (A % p ^ J) % p = A % p := Nat.mod_mod_of_dvd A hpdvd
        simpa [hmodp] using hdef
      · intro j hjIcc hsurplusX
        apply hex
        have hj_le : j ≤ J := by
          simp only [Finset.mem_Icc] at hjIcc
          exact hjIcc.2
        have hmodj : (A % p ^ J) % (p ^ j) = A % (p ^ j) :=
          Nat.mod_mod_of_dvd A (Nat.pow_dvd_pow p hj_le)
        exact ⟨j, hjIcc, by simpa [hmodj] using hsurplusX⟩
  · exact Or.inl hdef

/-- Combining semantic bad-residue avoidance with the medium-prime wrapper
gives finite-window carry-count domination. -/
theorem bounded_carry_count_le_medium_of_not_mem_semanticBadResidues
    {A k p b J : Nat} (hp : 2 ≤ p) (hp2 : 2 * k < p ^ 2) (hJ : 2 ≤ J)
    (h1mem : 1 ∈ Finset.Ico 1 b)
    (hwindow : ∀ j ∈ Finset.Icc 2 J, j ∈ Finset.Ico 1 b)
    (hnot : A % (p ^ J) ∉ semanticBadResidues k p J) :
    ((Finset.Ico 1 b).filter fun j => lowerCarry A k (p ^ j)).card
      ≤ ((Finset.Ico 1 b).filter fun j => centralCarry A (p ^ j)).card :=
  bounded_carry_count_le_medium_good_of_lt_sq hp hp2 h1mem
    (medium_good_of_not_mem_semanticBadResidues hp hp2 hJ hwindow hnot)

/-- A finite-prime, interval-level medium-prime conclusion: if the summed
`3/4` bad-residue estimates are smaller than the interval length, then some
`A ∈ [lo, hi)` has medium-prime carry-count domination for every `p ∈ P`. -/
theorem exists_mem_Ico_medium_carry_count_le_of_three_quarters_sum
    (P : Finset Nat) {lo hi k J b : Nat}
    (hp : ∀ p ∈ P, 8 ≤ p)
    (hJ : 2 ≤ J)
    (hbig : ∀ p ∈ P, 2 * k < p * p)
    (h1mem : 1 ∈ Finset.Ico 1 b)
    (hwindow : ∀ j ∈ Finset.Icc 2 J, j ∈ Finset.Ico 1 b)
    (hcard :
      ∑ p ∈ P,
        ((p / 2) * p * ((3 * p) / 4) ^ (J - 2))
          * ((hi - lo) / (p ^ J) + 1) < hi - lo) :
    ∃ A ∈ Finset.Ico lo hi,
      ∀ p ∈ P,
        ((Finset.Ico 1 b).filter fun j => lowerCarry A k (p ^ j)).card
          ≤ ((Finset.Ico 1 b).filter fun j => centralCarry A (p ^ j)).card := by
  rcases exists_mem_Ico_avoiding_semanticBadResidues_of_three_quarters_sum
      P hp hJ hbig hcard with ⟨A, hAIco, havoid⟩
  refine ⟨A, hAIco, ?_⟩
  intro p hpP
  have hp2 : 2 ≤ p := by
    have hp8 := hp p hpP
    omega
  have hp2big : 2 * k < p ^ 2 := by
    simpa [pow_two] using hbig p hpP
  exact bounded_carry_count_le_medium_of_not_mem_semanticBadResidues
    hp2 hp2big hJ h1mem hwindow (havoid p hpP)

/-- Arithmetic-progression version of the medium-prime conclusion. If the
progression step is coprime to each `p^J` and the summed bad-residue estimates
are smaller than the number of progression points, then some progression
element has carry-count domination for every prime in `P`. -/
theorem exists_mem_range_progression_medium_carry_count_le_of_three_quarters_sum
    (P : Finset Nat) {offset scale N k J b : Nat}
    (hcop : ∀ p ∈ P, Nat.Coprime scale (p ^ J))
    (hp : ∀ p ∈ P, 8 ≤ p)
    (hJ : 2 ≤ J)
    (hbig : ∀ p ∈ P, 2 * k < p * p)
    (h1mem : 1 ∈ Finset.Ico 1 b)
    (hwindow : ∀ j ∈ Finset.Icc 2 J, j ∈ Finset.Ico 1 b)
    (hcard :
      ∑ p ∈ P,
        ((p / 2) * p * ((3 * p) / 4) ^ (J - 2))
          * (N / (p ^ J) + 1) < N) :
    ∃ t ∈ Finset.range N,
      ∀ p ∈ P,
        ((Finset.Ico 1 b).filter fun j => lowerCarry (offset + scale * t) k (p ^ j)).card
          ≤ ((Finset.Ico 1 b).filter fun j =>
            centralCarry (offset + scale * t) (p ^ j)).card := by
  rcases exists_mem_range_avoiding_semanticBadResidues_of_three_quarters_sum
      P hcop hp hJ hbig hcard with ⟨t, htRange, havoid⟩
  refine ⟨t, htRange, ?_⟩
  intro p hpP
  have hp2 : 2 ≤ p := by
    have hp8 := hp p hpP
    omega
  have hp2big : 2 * k < p ^ 2 := by
    simpa [pow_two] using hbig p hpP
  exact bounded_carry_count_le_medium_of_not_mem_semanticBadResidues
    hp2 hp2big hJ h1mem hwindow (havoid p hpP)

end Erdos728

end CentralBinomialLean
