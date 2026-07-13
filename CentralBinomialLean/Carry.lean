import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-!
# Carry lemmas for the deterministic Erdos #728 proof

This file starts the formalization of the proof in `../erdos728.pdf`.
It isolates the finite, deterministic carry bookkeeping used in Sections 4--6.
-/

namespace CentralBinomialLean

namespace Erdos728

attribute [local instance] Classical.propDecidable

/-- The carry indicator for the lower binomial coefficient `(A + k).choose k`
at modulus `q`. -/
def lowerCarry (A k q : Nat) : Prop :=
  q ≤ A % q + k % q

/-- The carry indicator for the central binomial coefficient `(2 * A).choose A`
at modulus `q`. -/
def centralCarry (A q : Nat) : Prop :=
  q ≤ 2 * (A % q)

/-- Paper Lemma 5: above `2k`, every lower carry is also a central carry. -/
theorem lowerCarry_le_centralCarry_of_two_mul_lt
    {A k q : Nat} (h2kq : 2 * k < q) :
    lowerCarry A k q → centralCarry A q := by
  intro h
  unfold lowerCarry centralCarry at *
  have hkq : k < q := by omega
  rw [Nat.mod_eq_of_lt hkq] at h
  omega

/-- If two numbers are congruent modulo `q`, they have the same carry indicator
against `k` and against themselves. This is the local content of paper Lemma 6. -/
theorem lowerCarry_eq_centralCarry_of_modEq
    {A k q : Nat} (hA : A % q = k % q) :
    lowerCarry A k q ↔ centralCarry k q := by
  unfold lowerCarry centralCarry
  rw [hA]
  omega

/-- A residue `r` modulo `p` creates the unit level-`p` deficit for a large
prime, represented in the interval `[0, p)`. -/
def deficitResidue (k p r : Nat) : Prop :=
  p - (k % p) ≤ r ∧ 2 * r < p

/-- A residue `r` modulo `q` creates a higher-power surplus carry:
central carry, but no lower carry. -/
def surplusResidue (k q r : Nat) : Prop :=
  q ≤ 2 * r ∧ r < q - k

/-- The interval defining deficit residues has length at most `p / 2`.

This is the finite counting input behind `|D_p| ≤ p/2`. -/
theorem deficitResidue_card_le (k p : Nat) (hp : 0 < p) :
    ((Finset.range p).filter fun r => deficitResidue k p r).card ≤ p / 2 := by
  classical
  let shiftDown : Nat → Nat := fun r => r - 1
  have hinj : Set.InjOn shiftDown ((Finset.range p).filter fun r => deficitResidue k p r) := by
    intro a ha b hb hab
    simp at ha hb
    have ha0 : 0 < a := by
      have hklt : k % p < p := Nat.mod_lt k hp
      have hpos : 0 < p - k % p := Nat.sub_pos_of_lt hklt
      exact lt_of_lt_of_le hpos ha.2.1
    have hb0 : 0 < b := by
      have hklt : k % p < p := Nat.mod_lt k hp
      have hpos : 0 < p - k % p := Nat.sub_pos_of_lt hklt
      exact lt_of_lt_of_le hpos hb.2.1
    unfold shiftDown at hab
    omega
  have hsub :
      (((Finset.range p).filter fun r => deficitResidue k p r).image shiftDown)
        ⊆ Finset.range (p / 2) := by
    intro r hr
    simp only [Finset.mem_range]
    simp at hr
    rcases hr with ⟨x, hx, rfl⟩
    unfold deficitResidue at hx
    have hx0 : 0 < x := by
      have hklt : k % p < p := Nat.mod_lt k hp
      have hpos : 0 < p - k % p := Nat.sub_pos_of_lt hklt
      exact lt_of_lt_of_le hpos hx.2.1
    have hxle : x ≤ p / 2 := by
      rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
      nlinarith
    change x - 1 < p / 2
    omega
  calc
    ((Finset.range p).filter fun r => deficitResidue k p r).card
        = (((Finset.range p).filter fun r => deficitResidue k p r).image shiftDown).card := by
          rw [Finset.card_image_of_injOn hinj]
    _ ≤ p / 2 := by simpa using Finset.card_le_card hsub

/-- At a modulus `q > 2k`, the surplus interval is nonempty. -/
theorem exists_surplusResidue_of_two_mul_lt
    {k q : Nat} (h2kq : 2 * k + 1 < q) :
    ∃ r, r < q ∧ surplusResidue k q r := by
  refine ⟨(q + 1) / 2, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega

/-- Lifts modulo `p * Q` of a fixed residue modulo `Q`. -/
def lifts (p Q u : Nat) : Finset Nat :=
  (Finset.range p).image fun l => u + l * Q

/-- The lifting map `l ↦ u + lQ` is injective when `Q > 0`. -/
theorem lifts_card {p Q u : Nat} (hQ : 0 < Q) :
    (lifts p Q u).card = p := by
  unfold lifts
  rw [Finset.card_image_of_injOn]
  · exact Finset.card_range p
  · intro a ha b hb hab
    have hmul : a * Q = b * Q := Nat.add_left_cancel hab
    exact Nat.eq_of_mul_eq_mul_right hQ hmul

/-- Indices that can avoid the surplus interval at one lifting step. -/
def badLiftIndices (p : Nat) : Finset Nat :=
  insert (p - 1) (Finset.range (p / 2 + 1))

theorem badLiftIndices_card_le (p : Nat) :
    (badLiftIndices p).card ≤ p / 2 + 2 := by
  unfold badLiftIndices
  calc
    (insert (p - 1) (Finset.range (p / 2 + 1))).card
        ≤ (Finset.range (p / 2 + 1)).card + 1 := Finset.card_insert_le _ _
    _ = p / 2 + 2 := by simp

theorem low_lift_index_le_half
    {p Q u l : Nat} (hQ : 0 < Q)
    (h : 2 * (u + l * Q) < p * Q) :
    l ≤ p / 2 := by
  have hle : 2 * l * Q ≤ 2 * (u + l * Q) := by nlinarith
  have hlt2 : 2 * l * Q < p * Q := lt_of_le_of_lt hle h
  by_contra hn
  have hp : p < 2 * l := by omega
  have hmul : p * Q < 2 * l * Q := Nat.mul_lt_mul_of_pos_right hp hQ
  omega

theorem high_lift_index_eq_last
    {k p Q u l : Nat} (hkQ : k < Q) (hu : u < Q) (hlp : l < p)
    (h : p * Q - k ≤ u + l * Q) :
    l = p - 1 := by
  by_contra hne
  have hle : l ≤ p - 2 := by omega
  have hsum : u + l * Q + k < Q + l * Q + Q := by nlinarith
  have hshape : Q + l * Q + Q = (l + 2) * Q := by ring
  have hmul_le : (l + 2) * Q ≤ p * Q := Nat.mul_le_mul_right Q (by omega)
  have hupper : u + l * Q + k < p * Q := by
    calc
      u + l * Q + k < Q + l * Q + Q := hsum
      _ = (l + 2) * Q := hshape
      _ ≤ p * Q := hmul_le
  omega

/-- A real-interval-free version of the per-level bound used in Lemma 7:
among the `p` lifts of a residue modulo `Q`, at most `p/2 + 2` avoid the
higher-power surplus. This is stated as the reusable finite-counting target
for the residue-decay induction. -/
theorem lifts_avoiding_surplus_card_le
    {k p Q u : Nat}
    (hQ : 0 < Q) (hQbig : 2 * k < Q) (hu : u < Q) :
    ((lifts p Q u).filter fun x => ¬ surplusResidue k (p * Q) x).card
      ≤ p / 2 + 2 := by
  classical
  let badImages := (badLiftIndices p).image fun l => u + l * Q
  have hsub :
      ((lifts p Q u).filter fun x => ¬ surplusResidue k (p * Q) x) ⊆ badImages := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    rcases Finset.mem_image.mp hx.1 with ⟨l, hlrange, rfl⟩
    have hlp : l < p := by simpa using hlrange
    have hkQ : k < Q := by omega
    have hcases :
        2 * (u + l * Q) < p * Q ∨ p * Q - k ≤ u + l * Q := by
      unfold surplusResidue at hx
      omega
    refine Finset.mem_image.mpr ⟨l, ?_, rfl⟩
    unfold badLiftIndices
    rcases hcases with hlow | hhigh
    · have hlhalf : l ≤ p / 2 := low_lift_index_le_half hQ hlow
      simp only [Finset.mem_insert, Finset.mem_range]
      right
      omega
    · have hlast : l = p - 1 := high_lift_index_eq_last hkQ hu hlp hhigh
      simp only [Finset.mem_insert, Finset.mem_range]
      left
      exact hlast
  calc
    ((lifts p Q u).filter fun x => ¬ surplusResidue k (p * Q) x).card
        ≤ badImages.card := Finset.card_le_card hsub
    _ ≤ (badLiftIndices p).card := Finset.card_image_le
    _ ≤ p / 2 + 2 := badLiftIndices_card_le p

/-- Product-form version of `lifts_avoiding_surplus_card_le`.

For a set `S` of residues modulo `Q`, this counts pairs `(u, l)` with
`u ∈ S`, `l < p`, and the lift `u + lQ` avoiding the surplus interval at
modulus `pQ`. -/
noncomputable def avoidingLiftPairs (k p Q : Nat) (S : Finset Nat) : Finset (Nat × Nat) :=
  (S ×ˢ Finset.range p).filter fun ul =>
    ¬ surplusResidue k (p * Q) (ul.1 + ul.2 * Q)

theorem avoidingLiftPairs_card_le
    {k p Q : Nat} {S : Finset Nat}
    (hQ : 0 < Q) (hQbig : 2 * k < Q)
    (hS : ∀ u ∈ S, u < Q) :
    (avoidingLiftPairs k p Q S).card ≤ S.card * (p / 2 + 2) := by
  classical
  have hsub :
      avoidingLiftPairs k p Q S ⊆ S ×ˢ badLiftIndices p := by
    intro ul hul
    rcases ul with ⟨u, l⟩
    unfold avoidingLiftPairs at hul
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hul ⊢
    rcases hul with ⟨⟨huS, hlp⟩, havoid⟩
    have huQ : u < Q := hS u huS
    have hkQ : k < Q := by omega
    have hcases :
        2 * (u + l * Q) < p * Q ∨ p * Q - k ≤ u + l * Q := by
      unfold surplusResidue at havoid
      omega
    refine ⟨huS, ?_⟩
    unfold badLiftIndices
    rcases hcases with hlow | hhigh
    · have hlhalf : l ≤ p / 2 := low_lift_index_le_half hQ hlow
      simp only [Finset.mem_insert, Finset.mem_range]
      right
      omega
    · have hlast : l = p - 1 := high_lift_index_eq_last hkQ huQ hlp hhigh
      simp only [Finset.mem_insert, Finset.mem_range]
      left
      exact hlast
  calc
    (avoidingLiftPairs k p Q S).card
        ≤ (S ×ˢ badLiftIndices p).card := Finset.card_le_card hsub
    _ = S.card * (badLiftIndices p).card := Finset.card_product _ _
    _ ≤ S.card * (p / 2 + 2) :=
      Nat.mul_le_mul_left S.card (badLiftIndices_card_le p)

/-- One step of the bad-residue tree: lift residues from modulus `Q` to
modulus `pQ`, retaining only lifts that avoid the surplus interval. -/
noncomputable def avoidingLiftResidues (k p Q : Nat) (S : Finset Nat) : Finset Nat :=
  (avoidingLiftPairs k p Q S).image fun ul => ul.1 + ul.2 * Q

theorem avoidingLiftResidues_card_le
    {k p Q : Nat} {S : Finset Nat}
    (hQ : 0 < Q) (hQbig : 2 * k < Q)
    (hS : ∀ u ∈ S, u < Q) :
    (avoidingLiftResidues k p Q S).card ≤ S.card * (p / 2 + 2) := by
  unfold avoidingLiftResidues
  exact (Finset.card_image_le.trans (avoidingLiftPairs_card_le hQ hQbig hS))

theorem avoidingLiftResidues_mem_lt
    {k p Q : Nat} {S : Finset Nat}
    (hS : ∀ u ∈ S, u < Q) :
    ∀ x ∈ avoidingLiftResidues k p Q S, x < p * Q := by
  intro x hx
  unfold avoidingLiftResidues at hx
  rcases Finset.mem_image.mp hx with ⟨ul, hul, rfl⟩
  rcases ul with ⟨u, l⟩
  unfold avoidingLiftPairs at hul
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hul
  have huQ : u < Q := hS u hul.1.1
  have hlp : l < p := hul.1.2
  nlinarith

/-- One-step membership in the lifted bad tree from a previous residue and
avoidance of the current surplus interval. -/
theorem mem_avoidingLiftResidues_of_prev_of_not_surplus
    {k p Q x : Nat} {S : Finset Nat} (hQ : 0 < Q) (hx : x < p * Q)
    (hprev : x % Q ∈ S) (havoid : ¬ surplusResidue k (p * Q) x) :
    x ∈ avoidingLiftResidues k p Q S := by
  unfold avoidingLiftResidues avoidingLiftPairs
  refine Finset.mem_image.mpr ⟨(x % Q, x / Q), ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    constructor
    · constructor
      · exact hprev
      · rw [Nat.div_lt_iff_lt_mul hQ]
        exact hx
    · have hdecomp : x % Q + (x / Q) * Q = x := by
        simpa [Nat.mul_comm] using Nat.mod_add_div x Q
      simpa [hdecomp]
  · simpa [Nat.mul_comm] using Nat.mod_add_div x Q

/-- Iterate the bad-residue lifting operation for `n` further digit levels,
starting from residues modulo `Q`. -/
noncomputable def iterAvoidingLiftResidues (k p : Nat) :
    Nat → Nat → Finset Nat → Finset Nat
  | 0, _Q, S => S
  | n + 1, Q, S =>
      iterAvoidingLiftResidues k p n (p * Q) (avoidingLiftResidues k p Q S)

theorem iterAvoidingLiftResidues_mem_lt
    {k p n Q : Nat} {S : Finset Nat}
    (hS : ∀ u ∈ S, u < Q) :
    ∀ x ∈ iterAvoidingLiftResidues k p n Q S, x < p ^ n * Q := by
  induction n generalizing Q S with
  | zero =>
      intro x hx
      simpa using hS x hx
  | succ n ih =>
      intro x hx
      unfold iterAvoidingLiftResidues at hx
      have hstep :
          ∀ u ∈ avoidingLiftResidues k p Q S, u < p * Q :=
        avoidingLiftResidues_mem_lt hS
      have hxlt := ih hstep x hx
      have hpow : p ^ (n + 1) * Q = p ^ n * (p * Q) := by
        ring
      simpa [hpow] using hxlt

theorem iterAvoidingLiftResidues_card_le
    {k p n Q : Nat} {S : Finset Nat}
    (hp : 0 < p) (hQ : 0 < Q) (hQbig : 2 * k < Q)
    (hS : ∀ u ∈ S, u < Q) :
    (iterAvoidingLiftResidues k p n Q S).card
      ≤ S.card * (p / 2 + 2) ^ n := by
  induction n generalizing Q S with
  | zero =>
      simp [iterAvoidingLiftResidues]
  | succ n ih =>
      unfold iterAvoidingLiftResidues
      let S' := avoidingLiftResidues k p Q S
      have hstepCard : S'.card ≤ S.card * (p / 2 + 2) :=
        avoidingLiftResidues_card_le hQ hQbig hS
      have hS' : ∀ u ∈ S', u < p * Q :=
        avoidingLiftResidues_mem_lt hS
      have hpQ : 0 < p * Q := Nat.mul_pos hp hQ
      have hQbig' : 2 * k < p * Q := by
        have hQle : Q ≤ p * Q := by
          have hp1 : 1 ≤ p := hp
          nlinarith
        omega
      have ih' := ih hpQ hQbig' hS'
      calc
        (iterAvoidingLiftResidues k p n (p * Q) S').card
            ≤ S'.card * (p / 2 + 2) ^ n := ih'
        _ ≤ (S.card * (p / 2 + 2)) * (p / 2 + 2) ^ n :=
            Nat.mul_le_mul_right _ hstepCard
        _ = S.card * (p / 2 + 2) ^ (n + 1) := by ring

/-- Membership in the iterated bad-residue tree from semantic avoidance at
each lifted level. -/
theorem mem_iterAvoidingLiftResidues_of_avoids
    {k p n Q x : Nat} {S : Finset Nat} (hp : 0 < p) (hQ : 0 < Q)
    (hx : x < p ^ n * Q) (hbase : x % Q ∈ S)
    (havoid : ∀ r ∈ Finset.Icc 1 n,
      ¬ surplusResidue k (p ^ r * Q) (x % (p ^ r * Q))) :
    x ∈ iterAvoidingLiftResidues k p n Q S := by
  induction n generalizing Q S x with
  | zero =>
      simp only [iterAvoidingLiftResidues]
      have hxQ : x < Q := by simpa using hx
      simpa [Nat.mod_eq_of_lt hxQ] using hbase
  | succ n ih =>
      unfold iterAvoidingLiftResidues
      have hpQ : 0 < p * Q := Nat.mul_pos hp hQ
      have hxmod_lt : x % (p * Q) < p * Q := Nat.mod_lt x hpQ
      have hprevBase : (x % (p * Q)) % Q ∈ S := by
        have hQdvd : Q ∣ p * Q := dvd_mul_left Q p
        have hmod : (x % (p * Q)) % Q = x % Q := Nat.mod_mod_of_dvd x hQdvd
        simpa [hmod] using hbase
      have havoid1 : ¬ surplusResidue k (p * Q) (x % (p * Q)) := by
        have hmem : 1 ∈ Finset.Icc 1 (n + 1) := by simp
        have h := havoid 1 hmem
        simpa using h
      have hstep : x % (p * Q) ∈ avoidingLiftResidues k p Q S :=
        mem_avoidingLiftResidues_of_prev_of_not_surplus hQ hxmod_lt hprevBase havoid1
      have hx' : x < p ^ n * (p * Q) := by
        have hpow : p ^ (n + 1) * Q = p ^ n * (p * Q) := by ring
        simpa [hpow] using hx
      have havoid' : ∀ r ∈ Finset.Icc 1 n,
          ¬ surplusResidue k (p ^ r * (p * Q)) (x % (p ^ r * (p * Q))) := by
        intro r hr
        have hr1mem : r + 1 ∈ Finset.Icc 1 (n + 1) := by
          simp only [Finset.mem_Icc] at hr ⊢
          omega
        have h := havoid (r + 1) hr1mem
        have hmul : p ^ (r + 1) * Q = p ^ r * (p * Q) := by ring
        simpa [hmul] using h
      exact ih hpQ hx' hstep havoid'

/-- Deficit residues modulo `p`, represented in `[0, p)`. -/
noncomputable def deficitResidues (k p : Nat) : Finset Nat :=
  (Finset.range p).filter fun r => deficitResidue k p r

theorem deficitResidues_card_le (k p : Nat) (hp : 0 < p) :
    (deficitResidues k p).card ≤ p / 2 := by
  simpa [deficitResidues] using deficitResidue_card_le k p hp

theorem deficitResidues_mem_lt {k p r : Nat} (hr : r ∈ deficitResidues k p) :
    r < p := by
  unfold deficitResidues at hr
  simp only [Finset.mem_filter, Finset.mem_range] at hr
  exact hr.1

/-- The paper's first two levels: choose a deficit residue modulo `p`, then
lift freely to modulo `p^2`. The proof of Lemma 7 uses this level trivially,
giving the factor `(p/2) * p`. -/
noncomputable def deficitSecondLevelLifts (k p : Nat) : Finset Nat :=
  (deficitResidues k p ×ˢ Finset.range p).image fun ul => ul.1 + ul.2 * p

theorem deficitSecondLevelLifts_card_le (k p : Nat) :
    0 < p →
    (deficitSecondLevelLifts k p).card ≤ (p / 2) * p := by
  intro hp
  unfold deficitSecondLevelLifts
  calc
    ((deficitResidues k p ×ˢ Finset.range p).image fun ul => ul.1 + ul.2 * p).card
        ≤ (deficitResidues k p ×ˢ Finset.range p).card := Finset.card_image_le
    _ = (deficitResidues k p).card * p := by
      rw [Finset.card_product, Finset.card_range]
    _ ≤ (p / 2) * p := Nat.mul_le_mul_right p (deficitResidues_card_le k p hp)

theorem deficitSecondLevelLifts_mem_lt
    {k p : Nat} :
    ∀ x ∈ deficitSecondLevelLifts k p, x < p * p := by
  intro x hx
  unfold deficitSecondLevelLifts at hx
  rcases Finset.mem_image.mp hx with ⟨ul, hul, rfl⟩
  rcases ul with ⟨r, l⟩
  simp only [Finset.mem_product, Finset.mem_range] at hul
  have hrp : r < p := deficitResidues_mem_lt hul.1
  have hlp : l < p := hul.2
  nlinarith

/-- Any residue below `p^2` whose level-`p` residue is deficient lies in the
second-level lift set. -/
theorem mem_deficitSecondLevelLifts_of_deficit
    {k p x : Nat} (hp : 0 < p) (hx : x < p * p)
    (hdef : deficitResidue k p (x % p)) :
    x ∈ deficitSecondLevelLifts k p := by
  unfold deficitSecondLevelLifts
  refine Finset.mem_image.mpr ⟨(x % p, x / p), ?_, ?_⟩
  · simp only [Finset.mem_product, Finset.mem_range]
    constructor
    · unfold deficitResidues
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.mod_lt x hp, hdef⟩
    · rw [Nat.div_lt_iff_lt_mul hp]
      simpa [mul_comm] using hx
  · simpa [Nat.mul_comm] using Nat.mod_add_div x p

/-- Geometric finite residue count corresponding to the counting core of paper
Lemma 7. Starting from the level-`p` deficit classes and giving level `p^2`
the paper's trivial factor `p`, every further digit level contributes at most
`p / 2 + 2` choices. -/
theorem geometric_badResidues_card_le
    {k p J : Nat} (hp : 0 < p) (hbig : 2 * k < p * p) :
    (iterAvoidingLiftResidues k p (J - 2) (p * p) (deficitSecondLevelLifts k p)).card
      ≤ (p / 2) * p * (p / 2 + 2) ^ (J - 2) := by
  have hp2 : 0 < p * p := Nat.mul_pos hp hp
  have hS :
      ∀ u ∈ deficitSecondLevelLifts k p, u < p * p :=
    deficitSecondLevelLifts_mem_lt
  have hiter :=
    iterAvoidingLiftResidues_card_le
      (k := k) (p := p) (n := J - 2) (Q := p * p)
      (S := deficitSecondLevelLifts k p)
      hp hp2 hbig hS
  calc
    (iterAvoidingLiftResidues k p (J - 2) (p * p) (deficitSecondLevelLifts k p)).card
        ≤ (deficitSecondLevelLifts k p).card * (p / 2 + 2) ^ (J - 2) := hiter
    _ ≤ ((p / 2) * p) * (p / 2 + 2) ^ (J - 2) :=
        Nat.mul_le_mul_right _ (deficitSecondLevelLifts_card_le k p hp)
    _ = (p / 2) * p * (p / 2 + 2) ^ (J - 2) := by ring

theorem liftDecayFactor_le_three_mul_div_four {p : Nat} (hp : 8 ≤ p) :
    p / 2 + 2 ≤ (3 * p) / 4 := by
  omega

/-- Paper Lemma 7's geometric decay factor in integer form. For `p ≥ 8`,
the per-level factor `p / 2 + 2` is at most `(3p) / 4`. -/
theorem geometric_badResidues_card_le_three_quarters
    {k p J : Nat} (hp : 8 ≤ p) (hbig : 2 * k < p * p) :
    (iterAvoidingLiftResidues k p (J - 2) (p * p) (deficitSecondLevelLifts k p)).card
      ≤ (p / 2) * p * ((3 * p) / 4) ^ (J - 2) := by
  have hp_pos : 0 < p := by omega
  have hgeom :=
    geometric_badResidues_card_le (k := k) (p := p) (J := J) hp_pos hbig
  have hpow :
      (p / 2 + 2) ^ (J - 2) ≤ ((3 * p) / 4) ^ (J - 2) :=
    Nat.pow_le_pow_left (liftDecayFactor_le_three_mul_div_four hp) _
  calc
    (iterAvoidingLiftResidues k p (J - 2) (p * p) (deficitSecondLevelLifts k p)).card
        ≤ (p / 2) * p * (p / 2 + 2) ^ (J - 2) := hgeom
    _ ≤ (p / 2) * p * ((3 * p) / 4) ^ (J - 2) :=
        Nat.mul_le_mul_left ((p / 2) * p) hpow

end Erdos728

end CentralBinomialLean
