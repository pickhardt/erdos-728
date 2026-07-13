import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Union
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-!
# Finite counting utilities

This file contains deterministic finite union-bound lemmas used by the global
construction.
-/

namespace CentralBinomialLean

namespace Erdos728

open Finset

/-- A finite union has cardinality at most the sum of the cardinalities of its
members. -/
theorem card_biUnion_le_sum {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (B : ι → Finset α) :
    (I.biUnion B).card ≤ ∑ i ∈ I, (B i).card := by
  induction I using Finset.induction_on with
  | empty => simp
  | insert a I ha ih =>
      rw [Finset.biUnion_insert]
      calc
        (B a ∪ I.biUnion B).card ≤ (B a).card + (I.biUnion B).card :=
          Finset.card_union_le _ _
        _ ≤ (B a).card + ∑ i ∈ I, (B i).card := Nat.add_le_add_left ih _
        _ = ∑ i ∈ insert a I, (B i).card := by simp [ha]

/-- Deterministic finite avoidance: if the sum of the sizes of all bad sets is
smaller than the universe, some universe element avoids every bad set. -/
theorem exists_mem_not_mem_biUnion_of_sum_card_lt
    {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (U : Finset α) (B : ι → Finset α)
    (hsub : ∀ i ∈ I, B i ⊆ U)
    (hcard : ∑ i ∈ I, (B i).card < U.card) :
    ∃ x ∈ U, ∀ i ∈ I, x ∉ B i := by
  by_contra hnone
  push Not at hnone
  have hUsub : U ⊆ I.biUnion B := by
    intro x hxU
    rcases hnone x hxU with ⟨i, hiI, hxi⟩
    exact Finset.mem_biUnion.mpr ⟨i, hiI, hxi⟩
  have hUnionSub : I.biUnion B ⊆ U := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨i, hiI, hxi⟩
    exact hsub i hiI hxi
  have hUcard_le_union : U.card ≤ (I.biUnion B).card := Finset.card_le_card hUsub
  have hunion_card_le_sum : (I.biUnion B).card ≤ ∑ i ∈ I, (B i).card :=
    card_biUnion_le_sum I B
  omega

/-- The elements below `N` lying in one residue class modulo `q`. -/
noncomputable def residueClassInRange (N q r : Nat) : Finset Nat :=
  (Finset.range N).filter fun x => x % q = r

/-- Each residue class modulo `q` appears at most `N / q + 1` times among
the first `N` natural numbers. -/
theorem residueClassInRange_card_le {N q r : Nat} :
    (residueClassInRange N q r).card ≤ N / q + 1 := by
  calc
    (residueClassInRange N q r).card
        ≤ (Finset.range (N / q + 1)).card := by
          apply Finset.card_le_card_of_injOn (fun x => x / q)
          · intro x hx
            have hx' : x ∈ residueClassInRange N q r := hx
            unfold residueClassInRange at hx'
            simp only [Finset.mem_filter, Finset.mem_range] at hx'
            have hxdiv : x / q ≤ N / q :=
              Nat.div_le_div_right (Nat.le_of_lt hx'.1)
            simpa [Finset.mem_range] using Nat.lt_succ_of_le hxdiv
          · intro a ha b hb hab
            have ha' : a ∈ residueClassInRange N q r := ha
            have hb' : b ∈ residueClassInRange N q r := hb
            unfold residueClassInRange at ha' hb'
            simp only [Finset.mem_filter, Finset.mem_range] at ha' hb'
            have hmoda : a % q = r := ha'.2
            have hmodb : b % q = r := hb'.2
            have hab' : a / q = b / q := hab
            calc
              a = a % q + q * (a / q) := (Nat.mod_add_div a q).symm
              _ = r + q * (b / q) := by rw [hmoda, hab']
              _ = b % q + q * (b / q) := by rw [hmodb]
              _ = b := Nat.mod_add_div b q
    _ = N / q + 1 := by simp

/-- If each summand is bounded by `C`, then the finite sum is bounded by
`card * C`. -/
theorem sum_le_card_mul {α : Type*} [DecidableEq α]
    {s : Finset α} {f : α → Nat} {C : Nat}
    (h : ∀ a ∈ s, f a ≤ C) :
    (∑ a ∈ s, f a) ≤ s.card * C := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hfa : f a ≤ C := h a (by simp [ha])
      have hs : (∑ x ∈ s, f x) ≤ s.card * C := by
        apply ih
        intro x hx
        exact h x (by simp [hx])
      calc
        (∑ x ∈ insert a s, f x)
            = f a + ∑ x ∈ s, f x := by simp [ha]
        _ ≤ C + s.card * C := Nat.add_le_add hfa hs
        _ = (insert a s).card * C := by
          simp [Finset.card_insert_of_notMem ha]
          ring_nf

/-- The elements below `N` whose residue modulo `q` lies in `B`. -/
noncomputable def residueSetPreimageInRange (N q : Nat) (B : Finset Nat) :
    Finset Nat :=
  (Finset.range N).filter fun x => x % q ∈ B

/-- A finite set of residues modulo `q` captures at most
`B.card * (N / q + 1)` elements below `N`. -/
theorem residueSetPreimageInRange_card_le
    {N q : Nat} (B : Finset Nat) :
    (residueSetPreimageInRange N q B).card ≤ B.card * (N / q + 1) := by
  have hsub :
      residueSetPreimageInRange N q B ⊆
        B.biUnion fun r => residueClassInRange N q r := by
    intro x hx
    unfold residueSetPreimageInRange at hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    exact Finset.mem_biUnion.mpr
      ⟨x % q, hx.2, by
        unfold residueClassInRange
        simp [hx.1]⟩
  calc
    (residueSetPreimageInRange N q B).card
        ≤ (B.biUnion fun r => residueClassInRange N q r).card :=
          Finset.card_le_card hsub
    _ ≤ ∑ r ∈ B, (residueClassInRange N q r).card :=
          card_biUnion_le_sum B fun r => residueClassInRange N q r
    _ ≤ B.card * (N / q + 1) :=
          sum_le_card_mul fun r hr => residueClassInRange_card_le (N := N) (q := q) (r := r)

/-- A translated residue class: the offsets `y < N` for which `offset + y`
has residue `r` modulo `q`. -/
noncomputable def shiftedResidueClassInRange (offset N q r : Nat) : Finset Nat :=
  (Finset.range N).filter fun y => (offset + y) % q = r

/-- Translated residue classes obey the same `N / q + 1` count as ordinary
initial-segment residue classes. -/
theorem shiftedResidueClassInRange_card_le {offset N q r : Nat} :
    (shiftedResidueClassInRange offset N q r).card ≤ N / q + 1 := by
  calc
    (shiftedResidueClassInRange offset N q r).card
        ≤ (Finset.range (N / q + 1)).card := by
          apply Finset.card_le_card_of_injOn (fun y => y / q)
          · intro y hy
            have hy' : y ∈ shiftedResidueClassInRange offset N q r := hy
            unfold shiftedResidueClassInRange at hy'
            simp only [Finset.mem_filter, Finset.mem_range] at hy'
            have hydiv : y / q ≤ N / q :=
              Nat.div_le_div_right (Nat.le_of_lt hy'.1)
            simpa [Finset.mem_range] using Nat.lt_succ_of_le hydiv
          · intro a ha b hb hab
            have ha' : a ∈ shiftedResidueClassInRange offset N q r := ha
            have hb' : b ∈ shiftedResidueClassInRange offset N q r := hb
            unfold shiftedResidueClassInRange at ha' hb'
            simp only [Finset.mem_filter, Finset.mem_range] at ha' hb'
            have hmoda : (offset + a) % q = r := ha'.2
            have hmodb : (offset + b) % q = r := hb'.2
            have hshift : offset + a ≡ offset + b [MOD q] := by
              unfold Nat.ModEq
              rw [hmoda, hmodb]
            have hrem : a % q = b % q :=
              Nat.ModEq.add_left_cancel' offset hshift
            have hab' : a / q = b / q := hab
            calc
              a = a % q + q * (a / q) := (Nat.mod_add_div a q).symm
              _ = b % q + q * (b / q) := by rw [hrem, hab']
              _ = b := Nat.mod_add_div b q
    _ = N / q + 1 := by simp

/-- The translated offsets below `N` whose shifted residue modulo `q` lies in
`B`. -/
noncomputable def shiftedResidueSetPreimageInRange
    (offset N q : Nat) (B : Finset Nat) : Finset Nat :=
  (Finset.range N).filter fun y => (offset + y) % q ∈ B

/-- A finite set of shifted residues captures at most
`B.card * (N / q + 1)` offsets below `N`. -/
theorem shiftedResidueSetPreimageInRange_card_le
    {offset N q : Nat} (B : Finset Nat) :
    (shiftedResidueSetPreimageInRange offset N q B).card
      ≤ B.card * (N / q + 1) := by
  have hsub :
      shiftedResidueSetPreimageInRange offset N q B ⊆
        B.biUnion fun r => shiftedResidueClassInRange offset N q r := by
    intro y hy
    unfold shiftedResidueSetPreimageInRange at hy
    simp only [Finset.mem_filter, Finset.mem_range] at hy
    exact Finset.mem_biUnion.mpr
      ⟨(offset + y) % q, hy.2, by
        unfold shiftedResidueClassInRange
        simp [hy.1]⟩
  calc
    (shiftedResidueSetPreimageInRange offset N q B).card
        ≤ (B.biUnion fun r => shiftedResidueClassInRange offset N q r).card :=
          Finset.card_le_card hsub
    _ ≤ ∑ r ∈ B, (shiftedResidueClassInRange offset N q r).card :=
          card_biUnion_le_sum B fun r => shiftedResidueClassInRange offset N q r
    _ ≤ B.card * (N / q + 1) :=
          sum_le_card_mul fun r hr =>
            shiftedResidueClassInRange_card_le (offset := offset) (N := N) (q := q) (r := r)

/-- A scaled translated residue class: the indices `y < N` for which
`offset + scale * y` has residue `r` modulo `q`. -/
noncomputable def scaledShiftedResidueClassInRange
    (offset scale N q r : Nat) : Finset Nat :=
  (Finset.range N).filter fun y => (offset + scale * y) % q = r

/-- If `scale` is invertible modulo `q`, scaled translated residue classes
obey the same `N / q + 1` count. -/
theorem scaledShiftedResidueClassInRange_card_le
    {offset scale N q r : Nat} (hcop : Nat.Coprime scale q) :
    (scaledShiftedResidueClassInRange offset scale N q r).card ≤ N / q + 1 := by
  calc
    (scaledShiftedResidueClassInRange offset scale N q r).card
        ≤ (Finset.range (N / q + 1)).card := by
          apply Finset.card_le_card_of_injOn (fun y => y / q)
          · intro y hy
            have hy' : y ∈ scaledShiftedResidueClassInRange offset scale N q r := hy
            unfold scaledShiftedResidueClassInRange at hy'
            simp only [Finset.mem_filter, Finset.mem_range] at hy'
            have hydiv : y / q ≤ N / q :=
              Nat.div_le_div_right (Nat.le_of_lt hy'.1)
            simpa [Finset.mem_range] using Nat.lt_succ_of_le hydiv
          · intro a ha b hb hab
            have ha' : a ∈ scaledShiftedResidueClassInRange offset scale N q r := ha
            have hb' : b ∈ scaledShiftedResidueClassInRange offset scale N q r := hb
            unfold scaledShiftedResidueClassInRange at ha' hb'
            simp only [Finset.mem_filter, Finset.mem_range] at ha' hb'
            have hmoda : (offset + scale * a) % q = r := ha'.2
            have hmodb : (offset + scale * b) % q = r := hb'.2
            have hshift : offset + scale * a ≡ offset + scale * b [MOD q] := by
              unfold Nat.ModEq
              rw [hmoda, hmodb]
            have hmul : scale * a ≡ scale * b [MOD q] :=
              Nat.ModEq.add_left_cancel' offset hshift
            have hrem : a % q = b % q := by
              have hcancel : a ≡ b [MOD q] := by
                apply Nat.ModEq.cancel_left_of_coprime ?_ hmul
                simpa [Nat.Coprime, Nat.gcd_comm] using hcop
              unfold Nat.ModEq at hcancel
              exact hcancel
            have hab' : a / q = b / q := hab
            calc
              a = a % q + q * (a / q) := (Nat.mod_add_div a q).symm
              _ = b % q + q * (b / q) := by rw [hrem, hab']
              _ = b := Nat.mod_add_div b q
    _ = N / q + 1 := by simp

/-- The indices `y < N` whose scaled translated residue modulo `q` lies in
`B`. -/
noncomputable def scaledShiftedResidueSetPreimageInRange
    (offset scale N q : Nat) (B : Finset Nat) : Finset Nat :=
  (Finset.range N).filter fun y => (offset + scale * y) % q ∈ B

/-- A finite set of scaled shifted residues captures at most
`B.card * (N / q + 1)` indices, provided `scale` is coprime to `q`. -/
theorem scaledShiftedResidueSetPreimageInRange_card_le
    {offset scale N q : Nat} (B : Finset Nat) (hcop : Nat.Coprime scale q) :
    (scaledShiftedResidueSetPreimageInRange offset scale N q B).card
      ≤ B.card * (N / q + 1) := by
  have hsub :
      scaledShiftedResidueSetPreimageInRange offset scale N q B ⊆
        B.biUnion fun r => scaledShiftedResidueClassInRange offset scale N q r := by
    intro y hy
    unfold scaledShiftedResidueSetPreimageInRange at hy
    simp only [Finset.mem_filter, Finset.mem_range] at hy
    exact Finset.mem_biUnion.mpr
      ⟨(offset + scale * y) % q, hy.2, by
        unfold scaledShiftedResidueClassInRange
        simp [hy.1]⟩
  calc
    (scaledShiftedResidueSetPreimageInRange offset scale N q B).card
        ≤ (B.biUnion fun r => scaledShiftedResidueClassInRange offset scale N q r).card :=
          Finset.card_le_card hsub
    _ ≤ ∑ r ∈ B, (scaledShiftedResidueClassInRange offset scale N q r).card :=
          card_biUnion_le_sum B fun r => scaledShiftedResidueClassInRange offset scale N q r
    _ ≤ B.card * (N / q + 1) :=
          sum_le_card_mul fun r hr =>
            scaledShiftedResidueClassInRange_card_le
              (offset := offset) (scale := scale) (N := N) (q := q) (r := r) hcop

/-- The elements in `[lo, hi)` whose residue modulo `q` lies in `B`. -/
noncomputable def residueSetPreimageInIco
    (lo hi q : Nat) (B : Finset Nat) : Finset Nat :=
  (Finset.Ico lo hi).filter fun x => x % q ∈ B

/-- Interval version of the residue-set count, stated for the half-open
interval `[lo, hi)`. -/
theorem residueSetPreimageInIco_card_le
    {lo hi q : Nat} (B : Finset Nat) :
    (residueSetPreimageInIco lo hi q B).card
      ≤ B.card * ((hi - lo) / q + 1) := by
  have hmaps :
      Set.MapsTo (fun x => x - lo)
        (residueSetPreimageInIco lo hi q B)
        (shiftedResidueSetPreimageInRange lo (hi - lo) q B) := by
    intro x hx
    have hx' : x ∈ residueSetPreimageInIco lo hi q B := hx
    unfold residueSetPreimageInIco at hx'
    simp only [Finset.mem_filter, Finset.mem_Ico] at hx'
    change x - lo ∈ shiftedResidueSetPreimageInRange lo (hi - lo) q B
    unfold shiftedResidueSetPreimageInRange
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · omega
    · have hsum : lo + (x - lo) = x := Nat.add_sub_of_le hx'.1.1
      simpa [hsum] using hx'.2
  have hinj :
      Set.InjOn (fun x => x - lo)
        (residueSetPreimageInIco lo hi q B) := by
    intro a ha b hb hab
    have ha' : a ∈ residueSetPreimageInIco lo hi q B := ha
    have hb' : b ∈ residueSetPreimageInIco lo hi q B := hb
    unfold residueSetPreimageInIco at ha' hb'
    simp only [Finset.mem_filter, Finset.mem_Ico] at ha' hb'
    have hab' : a - lo = b - lo := hab
    omega
  calc
    (residueSetPreimageInIco lo hi q B).card
        ≤ (shiftedResidueSetPreimageInRange lo (hi - lo) q B).card :=
          Finset.card_le_card_of_injOn (fun x => x - lo) hmaps hinj
    _ ≤ B.card * ((hi - lo) / q + 1) :=
          shiftedResidueSetPreimageInRange_card_le (offset := lo) (N := hi - lo) (q := q) B

/-- Deterministic interval avoidance for a finite family of residue bad sets.
If the sum of the interval-count estimates is smaller than the interval length,
then some element of `[lo, hi)` avoids every bad residue set. -/
theorem exists_mem_Ico_avoiding_residueSets
    {ι : Type*} [DecidableEq ι] (I : Finset ι)
    {lo hi : Nat} (q : ι → Nat) (B : ι → Finset Nat)
    (hcard :
      ∑ i ∈ I, (B i).card * ((hi - lo) / (q i) + 1) < hi - lo) :
    ∃ x ∈ Finset.Ico lo hi, ∀ i ∈ I, x % q i ∉ B i := by
  let bad : ι → Finset Nat := fun i => residueSetPreimageInIco lo hi (q i) (B i)
  have hsub : ∀ i ∈ I, bad i ⊆ Finset.Ico lo hi := by
    intro i hiI x hx
    have hx' : x ∈ bad i := hx
    unfold bad residueSetPreimageInIco at hx'
    simp only [Finset.mem_filter] at hx'
    exact hx'.1
  have hsum :
      ∑ i ∈ I, (bad i).card
        ≤ ∑ i ∈ I, (B i).card * ((hi - lo) / (q i) + 1) := by
    apply Finset.sum_le_sum
    intro i hiI
    exact residueSetPreimageInIco_card_le (lo := lo) (hi := hi) (q := q i) (B := B i)
  have hsmall : ∑ i ∈ I, (bad i).card < (Finset.Ico lo hi).card := by
    have hsmall' : ∑ i ∈ I, (bad i).card < hi - lo :=
      lt_of_le_of_lt hsum hcard
    simpa [Nat.card_Ico] using hsmall'
  rcases exists_mem_not_mem_biUnion_of_sum_card_lt I (Finset.Ico lo hi) bad hsub hsmall with
    ⟨x, hxIco, havoid⟩
  refine ⟨x, hxIco, ?_⟩
  intro i hiI hxbad
  exact havoid i hiI (by
    change x ∈ residueSetPreimageInIco lo hi (q i) (B i)
    unfold residueSetPreimageInIco
    simp [hxIco, hxbad])

/-- Deterministic avoidance along an arithmetic progression
`offset + scale * t`, for `t < N`. -/
theorem exists_mem_range_avoiding_scaledResidueSets
    {ι : Type*} [DecidableEq ι] (I : Finset ι)
    {offset scale N : Nat} (q : ι → Nat) (B : ι → Finset Nat)
    (hcop : ∀ i ∈ I, Nat.Coprime scale (q i))
    (hcard :
      ∑ i ∈ I, (B i).card * (N / (q i) + 1) < N) :
    ∃ t ∈ Finset.range N,
      ∀ i ∈ I, (offset + scale * t) % q i ∉ B i := by
  let bad : ι → Finset Nat :=
    fun i => scaledShiftedResidueSetPreimageInRange offset scale N (q i) (B i)
  have hsub : ∀ i ∈ I, bad i ⊆ Finset.range N := by
    intro i hiI t ht
    have ht' : t ∈ bad i := ht
    unfold bad scaledShiftedResidueSetPreimageInRange at ht'
    simp only [Finset.mem_filter] at ht'
    exact ht'.1
  have hsum :
      ∑ i ∈ I, (bad i).card
        ≤ ∑ i ∈ I, (B i).card * (N / (q i) + 1) := by
    apply Finset.sum_le_sum
    intro i hiI
    exact scaledShiftedResidueSetPreimageInRange_card_le
      (offset := offset) (scale := scale) (N := N) (q := q i)
      (B := B i) (hcop i hiI)
  have hsmall : ∑ i ∈ I, (bad i).card < (Finset.range N).card := by
    have hsmall' : ∑ i ∈ I, (bad i).card < N :=
      lt_of_le_of_lt hsum hcard
    simpa using hsmall'
  rcases exists_mem_not_mem_biUnion_of_sum_card_lt I (Finset.range N) bad hsub hsmall with
    ⟨t, htRange, havoid⟩
  refine ⟨t, htRange, ?_⟩
  intro i hiI htbad
  exact havoid i hiI (by
    change t ∈ scaledShiftedResidueSetPreimageInRange offset scale N (q i) (B i)
    unfold scaledShiftedResidueSetPreimageInRange
    simp [htRange, htbad])

end Erdos728

end CentralBinomialLean
