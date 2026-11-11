import PMAtoms.CertifiedNumerics
import Mathlib.Tactic

/-!
# Certified rational enclosures of the nuclear ledger

`certifiedMass` is the smooth E8 nuclear ledger in `m_e`: a rational combination
of the six-pillar terms, `π`, the fine-structure `α`, the packing power `A^(2/3)`,
and a `√`. This module proves a **general rational enclosure**

  `cmLo Z N d ≤ certifiedMass Z N ≤ cmHi Z N d`

for *every* table nucleus, at `d` decimal digits — not an enumeration. The `cmLo`/
`cmHi` bounds are computable `ℚ` functions (via `CertifiedNumerics`), so a readout
(e8p) can evaluate *any* `(Z, N)` and cite the theorem for the error bar.

`certifiedMass_c12` is the regression instance checked against the general result.
All bounds are E8 statements; measured masses are the comparison, never inputs.
-/

noncomputable section
open PMAtoms
open PMHadrons.CompositeMasses
open PMElementaryParticles.SharedUnits

namespace PMAtoms

/-! ## The ledger expansion -/

/-- The typed link binding, expanded over the mean-field channel counts. -/
theorem packingBindingTyped_eq (z n : ℕ) (h : 4 < z + n) :
    packingBindingTyped z n =
      packingLinks (z + n) *
        (packingWeight + (5 / 16) * ((n : ℝ) - (z : ℝ)) / ((z + n : ℕ) : ℝ)) := by
  have hA : 1 < z + n := by omega
  have hs : packingChannelAsymmetry = 5 / 16 := packingChannelAsymmetry_eq
  unfold packingBindingTyped bindingFromRealCounts typedChannelWeight packingTypedCounts
  rw [ite_eq_right (by omega : ¬ (z + n ≤ 4))]
  rw [hs]
  push_cast
  have hsum := mixedChannelCounts_sum (packingLinks (z + n)) z n hA
  have hasym := mixedChannelCounts_asymmetry (packingLinks (z + n)) z n hA
  linear_combination packingWeight * hsum + (5 / 16) * hasym

/-- The sphere charge term, expanded with the E8 factor `6/25` and the `√`. -/
theorem chargeTermSphere_eq (z a : ℕ) :
    chargeTermSphere z a =
      (6 / 25) * Real.pi * ((z * (z - 1) : ℕ) : ℝ) /
        Real.sqrt (((a : ℝ) ^ ((2 : ℝ) / 3)) + 1) := by
  unfold chargeTermSphere sphereCoulomb chargeCoupling
  rw [sphereCoulomb_factor, sphereCoulomb_exponent]
  have hD : (D : ℝ) = 4 := by norm_num [D, PMSubstrate.baseline]
  have hs : (σ : ℝ) = 5 := by norm_num [σ, PMSubstrate.baseline]
  rw [hD, hs]
  ring

/-- **Expanded certified ledger** for `Z + N > 4`. -/
theorem certifiedMass_eq (z n : ℕ) (h : 4 < z + n) :
    certifiedMass z n =
      (z : ℝ) * proton + (n : ℝ) * neutron + (z : ℝ)
        - packingLinks (z + n) *
            (packingWeight + (5 / 16) * ((n : ℝ) - (z : ℝ)) / ((z + n : ℕ) : ℝ))
        + (6 / 25) * Real.pi * ((z * (z - 1) : ℕ) : ℝ) /
            Real.sqrt ((((z + n : ℕ) : ℝ) ^ ((2 : ℝ) / 3)) + 1)
        - (5 / 16) * packingClosureRank (z + n)
        - (43 / 4) * alphaCount z n
        + shellCorrectionPaired z n := by
  unfold certifiedMass nuclearMassPackingShellPaired nuclearMassPackingAlpha
    nuclearMassPackingClosure nuclearMassPackingTyped
  rw [packingBindingTyped_eq z n h, chargeTermSphere_eq z (z + n)]
  unfold closureBinding alphaClosureBinding
  rw [closureWeight_eq, alphaClosureWeight_eq]

/-- Certified interval for the `πD·3/5` packing weight. -/
theorem packingWeight_bounds :
    (12 / 5) * 3.1415926535 < packingWeight ∧ packingWeight < (12 / 5) * 3.1415926536 := by
  rw [packingWeight_eq]
  constructor <;> nlinarith [pi_b]

/-! ## Rational branch evaluations -/

/-- `alphaCount` as a computable `ℚ`. -/
def alphaCountQ (z n : ℕ) : ℚ :=
  if 4 ≤ z + n then
    (if isospinGap z n < Δ then
      (min z n : ℚ) / 2 * (1 - (isospinGap z n : ℚ) / (Δ : ℚ)) else 0)
  else 0

/-- `shellCorrectionPaired` as a computable `ℚ`. -/
def shellCorrQ (z n : ℕ) : ℚ :=
  (43 / 6) * (if (z + n) % 2 = 1 then (3 / 4 : ℚ) else 1) *
    (if neutronShell < n then ((n - neutronShell : ℕ) : ℚ) else 0)

theorem alphaCount_eq_Q (z n : ℕ) : alphaCount z n = (alphaCountQ z n : ℝ) := by
  unfold alphaCount alphaCountQ
  by_cases h1 : 4 ≤ z + n
  · simp only [h1, ite_true]
    by_cases h2 : isospinGap z n < Δ
    · simp only [h2, ite_true]; push_cast; ring
    · simp only [h2, ite_false]; norm_num
  · simp only [h1, ite_false]; norm_num

theorem shellCorrectionPaired_eq_Q (z n : ℕ) :
    shellCorrectionPaired z n = (shellCorrQ z n : ℝ) := by
  unfold shellCorrectionPaired shellCorrQ shellPairingFactor neutronExcess
  rw [shellWeight_eq]
  have hD : (D : ℝ) = 4 := by norm_num [D, PMSubstrate.baseline]
  have hD1 : ((D - 1 : ℕ) : ℝ) = 3 := by norm_num [D, PMSubstrate.baseline]
  rw [hD, hD1]
  by_cases h1 : (z + n) % 2 = 1
  · simp only [h1, ite_true]
    by_cases h2 : neutronShell < n
    · simp only [h2, ite_true]; push_cast; ring
    · simp only [h2, ite_false]; norm_num
  · simp only [h1, ite_false]
    by_cases h2 : neutronShell < n
    · simp only [h2, ite_true]; push_cast; ring
    · simp only [h2, ite_false]; norm_num

/-! ## Computable enclosure functions -/

/-- Rational lower endpoint of the certified ledger. -/
def cmLo (z n d : ℕ) : ℚ :=
  let A : ℚ := (z + n : ℕ)
  let c : ℚ := (5 / 16) * ((n : ℚ) - (z : ℚ)) / A
  let abig : ℚ := 3 * A - 3 * rpow23Lo (z + n) d
  let rbig : ℚ := 2 * A - 3 * rpow23Lo (z + n) d + 1
  ((z : ℚ) * (1836152673444 / 10 ^ 9)) + ((n : ℚ) * (18386836620 / 10 ^ 7)) + (z : ℚ)
    - abig * ((12 / 5) * 3.1415926536 + c)
    + ((6 / 25) * ((z * (z - 1) : ℕ) : ℚ) * (314159265358979323846 / 10 ^ 20))
        / sqrtHi (z + n) d
    - (5 / 16) * rbig - (43 / 4) * alphaCountQ z n + shellCorrQ z n

/-- Rational upper endpoint of the certified ledger. -/
def cmHi (z n d : ℕ) : ℚ :=
  let A : ℚ := (z + n : ℕ)
  let c : ℚ := (5 / 16) * ((n : ℚ) - (z : ℚ)) / A
  let asmall : ℚ := 3 * A - 3 * rpow23Hi (z + n) d
  let rsmall : ℚ := 2 * A - 3 * rpow23Hi (z + n) d + 1
  ((z : ℚ) * (1836152673445 / 10 ^ 9)) + ((n : ℚ) * (18386836621 / 10 ^ 7)) + (z : ℚ)
    - asmall * ((12 / 5) * 3.1415926535 + c)
    + ((6 / 25) * ((z * (z - 1) : ℕ) : ℚ) * (314159265358979323847 / 10 ^ 20))
        / sqrtLo (z + n) d
    - (5 / 16) * rsmall - (43 / 4) * alphaCountQ z n + shellCorrQ z n

/-- `a^(2/3) ≤ a` for `a ≥ 1`. -/
theorem rpow23_le_self {a : ℕ} (ha : 1 ≤ a) : (a : ℝ) ^ ((2 : ℝ) / 3) ≤ (a : ℝ) := by
  have h1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  simpa [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le h1 (show (2 : ℝ) / 3 ≤ 1 by norm_num)

/-- **General certified enclosure** of the nuclear ledger at `d` digits. -/
theorem certifiedMass_bounds (z n d : ℕ) (h : 4 < z + n) :
    (cmLo z n d : ℝ) ≤ certifiedMass z n ∧ certifiedMass z n ≤ (cmHi z n d : ℝ) := by
  have hu := rpow23_bounds_auto (z + n) d
  have hsq := sqrt_add_one_bounds_auto (z + n) d
  have hslo_pos : (0 : ℝ) < (sqrtLo (z + n) d : ℝ) := by
    unfold sqrtLo
    push_cast
    apply div_pos
    · have hM : 0 < (cbrt ((z + n) ^ 2 * 10 ^ (3 * d)) + 10 ^ d) * 10 ^ d := by positivity
      have h1 : (1 : ℕ) ≤ Nat.sqrt ((cbrt ((z + n) ^ 2 * 10 ^ (3 * d)) + 10 ^ d) * 10 ^ d) :=
        Nat.le_sqrt'.mpr (by omega)
      have : (1 : ℝ) ≤ (Nat.sqrt ((cbrt ((z + n) ^ 2 * 10 ^ (3 * d)) + 10 ^ d) * 10 ^ d) : ℝ) :=
        by exact_mod_cast h1
      linarith
    · positivity
  have hshi_pos : (0 : ℝ) < (sqrtHi (z + n) d : ℝ) := by
    unfold sqrtHi
    push_cast
    positivity
  have hinv := inv_bounds hsq.1 hsq.2 hslo_pos
  have hp := proton_value
  have hn := neutron_value
  have hpw := packingWeight_bounds
  have hpi := pi_b
  have hpiLo' : (314159265358979323846 / 10 ^ 20 : ℝ) ≤ Real.pi := by
    have hh : (314159265358979323846 / 10 ^ 20 : ℝ) = 3.14159265358979323846 := by norm_num
    linarith [hpi.1]
  have hpiHi' : Real.pi ≤ (314159265358979323847 / 10 ^ 20 : ℝ) := by
    have hh : (314159265358979323847 / 10 ^ 20 : ℝ) = 3.14159265358979323847 := by norm_num
    linarith [hpi.2]
  have hpLo : (1836152673444 / 10 ^ 9 : ℝ) ≤ proton := by
    have hh : (1836152673444 / 10 ^ 9 : ℝ) = 1836.152673444 := by norm_num
    linarith [hp.1]
  have hpHi : proton ≤ (1836152673445 / 10 ^ 9 : ℝ) := by
    have hh : (1836152673445 / 10 ^ 9 : ℝ) = 1836.152673445 := by norm_num
    linarith [hp.2]
  have hnLo : (18386836620 / 10 ^ 7 : ℝ) ≤ neutron := by
    have hh : (18386836620 / 10 ^ 7 : ℝ) = 1838.6836620 := by norm_num
    linarith [hn.1]
  have hnHi : neutron ≤ (18386836621 / 10 ^ 7 : ℝ) := by
    have hh : (18386836621 / 10 ^ 7 : ℝ) = 1838.6836621 := by norm_num
    linarith [hn.2]
  have huA : ((z + n : ℕ) : ℝ) ^ ((2 : ℝ) / 3) ≤ ((z + n : ℕ) : ℝ) := rpow23_le_self (by omega)
  have hfrac : -1 ≤ ((n : ℝ) - (z : ℝ)) / ((z : ℝ) + (n : ℝ)) ∧
      ((n : ℝ) - (z : ℝ)) / ((z : ℝ) + (n : ℝ)) ≤ 1 := by
    have hden : (0 : ℝ) < (z : ℝ) + (n : ℝ) := by
      rw [← Nat.cast_add]; exact_mod_cast (by omega : 0 < z + n)
    constructor
    · rw [le_div_iff₀ hden]; linarith
    · rw [div_le_one hden]; linarith
  have hk0 : (0 : ℝ) ≤ (6 / 25) * ((z : ℝ) * ((z - 1 : ℕ) : ℝ)) := by positivity
  rw [certifiedMass_eq z n h, alphaCount_eq_Q, shellCorrectionPaired_eq_Q,
    show packingLinks (z + n) = 3 * ((z + n : ℕ) : ℝ) - 3 * (((z + n : ℕ) : ℝ)) ^ ((2 : ℝ) / 3) by rfl,
    show packingClosureRank (z + n) = 2 * ((z + n : ℕ) : ℝ) - 3 * (((z + n : ℕ) : ℝ)) ^ ((2 : ℝ) / 3) + 1 by rfl]
  unfold cmLo cmHi
  push_cast at hu hsq huA ⊢
  have hc0 : 0 ≤ packingWeight + (5 / 16) * ((n : ℝ) - (z : ℝ)) / ((z : ℝ) + (n : ℝ)) := by
    rw [mul_div_assoc]; linarith [hpw.1, hfrac.1]
  have hpwc0 : 0 ≤ (12 / 5) * 3.1415926536 + (5 / 16) * ((n : ℝ) - (z : ℝ)) / ((z : ℝ) + (n : ℝ)) := by
    rw [mul_div_assoc]; linarith [hfrac.1]
  have hpwc1 : 0 ≤ (12 / 5) * 3.1415926535 + (5 / 16) * ((n : ℝ) - (z : ℝ)) / ((z : ℝ) + (n : ℝ)) := by
    rw [mul_div_assoc]; linarith [hfrac.1]
  constructor
  · have hmulz : (z : ℝ) * (1836152673444 / 10 ^ 9) ≤ (z : ℝ) * proton :=
      mul_le_mul_of_nonneg_left hpLo (by exact_mod_cast Nat.zero_le z)
    have hmuln : (n : ℝ) * (18386836620 / 10 ^ 7) ≤ (n : ℝ) * neutron :=
      mul_le_mul_of_nonneg_left hnLo (by exact_mod_cast Nat.zero_le n)
    have hpb : (3 * ((z : ℝ) + (n : ℝ)) - 3 * (((z : ℝ) + (n : ℝ))) ^ ((2 : ℝ) / 3)) *
          (packingWeight + (5 / 16) * ((n : ℝ) - (z : ℝ)) / ((z : ℝ) + (n : ℝ))) ≤
        (3 * ((z : ℝ) + (n : ℝ)) - 3 * (rpow23Lo (z + n) d : ℝ)) *
          ((12 / 5) * 3.1415926536 + (5 / 16) * ((n : ℝ) - (z : ℝ)) / ((z : ℝ) + (n : ℝ))) :=
      mul_le_mul (by linarith [hu.1]) (by linarith [hpw.2]) hc0 (by linarith [hu.1, huA])
    have hcore : (314159265358979323846 / 10 ^ 20 : ℝ) / (sqrtHi (z + n) d : ℝ) ≤
        Real.pi / Real.sqrt (((z : ℝ) + (n : ℝ)) ^ ((2 : ℝ) / 3) + 1) := by
      simpa [div_eq_mul_inv] using
        (mul_le_mul hpiLo' hinv.1 (le_of_lt (one_div_pos.mpr hshi_pos)) (by linarith [hpi.1]))
    have hch : (6 / 25) * ((z : ℝ) * ((z - 1 : ℕ) : ℝ)) * (314159265358979323846 / 10 ^ 20) /
          (sqrtHi (z + n) d : ℝ) ≤
        (6 / 25) * Real.pi * ((z : ℝ) * ((z - 1 : ℕ) : ℝ)) /
          Real.sqrt (((z : ℝ) + (n : ℝ)) ^ ((2 : ℝ) / 3) + 1) := by
      calc (6 / 25) * ((z : ℝ) * ((z - 1 : ℕ) : ℝ)) * (314159265358979323846 / 10 ^ 20) /
              (sqrtHi (z + n) d : ℝ)
          = ((6 / 25) * ((z : ℝ) * ((z - 1 : ℕ) : ℝ))) *
              ((314159265358979323846 / 10 ^ 20) / (sqrtHi (z + n) d : ℝ)) := by ring
        _ ≤ ((6 / 25) * ((z : ℝ) * ((z - 1 : ℕ) : ℝ))) *
              (Real.pi / Real.sqrt (((z : ℝ) + (n : ℝ)) ^ ((2 : ℝ) / 3) + 1)) :=
              mul_le_mul_of_nonneg_left hcore hk0
        _ = (6 / 25) * Real.pi * ((z : ℝ) * ((z - 1 : ℕ) : ℝ)) /
              Real.sqrt (((z : ℝ) + (n : ℝ)) ^ ((2 : ℝ) / 3) + 1) := by ring
    linarith [hmulz, hmuln, hpb, hch, hu.1]
  · have hmulz : (z : ℝ) * proton ≤ (z : ℝ) * (1836152673445 / 10 ^ 9) :=
      mul_le_mul_of_nonneg_left hpHi (by exact_mod_cast Nat.zero_le z)
    have hmuln : (n : ℝ) * neutron ≤ (n : ℝ) * (18386836621 / 10 ^ 7) :=
      mul_le_mul_of_nonneg_left hnHi (by exact_mod_cast Nat.zero_le n)
    have hpb : (3 * ((z : ℝ) + (n : ℝ)) - 3 * (rpow23Hi (z + n) d : ℝ)) *
          ((12 / 5) * 3.1415926535 + (5 / 16) * ((n : ℝ) - (z : ℝ)) / ((z : ℝ) + (n : ℝ))) ≤
        (3 * ((z : ℝ) + (n : ℝ)) - 3 * (((z : ℝ) + (n : ℝ))) ^ ((2 : ℝ) / 3)) *
          (packingWeight + (5 / 16) * ((n : ℝ) - (z : ℝ)) / ((z : ℝ) + (n : ℝ))) :=
      mul_le_mul (by linarith [hu.2]) (by linarith [hpw.1]) hpwc1 (by linarith [huA])
    have hcore : Real.pi / Real.sqrt (((z : ℝ) + (n : ℝ)) ^ ((2 : ℝ) / 3) + 1) ≤
        (314159265358979323847 / 10 ^ 20 : ℝ) / (sqrtLo (z + n) d : ℝ) := by
      simpa [div_eq_mul_inv] using
        (mul_le_mul hpiHi' hinv.2 (by positivity) (by linarith [hpi.2]))
    have hch : (6 / 25) * Real.pi * ((z : ℝ) * ((z - 1 : ℕ) : ℝ)) /
          Real.sqrt (((z : ℝ) + (n : ℝ)) ^ ((2 : ℝ) / 3) + 1) ≤
        (6 / 25) * ((z : ℝ) * ((z - 1 : ℕ) : ℝ)) * (314159265358979323847 / 10 ^ 20) /
          (sqrtLo (z + n) d : ℝ) := by
      calc (6 / 25) * Real.pi * ((z : ℝ) * ((z - 1 : ℕ) : ℝ)) /
              Real.sqrt (((z : ℝ) + (n : ℝ)) ^ ((2 : ℝ) / 3) + 1)
          = ((6 / 25) * ((z : ℝ) * ((z - 1 : ℕ) : ℝ))) *
              (Real.pi / Real.sqrt (((z : ℝ) + (n : ℝ)) ^ ((2 : ℝ) / 3) + 1)) := by ring
        _ ≤ ((6 / 25) * ((z : ℝ) * ((z - 1 : ℕ) : ℝ))) *
              ((314159265358979323847 / 10 ^ 20) / (sqrtLo (z + n) d : ℝ)) :=
              mul_le_mul_of_nonneg_left hcore hk0
        _ = (6 / 25) * ((z : ℝ) * ((z - 1 : ℕ) : ℝ)) * (314159265358979323847 / 10 ^ 20) /
              (sqrtLo (z + n) d : ℝ) := by ring
    linarith [hmulz, hmuln, hpb, hch, huA]

/-- **Regression instance**: C-12 (`Z = N = 6`), a fully worked interval proof
of the same ledger the general `certifiedMass_bounds` bounds. -/
theorem certifiedMass_c12 :
    (21875.0 : ℝ) < certifiedMass 6 6 ∧ certifiedMass 6 6 < (21877.0 : ℝ) := by
  rw [certifiedMass_eq 6 6 (by norm_num : 4 < 6 + 6)]
  rw [show alphaCount 6 6 = 3 by
        norm_num [alphaCount, isospinGap, Δ, PMSubstrate.baseline]]
  rw [show shellCorrectionPaired 6 6 = 0 by
        unfold shellCorrectionPaired shellPairingFactor neutronExcess neutronShell
        norm_num [shellWeight, D, χ, Δ, PMSubstrate.baseline]]
  rw [show packingLinks 12 = 36 - 3 * (12 : ℝ) ^ ((2 : ℝ) / 3) by
        unfold packingLinks; ring_nf]
  rw [show packingClosureRank 12 = 25 - 3 * (12 : ℝ) ^ ((2 : ℝ) / 3) by
        unfold packingClosureRank; ring_nf]
  norm_num
  have hu := rpow23_bounds (a := 12) (lo := 5.24148) (hi := 5.24149)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs := sqrt_add_one_bounds (u := (12 : ℝ) ^ ((2 : ℝ) / 3))
    (sl := 2.49829) (sh := 2.4983) (by norm_num) (by norm_num)
    (by nlinarith [hu.1]) (by nlinarith [hu.2])
  have hs_pos : 0 < Real.sqrt ((12 : ℝ) ^ ((2 : ℝ) / 3) + 1) :=
    lt_of_lt_of_le (by norm_num) hs.1
  have hsinv : (1 : ℝ) / 2.4983 ≤ 1 / Real.sqrt ((12 : ℝ) ^ ((2 : ℝ) / 3) + 1) ∧
      1 / Real.sqrt ((12 : ℝ) ^ ((2 : ℝ) / 3) + 1) ≤ 1 / 2.49829 :=
    ⟨one_div_le_one_div_of_le hs_pos hs.2, one_div_le_one_div_of_le (by norm_num) hs.1⟩
  have hpw := packingWeight_bounds
  have hpi := pi_b
  have hp := proton_value
  have hn := neutron_value
  have hA : (20.27553 : ℝ) ≤ 36 - 3 * (12 : ℝ) ^ ((2 : ℝ) / 3) ∧
      36 - 3 * (12 : ℝ) ^ ((2 : ℝ) / 3) ≤ 20.27556 := by
    constructor <;> nlinarith [hu.1, hu.2]
  have hApw : (152.87 : ℝ) ≤
        (36 - 3 * (12 : ℝ) ^ ((2 : ℝ) / 3)) * packingWeight ∧
      (36 - 3 * (12 : ℝ) ^ ((2 : ℝ) / 3)) * packingWeight ≤ 152.88 := by
    constructor <;> nlinarith [hA.1, hA.2, hpw.1, hpw.2]
  have hR : (9.27 : ℝ) ≤ 25 - 3 * (12 : ℝ) ^ ((2 : ℝ) / 3) ∧
      25 - 3 * (12 : ℝ) ^ ((2 : ℝ) / 3) ≤ 9.28 := by
    constructor <;> nlinarith [hu.1, hu.2]
  have hcharge : (9.05 : ℝ) ≤
        (36 / 5) * Real.pi * (1 / Real.sqrt ((12 : ℝ) ^ ((2 : ℝ) / 3) + 1)) ∧
      (36 / 5) * Real.pi * (1 / Real.sqrt ((12 : ℝ) ^ ((2 : ℝ) / 3) + 1)) ≤ 9.06 := by
    have hl := mul_le_mul hpi.1.le hsinv.1 (by norm_num : (0 : ℝ) ≤ 1 / 2.4983)
      (by linarith [hpi.1])
    have hu2 := mul_le_mul hpi.2.le hsinv.2 (by positivity)
      (by norm_num : (0 : ℝ) ≤ 3.14159265358979323847)
    constructor <;> nlinarith [hl, hu2]
  rw [show (6 / 25) * Real.pi * 30 / Real.sqrt ((12 : ℝ) ^ ((2 : ℝ) / 3) + 1)
        = (36 / 5) * Real.pi * (1 / Real.sqrt ((12 : ℝ) ^ ((2 : ℝ) / 3) + 1)) by ring]
  constructor <;>
    linarith [hp.1, hp.2, hn.1, hn.2, hu.1, hu.2, hApw.1, hApw.2, hR.1, hR.2,
      hcharge.1, hcharge.2]

end PMAtoms
