import PMAtoms.NuclearLedger
import Mathlib.Tactic

/-!
# Certified rational enclosures of the nuclear ledger

`certifiedMass` is the smooth E8 nuclear ledger in `m_e`: a rational combination
of the six-pillar terms, `π`, the fine-structure `α`, the packing power `A^(2/3)`,
and a `√`.  This module proves a **rational enclosure** of `certifiedMass` — a
certified error bar usable by downstream readouts (e8p), where the ledger was
previously only an unevaluated `π`/`√` expression.

The enclosure is assembled from proved primitive intervals (`proton_value`,
`neutron_value`, `pi_b`, `packingWeight_bounds`) plus per-nucleus bounds on
`A^(2/3)` and `√(A^(2/3)+1)` from exact cube/square arithmetic
(`rpow23_bounds`, `sqrt_add_one_bounds`).  `certifiedMass_c12` is the first
fully proved instance; the remaining table nuclei follow the same template.

All bounds are E8 statements; measured masses are the comparison, never inputs.
-/

noncomputable section
open PMAtoms
open PMHadrons.CompositeMasses
open PMElementaryParticles.SharedUnits

namespace PMAtoms

/-- Rational bounds on `a^(2/3)` from cube bounds on `a^2`. -/
lemma rpow23_bounds {a : ℕ} {lo hi : ℝ}
    (hlo0 : 0 ≤ lo) (hhi0 : 0 ≤ hi)
    (hlo : lo ^ 3 ≤ (a : ℝ) ^ 2) (hhi : (a : ℝ) ^ 2 ≤ hi ^ 3) :
    lo ≤ (a : ℝ) ^ ((2 : ℝ) / 3) ∧ (a : ℝ) ^ ((2 : ℝ) / 3) ≤ hi := by
  have ha : 0 ≤ (a : ℝ) := by positivity
  have hrt : (a : ℝ) ^ ((2 : ℝ) / 3) = ((a : ℝ) ^ (2 : ℝ)) ^ ((3 : ℕ)⁻¹ : ℝ) := by
    rw [show ((2 : ℝ) / 3) = 2 * ((3 : ℕ)⁻¹ : ℝ) by norm_num, Real.rpow_mul ha]
  have hbase : (a : ℝ) ^ (2 : ℝ) = (a : ℝ) ^ 2 := Real.rpow_natCast (a : ℝ) 2
  constructor
  · rw [hrt, hbase, ← Real.pow_rpow_inv_natCast hlo0 (by norm_num : (3 : ℕ) ≠ 0)]
    exact Real.rpow_le_rpow (by positivity) hlo (by norm_num)
  · rw [hrt, hbase, ← Real.pow_rpow_inv_natCast hhi0 (by norm_num : (3 : ℕ) ≠ 0)]
    exact Real.rpow_le_rpow (by positivity) hhi (by norm_num)

/-- `√(u+1)` bounds from rational bounds on `u+1`. -/
lemma sqrt_add_one_bounds {u sl sh : ℝ} (hsl : 0 ≤ sl) (hsh : 0 ≤ sh)
    (h1 : sl ^ 2 ≤ u + 1) (h2 : u + 1 ≤ sh ^ 2) :
    sl ≤ Real.sqrt (u + 1) ∧ Real.sqrt (u + 1) ≤ sh := by
  have hy : 0 ≤ u + 1 := le_trans (sq_nonneg sl) h1
  exact ⟨(Real.le_sqrt hsl hy).mpr h1, Real.sqrt_le_iff.mpr ⟨hsh, h2⟩⟩

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

/-- **Expanded certified ledger** for `Z + N > 4`: the free-nucleon sum minus the
link term (`packingLinks · (πD·3/5 ± σ/16)`), the closure term, the alpha closure,
the heavy-shell correction, and the sphere charge term. -/
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

/-- Certified interval for the `πD·3/5` packing weight, from `pi_b`. -/
theorem packingWeight_bounds :
    (12 / 5) * 3.1415926535 < packingWeight ∧ packingWeight < (12 / 5) * 3.1415926536 := by
  rw [packingWeight_eq]
  constructor <;> nlinarith [pi_b]

/-- **Certified enclosure of C-12 (`Z = N = 6`, `A = 12`)** in `m_e`.

Free nucleons `6p + 6n + 6` minus the link term `packingLinks(12)·πD·3/5`, plus
the sphere charge `(6/25)π·30/√(12^(2/3)+1)`, minus the closure `(5/16)R(12)`,
minus the alpha closure `(43/4)·3`; the heavy-shell correction vanishes.  Each
irrational piece is enclosed with a proved rational error bar. -/
theorem certifiedMass_c12 :
    (21875.0 : ℝ) < certifiedMass 6 6 ∧ certifiedMass 6 6 < (21877.0 : ℝ) := by
  rw [certifiedMass_eq 6 6 (by norm_num : 4 < 6 + 6)]
  rw [show alphaCount 6 6 = 3 by
        norm_num [alphaCount, isospinGap, Δ, PMSubstrate.baseline]]
  rw [show shellCorrectionPaired 6 6 = 0 by
        unfold shellCorrectionPaired shellPairingFactor neutronExcess neutronShell
        norm_num [shellWeight, D, χ, Δ, PMSubstrate.baseline]]
  rw [show packingLinks 12 = 36 - 3 * (12 : ℝ) ^ ((2 : ℝ) / 3) by
        unfold packingLinks; ring]
  rw [show packingClosureRank 12 = 25 - 3 * (12 : ℝ) ^ ((2 : ℝ) / 3) by
        unfold packingClosureRank; ring]
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
