import E8PConstants.Experimental
import PMConstants.ReferenceDirections
import PMConstants.RegulatoryMaximin
import PMConstants.RegulatoryLabels
import PMConstants.RepairBudget
import PMConstants.CoherentBudget
import PMConstants.GaugeWalkBudget
import PMConstants.TangentResponse
import PMConstants.BudgetReadout
import PMConstants.WalkTrials
import PMConstants.InterfaceCorrection
import PMConstants.StableReadout
import PMConstants.StrongLedgerBounds
import PMConstants.ResourceLedger
import PMConstants.ContentWeight

/-!
# Gauge and scalar comparisons using measured inputs

The response functions and E8 enclosures are in PMConstants.
This module applies the measured reference values and the comparison windows.
-/

open E8PConstants

noncomputable section

namespace PMConstants.ElectroweakBounds
open ElectroweakE8 CertifiedConstants JointConstants GaugeSpectrum

/-- The measured Z anchor used by the current W calculator is not the Z
mass of the paper's uncorrected quadratic-response formulas. -/
theorem z_anchor_not_derived : Real.sqrt (zMassSquared PMSubstrate.causalCoupling electronGeV) ≠ GaugeReferences.zMassGeV := by
  have h := z_mass_bounds.2
  intro he; rw [he] at h; norm_num at h

end PMConstants.ElectroweakBounds

namespace PMConstants.ScaleConsistency
open ElectroweakE8 CertifiedConstants JointConstants GaugeSpectrum ElectroweakBounds

theorem z_needs_factor {k : ℝ} (hk : 0 < k) (h : k * zMassSquared PMSubstrate.causalCoupling electronGeV = GaugeReferences.zMassGeV^2) :
    1.0362 < k ∧ k < 1.0365 := by
  have hz := z_squared_bounds
  unfold GaugeReferences.zMassGeV at h
  constructor <;> nlinarith [hz.1, hz.2]

theorem same_scale_obstruction {k : ℝ} (hk : 0 < k)
    (h : k * zMassSquared PMSubstrate.causalCoupling electronGeV = GaugeReferences.zMassGeV^2) :
    GaugeReferences.strongWindowHi < k * strongCoupling PMSubstrate.causalCoupling := by
  have hk' := z_needs_factor hk h
  have hs := strong_bounds
  unfold GaugeReferences.strongWindowHi
  nlinarith [hk'.1, hs.1]

theorem anchored_w :
    (80.3845 : ℝ) < GaugeReferences.zMassGeV * Real.sqrt (1 - clockRatio) ∧
      GaugeReferences.zMassGeV * Real.sqrt (1 - clockRatio) < 80.3846 := by
  have hw := weak_bounds
  have h0 : 0 ≤ 1 - clockRatio := by linarith [hw.2]
  have hsq := Real.sq_sqrt h0
  have hnn := Real.sqrt_nonneg (1 - clockRatio)
  unfold GaugeReferences.zMassGeV
  constructor <;> nlinarith [hw.1, hw.2]

end PMConstants.ScaleConsistency

namespace PMConstants.ScaleResponse
open PMConstants ElectroweakE8 CertifiedConstants

theorem zpole_screening_overshoots {dα : ℝ} (h : GaugeReferences.screeningLo < dα ∧ dα < GaugeReferences.screeningHi) :
    1.07 < zpoleFactor dα := by
  simp only [GaugeReferences.screeningLo, GaugeReferences.screeningHi] at h
  have ha := inv_alpha_bounds
  rw [one_div] at ha
  have hz : 0 < zpoleInverse dα := by
    unfold zpoleInverse; norm_num [overhead]; nlinarith [ha.1, h.2]
  unfold zpoleFactor
  rw [lt_div_iff₀ hz]
  unfold zpoleInverse; norm_num [overhead]
  nlinarith [ha.1, ha.2, h.1, h.2]

theorem zpole_not_interface {dα k : ℝ} (h : GaugeReferences.screeningLo < dα ∧ dα < GaugeReferences.screeningHi) (hk : 0 < k)
    (hz : k * GaugeSpectrum.zMassSquared PMSubstrate.causalCoupling ElectroweakBounds.electronGeV =
      GaugeReferences.zMassGeV^2) : k ≠ zpoleFactor dα := by
  have h1 := (ScaleConsistency.z_needs_factor hk hz).2
  have h2 := zpole_screening_overshoots h
  intro he; rw [he] at h1; linarith

theorem antiscreening_required {dα k X : ℝ} (h : GaugeReferences.screeningLo < dα ∧ dα < GaugeReferences.screeningHi) (hk : 0 < k)
    (hz : k * GaugeSpectrum.zMassSquared PMSubstrate.causalCoupling ElectroweakBounds.electronGeV =
      GaugeReferences.zMassGeV^2)
    (hdec : 1/k = 1 - dα + X) : 0.0236 < X ∧ X < 0.0242 := by
  simp only [GaugeReferences.screeningLo, GaugeReferences.screeningHi] at h
  have hb := ScaleConsistency.z_needs_factor hk hz
  have hk0 : 0 < k := hk
  have hX : X = 1/k - 1 + dα := by linarith
  have hlo : 1/1.0365 < 1/k := one_div_lt_one_div_of_lt hk0 hb.2
  have hhi : 1/k < 1/1.0362 := one_div_lt_one_div_of_lt (by norm_num) hb.1
  rw [hX]
  constructor
  · norm_num at hlo ⊢; linarith [h.1]
  · norm_num at hhi ⊢; linarith [h.2]

end PMConstants.ScaleResponse

namespace PMConstants.StrongLedgerBounds
open PMConstants CertifiedConstants ElectroweakE8 GaugeSpectrum ElectroweakBounds ColourChannels

theorem ledger_interface_obstruction {k : ℝ} (hk : 0 < k)
    (h : k * zMassSquared PMSubstrate.causalCoupling electronGeV = GaugeReferences.zMassGeV^2) :
    (0.1222 : ℝ) < k * ledgerStrong := by
  have hk' := ScaleConsistency.z_needs_factor hk h
  have hs := strong_from_channels
  unfold ledgerStrong
  nlinarith [hk'.1, hs.1]

end PMConstants.StrongLedgerBounds

namespace PMConstants.LinkCustodial
open PMConstants ElectroweakE8 CertifiedConstants JointConstants GaugeSpectrum ElectroweakBounds

theorem delta_r_window {k : ℝ} (hk : 0 < k)
    (hz : k * zMassSquared PMSubstrate.causalCoupling electronGeV = GaugeReferences.zMassGeV^2) :
    0.0349 < 1 - 1/k ∧ 1 - 1/k < 0.0353 := by
  have hb := ScaleConsistency.z_needs_factor hk hz
  have hlo : 1/1.0365 < 1/k := one_div_lt_one_div_of_lt hk hb.2
  have hhi : 1/k < 1/1.0362 := one_div_lt_one_div_of_lt (by norm_num) hb.1
  norm_num at hlo hhi ⊢
  constructor <;> linarith

theorem leading_bounds {mt : ℝ} (h : GaugeReferences.topLoGeV < mt ∧ mt < GaugeReferences.topHiGeV) :
    0.0324 < leadingTerm clockRatio (fermi PMSubstrate.causalCoupling electronGeV) mt ∧
      leadingTerm clockRatio (fermi PMSubstrate.causalCoupling electronGeV) mt < 0.0327 := by
  simp only [GaugeReferences.topLoGeV, GaugeReferences.topHiGeV] at h
  have hs : (1 - clockRatio)/clockRatio = 6446/1849 := by
    norm_num [clockRatio, footprint, overhead]
  have hg := fermi_bounds
  have hs2 := sqrt_two_bounds
  have hpi := pi_bounds
  have hp2lo : (9.8696044 : ℝ) < Real.pi^2 := by nlinarith [hpi.1]
  have hp2hi : Real.pi^2 < (9.8696045 : ℝ) := by nlinarith [hpi.1, hpi.2]
  have hDlo' := mul_lt_mul'' hs2.1 hp2lo (by norm_num) (by norm_num)
  have hDhi' := mul_lt_mul'' hs2.2 hp2hi (Real.sqrt_nonneg 2) (by positivity)
  have hD : 8 * Real.sqrt 2 * Real.pi^2 = 8 * (Real.sqrt 2 * Real.pi^2) := by ring
  have hDlo : (111.66 : ℝ) < 8 * Real.sqrt 2 * Real.pi^2 := by rw [hD]; linarith
  have hDhi : 8 * Real.sqrt 2 * Real.pi^2 < (111.67 : ℝ) := by rw [hD]; linarith
  have hm2lo : (29680.39 : ℝ) < mt^2 := by nlinarith [h.1]
  have hm2hi : mt^2 < (29880.59 : ℝ) := by nlinarith [h.1, h.2]
  have hNlo' := mul_lt_mul'' hg.1 hm2lo (by norm_num) (by norm_num)
  have hNhi' := mul_lt_mul'' hg.2 hm2hi (by linarith [hg.1]) (by positivity)
  have hDpos : 0 < 8 * Real.sqrt 2 * Real.pi^2 := by linarith
  unfold leadingTerm
  rw [hs]
  constructor
  · rw [lt_div_iff₀ hDpos]; nlinarith
  · rw [div_lt_iff₀ hDpos]; nlinarith

/-- The leading splitting term overshoots the required opposite-sign term; the non-leading
remainder must lie in `(0.0082, 0.0091)`. -/
theorem remainder_required {dα k X mt R : ℝ} (h : GaugeReferences.screeningLo < dα ∧ dα < GaugeReferences.screeningHi) (hk : 0 < k)
    (hz : k * zMassSquared PMSubstrate.causalCoupling electronGeV = GaugeReferences.zMassGeV^2)
    (hdec : 1/k = 1 - dα + X) (hmt : GaugeReferences.topLoGeV < mt ∧ mt < GaugeReferences.topHiGeV)
    (hX : X = leadingTerm clockRatio (fermi PMSubstrate.causalCoupling electronGeV) mt - R) :
    0.0082 < R ∧ R < 0.0091 := by
  have hx := ScaleResponse.antiscreening_required h hk hz hdec
  have hl := leading_bounds hmt
  constructor <;> linarith [hx.1, hx.2, hl.1, hl.2]

end PMConstants.LinkCustodial

namespace PMConstants.InterfaceCorrection
open PMConstants ElectroweakE8 CertifiedConstants GaugeSpectrum ElectroweakBounds

/-- The Z-anchor requirement fixes `Δr` to the on-shell window. -/
theorem deltaR_window {k : ℝ} (hk : 0 < k)
    (hz : k * zMassSquared PMSubstrate.causalCoupling electronGeV = GaugeReferences.zMassGeV ^ 2) :
    0.0349 < deltaR k ∧ deltaR k < 0.0353 := by
  simpa [deltaR] using LinkCustodial.delta_r_window hk hz

/-- With the leading top-splitting term, the non-leading remainder is bounded. -/
theorem deltaR_remainder {dα k X mt R : ℝ}
    (h : GaugeReferences.screeningLo < dα ∧ dα < GaugeReferences.screeningHi) (hk : 0 < k)
    (hz : k * zMassSquared PMSubstrate.causalCoupling electronGeV = GaugeReferences.zMassGeV ^ 2)
    (hdec : 1 / k = 1 - dα + X) (hmt : GaugeReferences.topLoGeV < mt ∧ mt < GaugeReferences.topHiGeV)
    (hX : X = LinkCustodial.leadingTerm clockRatio (fermi PMSubstrate.causalCoupling electronGeV) mt - R) :
    0.0082 < R ∧ R < 0.0091 :=
  LinkCustodial.remainder_required h hk hz hdec hmt hX

end PMConstants.InterfaceCorrection

namespace PMConstants.ReadoutScales
open PMConstants Matrix GeneratorNormalization PacketTraceForm ReferenceAnchor ReferenceStabilizer

theorem at_Z {A : ℝ} (hA : 0.11799 < A ∧ A < 0.11800) :
    implied GaugeReferences.zMassGeV A GaugeReferences.zMassGeV = A ∧ |(A - GaugeReferences.strongComparison) / GaugeReferences.strongSigma| < 0.012 := by
  have hA0 : 0 < A := by linarith
  refine ⟨by simp [implied], ?_⟩
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

theorem at_W {A : ℝ} (hA : 0.11799 < A ∧ A < 0.11800) : implied GaugeReferences.zMassGeV A GaugeReferences.wMassGeV < 0.1162 := by
  have hA0 : 0 < A := by linarith
  have hL : Real.log (GaugeReferences.wMassGeV / GaugeReferences.zMassGeV) ≤ GaugeReferences.wMassGeV / GaugeReferences.zMassGeV - 1 :=
    Real.log_le_sub_one_of_pos (by norm_num)
  have hb := b_bounds
  have hinv : 1 / 0.118 < 1 / A := one_div_lt_one_div_of_lt hA0 (by linarith [hA.2] : A < 0.118)
  have hD : 8.61 < 1 / A - 23 / (6 * Real.pi) * Real.log (GaugeReferences.wMassGeV / GaugeReferences.zMassGeV) := by
    have hneg : 0.1186 ≤ -Real.log (GaugeReferences.wMassGeV / GaugeReferences.zMassGeV) := by
      have : (GaugeReferences.wMassGeV : ℝ) / GaugeReferences.zMassGeV - 1 ≤ -0.1186 := by norm_num
      linarith
    have : (23 / (6 * 3.15)) * 0.1186 ≤ 23 / (6 * Real.pi) * -Real.log (GaugeReferences.wMassGeV / GaugeReferences.zMassGeV) :=
      mul_le_mul hb.1.le hneg (by norm_num) (by linarith)
    have h1 : (8.47 : ℝ) < 1 / 0.118 := by norm_num
    have h2 : (8.47 : ℝ) + 23 / (6 * 3.15) * 0.1186 > 8.61 := by norm_num
    nlinarith
  unfold implied
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

lemma above_bound {A μ L0 c : ℝ} (hA : 0.11799 < A ∧ A < 0.11800) (hμ : 0 < μ)
    (hL : L0 ≤ Real.log (μ / GaugeReferences.zMassGeV)) (hL0 : 0 ≤ L0)
    (hc : 1 / 0.11799 - 23 / (6 * 3.15) * L0 < c)
    (hU : 23 / (6 * 3.14) * (μ / GaugeReferences.zMassGeV - 1) < 1 / 0.118) :
    1 / c < implied GaugeReferences.zMassGeV A μ := by
  have hA0 : 0 < A := by linarith
  have hb := b_bounds
  have hinv : 1 / A < 1 / 0.11799 := one_div_lt_one_div_of_lt (by norm_num) hA.1
  have hprod : 23 / (6 * 3.15) * L0 ≤ 23 / (6 * Real.pi) * Real.log (μ / GaugeReferences.zMassGeV) :=
    mul_le_mul hb.1.le hL hL0 (by linarith)
  have hD : 1 / A - 23 / (6 * Real.pi) * Real.log (μ / GaugeReferences.zMassGeV) < c := by linarith
  have hDpos : 0 < 1 / A - 23 / (6 * Real.pi) * Real.log (μ / GaugeReferences.zMassGeV) ∨
      1 / A - 23 / (6 * Real.pi) * Real.log (μ / GaugeReferences.zMassGeV) ≤ 0 := lt_or_ge _ _
  rcases hDpos with hp | hn
  · unfold implied; exact one_div_lt_one_div_of_lt hp hD
  · exfalso
    have hl : Real.log (μ / GaugeReferences.zMassGeV) ≤ μ / GaugeReferences.zMassGeV - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have hinv2 : 1 / 0.118 < 1 / A := one_div_lt_one_div_of_lt hA0 (by linarith [hA.2] : A < 0.118)
    have hlpos : 0 ≤ Real.log (μ / GaugeReferences.zMassGeV) := hL0.trans hL
    have : 23 / (6 * Real.pi) * Real.log (μ / GaugeReferences.zMassGeV) ≤ 23 / (6 * 3.14) * (μ / GaugeReferences.zMassGeV - 1) :=
      mul_le_mul hb.2.le hl hlpos (by norm_num)
    linarith

theorem at_H {A : ℝ} (hA : 0.11799 < A ∧ A < 0.11800) : 0.1227 < implied GaugeReferences.zMassGeV A GaugeReferences.higgsMassGeV := by
  have hL : 1 - (GaugeReferences.higgsMassGeV / GaugeReferences.zMassGeV)⁻¹ ≤ Real.log (GaugeReferences.higgsMassGeV / GaugeReferences.zMassGeV) :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  have := above_bound (L0 := 0.2716) (c := 1 / 0.1227) hA (by norm_num)
    (le_trans (by norm_num) hL) (by norm_num) (by norm_num) (by norm_num)
  simpa using this

theorem at_v {A : ℝ} (hA : 0.11799 < A ∧ A < 0.11800) : 0.1296 < implied GaugeReferences.zMassGeV A GaugeReferences.vevRoundedGeV := by
  have hL : 1 - (GaugeReferences.vevRoundedGeV / GaugeReferences.zMassGeV)⁻¹ ≤ Real.log (GaugeReferences.vevRoundedGeV / GaugeReferences.zMassGeV) :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  have := above_bound (L0 := 0.6296) (c := 1 / 0.1296) hA (by norm_num)
    (le_trans (by norm_num) hL) (by norm_num) (by norm_num) (by norm_num)
  simpa using this

end PMConstants.ReadoutScales

namespace PMConstants.ScalePairing
open PMConstants

theorem same_scale_excluded {aZ : ℝ} (h : 1 / GaugeReferences.inverseZAlphaHi < aZ ∧ aZ < 1 / GaugeReferences.inverseZAlphaLo) :
    0.1263 < aZ * footprint / ColourChannels.colourLedger ∧
      9 < (aZ * footprint / ColourChannels.colourLedger - GaugeReferences.strongComparison) / GaugeReferences.strongSigma := by
  have hf : footprint / ColourChannels.colourLedger = 8295 / 43 / (12 * (171 / 172)) := by
    norm_num [footprint, ColourChannels.colourLedger, overhead]
  have e : aZ * footprint / ColourChannels.colourLedger = aZ * (8295 / 43 / (12 * (171 / 172))) := by
    rw [mul_div_assoc, hf]
  rw [e]
  constructor
  · nlinarith [h.1]
  · rw [lt_div_iff₀ (by norm_num)]; nlinarith [h.1]

end PMConstants.ScalePairing

namespace PMConstants.StableReadout
open PMAction.RunningCoefficients Matrix GeneratorNormalization PacketTraceForm ReferenceAnchor

/-- **The pairing.** The electric side has a scale-free plateau below the lightest charged carrier;
colour has none at any flavour number; the same-scale reading misses the data. -/
theorem pairing :
    bContent 0 0 0 = 0 ∧ (∀ nf : ℕ, b0 3 nf 0 ≠ 0) ∧
      ∀ {aZ : ℝ}, (1 / GaugeReferences.inverseZAlphaHi < aZ ∧ aZ < 1 / GaugeReferences.inverseZAlphaLo) →
        9 < (aZ * footprint / ColourChannels.colourLedger - GaugeReferences.strongComparison) / GaugeReferences.strongSigma :=
  ⟨(abelian_stationary_iff 0 0 le_rfl le_rfl).mpr ⟨rfl, rfl⟩, colour_never_stationary,
    fun h => (ScalePairing.same_scale_excluded h).2⟩

end PMConstants.StableReadout

namespace PMConstants.ResourceLedger
open PMConstants

theorem sterile_counted {mZ : ℝ} (h : GaugeReferences.zMassLoGeV < mZ ∧ mZ < GaugeReferences.zMassHiGeV) :
    mZ * Real.sqrt (1 - 43/footprint15) < 80.3268 ∧
      (mZ * Real.sqrt (1 - 43/footprint15) - GaugeReferences.wMassGeV) / GaugeReferences.wMassSigmaGeV < -3.1 := by
  simp only [GaugeReferences.zMassLoGeV, GaugeReferences.zMassHiGeV] at h
  have hr : Real.sqrt (1 - 43/footprint15) < 0.8808755 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num [footprint15, overhead]
  have hp : 0 ≤ Real.sqrt (1 - 43/footprint15) := Real.sqrt_nonneg _
  have h1 : mZ * Real.sqrt (1 - 43/footprint15) < 80.3268 := by nlinarith [h.1, h.2]
  refine ⟨h1, ?_⟩
  rw [div_lt_iff₀ (by norm_num)]; linarith

end PMConstants.ResourceLedger

namespace PMConstants.ContentWeight
open PMConstants CertifiedConstants StrongLedgerTest

theorem extensive_w_mass {mZ : ℝ} (h : GaugeReferences.zMassLoGeV < mZ ∧ mZ < GaugeReferences.zMassHiGeV) :
    80.3882 < mZ * Real.sqrt (1 - 43 / footprintW 1) ∧
      mZ * Real.sqrt (1 - 43 / footprintW 1) < 80.3926 := by
  simp only [GaugeReferences.zMassLoGeV, GaugeReferences.zMassHiGeV] at h
  have h1 : (0.881590 : ℝ) < Real.sqrt (1 - 43 / footprintW 1) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num [footprintW]
  have h2 : Real.sqrt (1 - 43 / footprintW 1) < 0.881592 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num [footprintW]
  constructor <;> nlinarith [h.1, h.2]

end PMConstants.ContentWeight

namespace PMConstants.ScalarBudget


theorem budget_unique (B : ℕ) :
    ((GaugeReferences.scalarLo : ℚ) < ((B : ℚ) - 1/43) / 23 ∧ ((B : ℚ) - 1/43) / 23 < GaugeReferences.scalarHi) ↔ B = 3 := by
  constructor
  · rintro ⟨h1, h2⟩
    have hB1 : (2.98 : ℚ) < B := by linarith
    have hB2 : (B : ℚ) < 3.02 := by linarith
    have : 2 < B := by exact_mod_cast (by linarith : (2 : ℚ) < B)
    have : B < 4 := by exact_mod_cast (by linarith : (B : ℚ) < 4)
    omega
  · rintro rfl; norm_num

end PMConstants.ScalarBudget

namespace PMConstants.ReferenceDirections
open PMConstants Matrix GeneratorNormalization PacketTraceForm ReferenceAnchor ReferenceStabilizer

/-- **The scalar budget is the number of directions that move the reference.** -/
theorem budget_is_moved_count (B : ℕ) :
    ((GaugeReferences.scalarLo : ℚ) < ((B : ℚ) - 1/43) / 23 ∧ ((B : ℚ) - 1/43) / 23 < GaugeReferences.scalarHi) ↔
      B = Module.finrank ℝ (ℝ × ℂ) := by
  rw [displacement_dim]; exact ScalarBudget.budget_unique B

end PMConstants.ReferenceDirections

namespace PMConstants.RegulatoryMaximin
open Finset

/-- **The measured coupling pins the count to 23.** -/
theorem count_unique (N : ℕ) :
    ((GaugeReferences.scalarLo : ℚ) < (3 - 1/43) / N ∧ (3 - 1/43) / N < (GaugeReferences.scalarHi : ℚ)) ↔ N = 23 := by
  constructor
  · rintro ⟨h1, h2⟩
    have hN : (0 : ℚ) < N := by
      by_contra h; push Not at h
      have : (N : ℚ) = 0 := le_antisymm h (Nat.cast_nonneg N)
      rw [this] at h1; norm_num at h1
    rw [lt_div_iff₀ hN] at h1
    rw [div_lt_iff₀ hN] at h2
    have a : (22 : ℚ) < N := by linarith
    have b : (N : ℚ) < 24 := by linarith
    have : 22 < N := by exact_mod_cast a
    have : N < 24 := by exact_mod_cast b
    omega
  · rintro rfl; norm_num

theorem pair_not_pinned :
    (GaugeReferences.scalarLo : ℚ) < (7 - 1/43) / 54 ∧ (7 - 1/43) / 54 < (GaugeReferences.scalarHi : ℚ) := by norm_num

end PMConstants.RegulatoryMaximin

namespace PMConstants.RegulatoryLabels


theorem joint_excluded :
    ¬ ((GaugeReferences.scalarLo : ℚ) < (3 - 1/43) / (160 : ℕ) ∧ (3 - 1/43) / (160 : ℕ) < (GaugeReferences.scalarHi : ℚ)) := by
  rw [RegulatoryMaximin.count_unique]; norm_num

end PMConstants.RegulatoryLabels

namespace PMConstants.RepairBudget
open PMConstants.ReferenceDirections (RepairDisplacement)
open Filter Topology PMConstants ReferenceDirections

/-- **The budget from one exact repair.** -/
theorem budget_from_repair (R : ExactRepair) (B : ℝ)
    (hB : B = LinearMap.trace ℝ RepairDisplacement R.K.toLinearMap) :
    B = 3 ∧ ((GaugeReferences.scalarLo : ℚ) < (3 - 1/43) / (23 : ℕ) ∧ (3 - 1/43) / (23 : ℕ) < (GaugeReferences.scalarHi : ℚ)) := by
  refine ⟨by rw [hB, repair_gain], (RegulatoryMaximin.count_unique 23).mpr rfl⟩

end PMConstants.RepairBudget

namespace PMConstants.CoherentBudget
open PMConstants.ReferenceDirections (RepairDisplacement)
open PMConstants.ReferenceDirections.DoubletChart
open Matrix PMAction.CoherentRecordRestoration PMAction.BranchMixerSynthesis

theorem coherent_budget (B : ℝ)
    (hB : B = LinearMap.trace ℝ RepairDisplacement coherent_repair.K.toLinearMap) :
    B = 3 ∧ ((GaugeReferences.scalarLo : ℚ) < (3 - 1/43) / (23 : ℕ) ∧ (3 - 1/43) / (23 : ℕ) < (GaugeReferences.scalarHi : ℚ)) :=
  RepairBudget.budget_from_repair coherent_repair B hB

end PMConstants.CoherentBudget

namespace PMConstants.GaugeWalkBudget
open PMConstants.ReferenceDirections (RepairDisplacement)
open PMConstants.ReferenceDirections.DoubletChart
open Matrix PMAction ConcreteFermion GaugeRecordEmbedding

theorem gauge_budget (B : ℝ) (hB : B = LinearMap.trace ℝ RepairDisplacement gauge_repair.K.toLinearMap) :
    B = 3 ∧ ((GaugeReferences.scalarLo : ℚ) < (3 - 1/43) / (23 : ℕ) ∧ (3 - 1/43) / (23 : ℕ) < (GaugeReferences.scalarHi : ℚ)) :=
  RepairBudget.budget_from_repair gauge_repair B hB

end PMConstants.GaugeWalkBudget

namespace PMConstants.TangentResponse
open PMConstants.ReferenceDirections (RepairDisplacement)
open PMConstants.ReferenceDirections.DoubletChart
open Matrix PMAction CommonResponse

/-- **The count λ keeps is the real family's.** -/
theorem count_by_lambda :
    ¬ ((GaugeReferences.scalarLo : ℝ) < (2 - 1/43) / 23) ∧ (GaugeReferences.scalarLo : ℝ) < (3 - 1/43) / 23 ∧ (3 - 1/43 : ℝ) / 23 < GaugeReferences.scalarHi := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

end PMConstants.TangentResponse

namespace PMConstants.BudgetReadout
open PMConstants.ReferenceDirections (RepairDisplacement)
open Filter Topology PMConstants

/-- **Counting the whole repair as one event is excluded by the `λ` window.** -/
theorem single_unit_excluded : ¬ ((GaugeReferences.scalarLo : ℝ) < (1 - 1/43) / 23) := by norm_num

/-- **Per-direction renewal of the repair record cannot be the clock credit.** Any renewal charge
of at least `3/43` per phase puts the ledger below the window. -/
theorem renewal_per_direction_excluded (c : ℝ) (hc : 3 / 43 ≤ c) :
    (3 - c) / 23 < GaugeReferences.scalarLo := by
  have : (3 - c) / 23 ≤ (3 - 3/43) / 23 := by gcongr
  linarith [show (3 - 3/43 : ℝ) / 23 < GaugeReferences.scalarLo by norm_num]

/-- **Both ledger terms in one unit.** -/
theorem ledger_from_readouts (R : RepairBudget.ExactRepair) (f : Module.End ℝ RepairDisplacement →ₗ[ℝ] ℝ)
    (hf : FrameIndependent f) (hone : f P₁ = 1)
    (clock : Fin PMSubstrate.E8Values.Delta → ℝ) (hinv : ∀ i, clock (finRotate PMSubstrate.E8Values.Delta i) = clock i) (hsum : ∑ i, clock i = 1) :
    (f R.K.toLinearMap - clock 0) / 23 = (3 - 1 / 43) / 23 ∧
      (GaugeReferences.scalarLo : ℝ) < (3 - 1 / 43) / 23 ∧ (3 - 1 / 43 : ℝ) / 23 < GaugeReferences.scalarHi := by
  rw [budget_readout R f hf hone, RegulatoryBudget.clock_credit clock hinv hsum]
  norm_num

end PMConstants.BudgetReadout

namespace PMConstants.WalkTrials
open PMAction WalkReferenceCycle

/-- **Uniform instruction counts do not fit as the budget.** -/
theorem instruction_ledgers_excluded :
    (WalkReferenceProtocol.program.map (WalkReferenceProtocol.price 1 1 1 1)).sum = 4 ∧
      ¬ ((GaugeReferences.scalarLo : ℝ) < (4 - 1/43) / 23 ∧ (4 - 1/43 : ℝ) / 23 < GaugeReferences.scalarHi) ∧
      ¬ ((GaugeReferences.scalarLo : ℝ) < (1 - 1/43) / 23) ∧
      ((GaugeReferences.scalarLo : ℝ) < (3 - 1/43) / 23 ∧ (3 - 1/43 : ℝ) / 23 < GaugeReferences.scalarHi) := by
  refine ⟨by rw [WalkReferenceProtocol.step_price]; norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num⟩

/-- **Renewal at the preparation price is not excluded.** -/
theorem preparation_renewal_allowed :
    let c := (1 - Real.cos (Real.pi / 4)) / 43
    (GaugeReferences.scalarLo : ℝ) < (3 - 1/43 - c) / 23 ∧ (3 - 1/43 - c) / 23 < GaugeReferences.scalarHi := by
  intro c
  have hc : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  have s1 : (1.414 : ℝ) < Real.sqrt 2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s2 : Real.sqrt 2 < (1.415 : ℝ) := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  simp only [c, hc]
  constructor <;> nlinarith

end PMConstants.WalkTrials
