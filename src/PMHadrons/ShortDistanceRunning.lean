import PMHadrons.DecayInstantiation
import PMAction.ContactRunning
import PMConstants.ElectroweakBounds
import PMConstants.Values
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-! **Candidate module.** The shared margin `R` from the running of the weak contact.

E8's `G_F` is the W exchange at zero momentum transfer (`PMAction.WeakVertex.exchange_at_zero`):
the contact at the W/Z scale. The decays happen at the hadron scale. The one-loop photon
correction to a charged-current contact between the two scales is

  `R = 1 + (3α/4π)(1 + 2Q̄) ln(m_Z²/m_p²)`,  `Q̄ = (Q_u + Q_d)/2`.

Every input here is an E8 value: `α` (Paper I), the carrier charges `2/3`, `−1/3`
(`PMElementaryParticles.CarrierAmplitude`), the tree-level E8 `m_Z`
(`ElectroweakBounds.z_mass_bounds`) and the E8 proton (`CompositeMasses.proton_value`). The
coefficient `(3/4π)(1 + 2Q̄)` is derived in `PMAction.ContactRunning` from Paper II's Dirac
matrices and the leg charges (`runningFactor_from_contact`); only the photon loop's overall log
normalization is still a continuum input.

**Result.** `runningFactor_bounds`: `1.021178 < R < 1.021180`. The pion's assigned
`32/33 = |V_ud|²·sharedFactor` gives `sharedFactor ∈ (1.021111, 1.021131)`
(`sharedFactor_bounds`), and the two agree to `< 7×10⁻⁵` (`runningFactor_sub_shared`). So the
substrate ratio `(Δ+ν+σ)/(Δ+ν+σ+χ)` that the pion channel carries is, to that precision,
`|V_ud|²` times the contact's running from the E8 W scale to the E8 proton: the margin is the
running, not a free factor.
-/

noncomputable section
namespace PMHadrons.ShortDistanceRunning
open Real

/-- E8 tree-level `m_Z` in GeV. -/
def mZ : ℝ :=
  Real.sqrt (PMConstants.GaugeSpectrum.zMassSquared PMConstants.CertifiedConstants.α
    PMConstants.ElectroweakBounds.electronGeV)

/-- E8 proton mass in GeV. -/
def mpGeV : ℝ := CompositeMasses.proton * CompositeMasses.me / 1000

/-- Average charge of the `(u, d)` carriers, `(2/3 − 1/3)/2 = 1/6`. -/
def chargeAverage : ℝ := ((2 / 3 : ℝ) + (-1 / 3)) / 2

/-- The one-loop running of the charged-current contact from `m_Z` to `m_p`. -/
def runningFactor : ℝ :=
  1 + 3 * PMElementaryParticles.SharedUnits.αe / (4 * π) * (1 + 2 * chargeAverage) *
    (2 * Real.log (mZ / mpGeV))

/-- The coefficient is `PMAction.ContactRunning`'s: twice the contact's amplitude coefficient
`c = 2` (carrier charges `2/3`, `−1/3`, lepton pair `−1`, `0`), in units of
`(α/4π)·ln(m_Z²/m_p²)`. -/
theorem runningFactor_from_contact :
    runningFactor = 1 + 2 * PMAction.ContactRunning.contactCoefficient (2 / 3) (-1 / 3) (-1) 0 *
      (PMElementaryParticles.SharedUnits.αe / (4 * π)) * (2 * Real.log (mZ / mpGeV)) := by
  rw [PMAction.ContactRunning.contact_neutron]
  unfold runningFactor chargeAverage
  ring

theorem runningFactor_eq :
    runningFactor = 1 + 2 * PMElementaryParticles.SharedUnits.αe / π * Real.log (mZ / mpGeV) := by
  unfold runningFactor chargeAverage
  ring

lemma exp_lower_point : Real.exp 4.5587 < 95.462 := by
  have hsplit : Real.exp 4.5587 = Real.exp 1 ^ 4 * Real.exp 0.5587 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he := Real.exp_one_lt_d9
  have h4 : Real.exp 1 ^ 4 < (2.7182818286 : ℝ) ^ 4 :=
    pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num)
  have hx := Real.exp_bound' (x := (0.5587 : ℝ)) (by norm_num) (by norm_num) (n := 10) (by norm_num)
  have hx2 : Real.exp 0.5587 ≤ 1.748399 := by
    norm_num [Finset.sum_range_succ, Nat.factorial] at hx; linarith
  rw [hsplit]
  calc Real.exp 1 ^ 4 * Real.exp 0.5587 < (2.7182818286 : ℝ) ^ 4 * 1.748399 :=
        mul_lt_mul h4 hx2 (Real.exp_pos _) (by positivity)
    _ < 95.462 := by norm_num

lemma exp_upper_point : (95.4735 : ℝ) < Real.exp 4.5589 := by
  have hsplit : Real.exp 4.5589 = Real.exp 1 ^ 4 * Real.exp 0.5589 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he := Real.exp_one_gt_d9
  have h4 : (2.7182818283 : ℝ) ^ 4 < Real.exp 1 ^ 4 :=
    pow_lt_pow_left₀ he (by norm_num) (by norm_num)
  have hx := Real.sum_le_exp_of_nonneg (x := (0.5589 : ℝ)) (by norm_num) 10
  have hx2 : (1.748746 : ℝ) ≤ Real.exp 0.5589 := by
    norm_num [Finset.sum_range_succ, Nat.factorial] at hx; linarith
  rw [hsplit]
  calc (95.4735 : ℝ) < (2.7182818283 : ℝ) ^ 4 * 1.748746 := by norm_num
    _ < Real.exp 1 ^ 4 * Real.exp 0.5589 := mul_lt_mul h4 hx2 (by norm_num) (by positivity)

lemma mZ_bounds : (89.57 : ℝ) < mZ ∧ mZ < 89.58 := by
  unfold mZ; exact PMConstants.ElectroweakBounds.z_mass_bounds

lemma mp_bounds : (0.938272089 : ℝ) < mpGeV ∧ mpGeV < 0.938272091 := by
  have h := CompositeMasses.proton_value
  unfold mpGeV
  simp only [PMElementaryParticles.SharedUnits.me, PMSubstrate.SIUnits.electronMassMeV]
  constructor <;> linarith [h.1, h.2]

lemma ratio_bounds : (95.462 : ℝ) < mZ / mpGeV ∧ mZ / mpGeV < 95.4735 := by
  obtain ⟨z1, z2⟩ := mZ_bounds
  obtain ⟨p1, p2⟩ := mp_bounds
  have hp : 0 < mpGeV := by linarith
  constructor
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith

lemma log_bounds : (4.5587 : ℝ) < Real.log (mZ / mpGeV) ∧ Real.log (mZ / mpGeV) < 4.5589 := by
  obtain ⟨r1, r2⟩ := ratio_bounds
  have hpos : 0 < mZ / mpGeV := by linarith
  constructor
  · rw [Real.lt_log_iff_exp_lt hpos]; linarith [exp_lower_point]
  · rw [Real.log_lt_iff_lt_exp hpos]; linarith [exp_upper_point]

/-- **`R` from the running is between `1.021178` and `1.021180`.** -/
theorem runningFactor_bounds : (1.021178 : ℝ) < runningFactor ∧ runningFactor < 1.021180 := by
  rw [runningFactor_eq]
  have ha := PMElementaryParticles.SharedUnits.a_b
  have hp1 : (3.14159265358979 : ℝ) < π := by linarith [Real.pi_gt_d20]
  have hp2 : π < (3.1415926535898 : ℝ) := by linarith [Real.pi_lt_d20]
  obtain ⟨l1, l2⟩ := log_bounds
  have hq1 : (2 * 0.007297352562 / 3.1415926535898 : ℝ) < 2 * PMElementaryParticles.SharedUnits.αe / π := by
    rw [div_lt_div_iff₀ (by norm_num) Real.pi_pos]; nlinarith [ha.1]
  have hq2 : 2 * PMElementaryParticles.SharedUnits.αe / π < (2 * 0.007297352563 / 3.14159265358979 : ℝ) := by
    rw [div_lt_div_iff₀ Real.pi_pos (by norm_num)]; nlinarith [ha.2]
  have hqpos : 0 < 2 * PMElementaryParticles.SharedUnits.αe / π := lt_trans (by norm_num) hq1
  constructor
  · have := mul_lt_mul'' hq1 l1 (by norm_num) (by norm_num)
    have hn : (1.021178 : ℝ) < 1 + 2 * 0.007297352562 / 3.1415926535898 * 4.5587 := by norm_num
    linarith
  · have := mul_lt_mul'' hq2 l2 hqpos.le (lt_trans (by norm_num) l1).le
    have hn : 1 + 2 * 0.007297352563 / 3.14159265358979 * 4.5589 < (1.021180 : ℝ) := by norm_num
    linarith

/-- The pion-fixed shared margin `(32/33)/|V_ud|²`. -/
theorem sharedFactor_bounds :
    (1.021111 : ℝ) < DecayInstantiation.sharedFactor ∧
      DecayInstantiation.sharedFactor < 1.021131 := by
  have hv := PMFlavor.Values.vud_bounds
  have hvpos : 0 < PMFlavor.Values.vud := by linarith [hv.1]
  have hv2 : 0 < PMFlavor.Values.vud ^ 2 := by positivity
  unfold DecayInstantiation.sharedFactor
  rw [PMSubstrate.E8Margin.pionMargin_eq]
  constructor
  · rw [lt_div_iff₀ hv2]; nlinarith [hv.1, hv.2]
  · rw [div_lt_iff₀ hv2]; nlinarith [hv.1, hv.2]

/-- **The pion's `32/33` is `|V_ud|²` times the running, to `7×10⁻⁵`.** -/
theorem runningFactor_sub_shared :
    (4e-5 : ℝ) < runningFactor - DecayInstantiation.sharedFactor ∧
      runningFactor - DecayInstantiation.sharedFactor < 7e-5 := by
  have h1 := runningFactor_bounds
  have h2 := sharedFactor_bounds
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end PMHadrons.ShortDistanceRunning
