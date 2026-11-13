import PMHadrons.DecayInstantiation
import PMHadrons.NeutronRate
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! **Candidate (the neutron's E8 template on the continuum route).**

# The neutron on the continuum route

The emitted electron is not a resource of any persistent volume: it leaves through the Toll
boundary (`TollGovernor`). Only a persistent volume's own sites are refreshed, so nothing confines
the electron, and its modes are those of the unbounded lattice at its own spacing, whose low-energy
limit is the continuum (`PMHadrons/REVIEW-AND-NEXT.md` §2, `tools/beta_channel_modes.py`). The
rate is then the same phase-space construction as the muon's (`PMElementaryParticles.MuonRate`,
`PolarMeasure`):

`Γ = G_F² |V_ud|² R (1 + 3 g_A²) f / (2π³)`,  `f = ∫₁^{E₀} √(E²−1) E (E₀−E)² dE`,

with `E₀ = m_n − m_p` (`neutronCutoffExact`), `|V_ud|² R = 32/33` (`vud_sq_mul_shared`,
`ShortDistanceRunning`) and `g_A = σ/D = 5/4` (`NeutronRate.gA`). All inputs are E8 values.

* `phase_integral`: `f` in closed form, `√(E₀²−1)(2E₀⁴−9E₀²−8)/60 + (E₀/4) log(E₀ + √(E₀²−1))`,
  proved as the integral (fundamental theorem of calculus).
* `coulomb_linear_integral`: the leading term of the Fermi factor, `F ≈ 1 + παE/p`, adds
  `πα ∫₁^{E₀} E²(E₀−E)² dE = πα (E₀−1)³(E₀²+3E₀+6)/30`.
* `neutronContinuum_rate`: the lifetime has the rate above.
* `neutronLifetimeContinuumSeconds_bounds`: `954.32–954.34 s` without the Coulomb pull;
  `neutronLifetimeContinuumCoulombSeconds_bounds`: `923.37–923.39 s` with its leading term
  (measured `878.4 s`). The full Fermi factor gives `922.9 s` (`tools/beta_channel_modes.py`).

The `3×3×3` spectral template (`DecayInstantiation`, `948.69–948.70 s`) is this route without
Coulomb to `0.6%`; it is kept as a comparison. What remains between `923 s` and `878.4 s` is `g_A`
(`PMAction/REVIEW-AND-NEXT.md` A.2) and the low-energy radiative correction.
-/

noncomputable section
namespace PMHadrons.NeutronContinuum
open Real Set
open PMElementaryParticles

/-! ## The phase-space integral -/

/-- Antiderivative of `√(E²−1) E (E₀−E)²` on `E ≥ 1`. -/
def phaseAnti (E0 E : ℝ) : ℝ :=
  √(E ^ 2 - 1) * (E ^ 4 / 5 - E0 / 2 * E ^ 3 + (5 * E0 ^ 2 - 1) / 15 * E ^ 2 + E0 / 4 * E -
      (5 * E0 ^ 2 + 2) / 15) +
    E0 / 4 * Real.log (E + √(E ^ 2 - 1))

/-- The closed-form phase-space factor `f(E₀)`. -/
def phaseFactor (E0 : ℝ) : ℝ :=
  √(E0 ^ 2 - 1) * ((2 * E0 ^ 4 - 9 * E0 ^ 2 - 8) / 60) + E0 / 4 * Real.log (E0 + √(E0 ^ 2 - 1))

theorem phaseAnti_one (E0 : ℝ) : phaseAnti E0 1 = 0 := by
  simp [phaseAnti]

theorem phaseAnti_self (E0 : ℝ) : phaseAnti E0 E0 = phaseFactor E0 := by
  unfold phaseAnti phaseFactor
  ring

theorem phaseAnti_hasDerivAt (E0 x : ℝ) (hx : 1 < x) :
    HasDerivAt (phaseAnti E0) (√(x ^ 2 - 1) * x * (E0 - x) ^ 2) x := by
  have hq : 0 < x ^ 2 - 1 := by nlinarith
  have hf : HasDerivAt (fun y : ℝ => y ^ 2 - 1) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).sub_const 1
  have hs := hf.sqrt hq.ne'
  have hs0 : 0 < √(x ^ 2 - 1) := Real.sqrt_pos.mpr hq
  have hxs : 0 < x + √(x ^ 2 - 1) := by linarith
  have hp := ((((hasDerivAt_pow 4 x).div_const 5).sub ((hasDerivAt_pow 3 x).const_mul (E0 / 2))).add
      ((hasDerivAt_pow 2 x).const_mul ((5 * E0 ^ 2 - 1) / 15))).add
      ((hasDerivAt_id' (x := x)).const_mul (E0 / 4)) |>.sub_const ((5 * E0 ^ 2 + 2) / 15)
  have hl := (((hasDerivAt_id' (x := x)).add hs).log hxs.ne').const_mul (E0 / 4)
  have hmain := (hs.mul hp).add hl
  refine hmain.congr_deriv ?_
  have hs2 : √(x ^ 2 - 1) ^ 2 = x ^ 2 - 1 := Real.sq_sqrt hq.le
  set s := √(x ^ 2 - 1)
  have hsne : s ≠ 0 := hs0.ne'
  have hxsne : x + s ≠ 0 := hxs.ne'
  simp only [Pi.add_apply, Pi.sub_apply, Nat.cast_ofNat, show (4 : ℕ) - 1 = 3 from rfl,
    show (3 : ℕ) - 1 = 2 from rfl, show (2 : ℕ) - 1 = 1 from rfl, pow_one, mul_one]
  calc _ = (x * (x ^ 4 / 5 - E0 / 2 * x ^ 3 + (5 * E0 ^ 2 - 1) / 15 * x ^ 2 + E0 / 4 * x -
          (5 * E0 ^ 2 + 2) / 15) +
        s ^ 2 * (4 * x ^ 3 / 5 - 3 * E0 / 2 * x ^ 2 + 2 * (5 * E0 ^ 2 - 1) / 15 * x + E0 / 4) +
        E0 / 4) / s := by
        field_simp
        ring
    _ = (x ^ 2 - 1) * x * (E0 - x) ^ 2 / s := by
        rw [hs2]
        congr 1
        ring
    _ = s * x * (E0 - x) ^ 2 := by
        rw [← hs2, div_eq_iff hsne]
        ring

theorem phaseAnti_continuousOn (E0 a : ℝ) : ContinuousOn (phaseAnti E0) (Icc 1 a) := by
  unfold phaseAnti
  apply ContinuousOn.add
  · exact (by fun_prop : Continuous (fun E : ℝ => √(E ^ 2 - 1) *
      (E ^ 4 / 5 - E0 / 2 * E ^ 3 + (5 * E0 ^ 2 - 1) / 15 * E ^ 2 + E0 / 4 * E -
        (5 * E0 ^ 2 + 2) / 15))).continuousOn
  · apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.log
    · exact (by fun_prop : Continuous (fun E : ℝ => E + √(E ^ 2 - 1))).continuousOn
    · intro y hy
      have h1 : 1 ≤ y := hy.1
      have := Real.sqrt_nonneg (y ^ 2 - 1)
      exact ne_of_gt (by linarith)

/-- **The phase-space factor is the integral**: `∫₁^{E₀} √(E²−1) E (E₀−E)² dE = f(E₀)`. -/
theorem phase_integral (E0 : ℝ) (h : 1 ≤ E0) :
    ∫ E in (1 : ℝ)..E0, √(E ^ 2 - 1) * E * (E0 - E) ^ 2 = phaseFactor E0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f' := fun E => √(E ^ 2 - 1) * E * (E0 - E) ^ 2) h (phaseAnti_continuousOn E0 E0)
    (fun x hx => phaseAnti_hasDerivAt E0 x hx.1)
    ((by fun_prop : Continuous (fun E : ℝ => √(E ^ 2 - 1) * E * (E0 - E) ^ 2)).intervalIntegrable _ _),
    phaseAnti_one, phaseAnti_self, sub_zero]

/-- The leading Coulomb term, `(E₀−1)³(E₀²+3E₀+6)/30`. -/
def coulombLinear (E0 : ℝ) : ℝ := (E0 - 1) ^ 3 * (E0 ^ 2 + 3 * E0 + 6) / 30

/-- **`∫₁^{E₀} E²(E₀−E)² dE = (E₀−1)³(E₀²+3E₀+6)/30`**: the integral that multiplies `πα` when the
Fermi factor `F = 2πη/(1−e^{−2πη})`, `η = αE/p`, is taken to first order, `F ≈ 1 + παE/p`. -/
theorem coulomb_linear_integral (E0 : ℝ) :
    ∫ E in (1 : ℝ)..E0, E ^ 2 * (E0 - E) ^ 2 = coulombLinear E0 := by
  have hd : ∀ x ∈ uIcc (1 : ℝ) E0, HasDerivAt
      (fun E : ℝ => E0 ^ 2 / 3 * E ^ 3 - E0 / 2 * E ^ 4 + E ^ 5 / 5) (x ^ 2 * (E0 - x) ^ 2) x := by
    intro x _
    have h := (((hasDerivAt_pow 3 x).const_mul (E0 ^ 2 / 3)).sub
      ((hasDerivAt_pow 4 x).const_mul (E0 / 2))).add ((hasDerivAt_pow 5 x).div_const 5)
    refine h.congr_deriv ?_
    simp only [Nat.cast_ofNat, show (5 : ℕ) - 1 = 4 from rfl, show (4 : ℕ) - 1 = 3 from rfl,
      show (3 : ℕ) - 1 = 2 from rfl]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous (fun E : ℝ => E ^ 2 * (E0 - E) ^ 2)).intervalIntegrable _ _)]
  simp only [coulombLinear]
  ring

/-! ## The neutron's numbers -/

/-- The neutron's phase-space factor at the E8 endpoint. -/
def neutronPhaseSpace : ℝ := phaseFactor neutronCutoffExact

/-- The neutron's leading Coulomb integral at the E8 endpoint. -/
def neutronCoulombLinear : ℝ := coulombLinear neutronCutoffExact

/-- Lifetime in seconds for a phase-space factor `f`. -/
def neutronContinuumSeconds (f : ℝ) : ℝ :=
  33 * (PhysicalUnits.electronTime * Real.pi ^ 3) / (91 * (SharedUnits.fermiME ^ 2 * f))

/-- The E8 neutron lifetime on the continuum route, no Coulomb pull. -/
def neutronLifetimeContinuumSeconds : ℝ := neutronContinuumSeconds neutronPhaseSpace

/-- The same with the Fermi factor's leading term, `f + πα ∫E²(E₀−E)²`. -/
def neutronLifetimeContinuumCoulombSeconds : ℝ :=
  neutronContinuumSeconds (neutronPhaseSpace + Real.pi * SharedUnits.αe * neutronCoulombLinear)

/-- **The rate is `G_F² |V_ud|² R (1+3g_A²) f/(2π³)`** with `|V_ud|² R` the shared factor and
`g_A = σ/D`: `33/91 = 1/((32/33)(1 + 3(5/4)²))` with the `2` of `2π³`. -/
theorem neutronContinuum_rate (f : ℝ) (hf : f ≠ 0) :
    neutronContinuumSeconds f = PhysicalUnits.electronTime /
      (SharedUnits.fermiME ^ 2 * (PMFlavor.Values.vud ^ 2 * DecayInstantiation.sharedFactor) *
        (1 + 3 * NeutronRate.gA ^ 2) * f / (2 * Real.pi ^ 3)) := by
  rw [DecayInstantiation.vud_sq_mul_shared, PMSubstrate.E8Margin.pionMargin_eq,
    NeutronRate.gA_eq]
  have hG : SharedUnits.fermiME ≠ 0 := PMElementaryParticles.Values.fermiME_pos.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  unfold neutronContinuumSeconds
  field_simp
  ring

/-! ### Certified bounds -/

theorem cutoff_bounds : (2.530988555 : ℝ) < neutronCutoffExact ∧
    neutronCutoffExact < 2.530988656 := by
  have hn := CompositeMasses.neutron_value
  have hp := CompositeMasses.proton_value
  unfold neutronCutoffExact
  constructor
  · linarith [hn.1, hp.2]
  · linarith [hn.2, hp.1]

theorem neutronPhaseSpace_eq_integral :
    neutronPhaseSpace =
      ∫ E in (1 : ℝ)..neutronCutoffExact, √(E ^ 2 - 1) * E * (neutronCutoffExact - E) ^ 2 := by
  rw [phase_integral _ (by linarith [cutoff_bounds.1])]
  rfl

private lemma log_lo : (1.5802249 : ℝ) < Real.log 4.856048 := by
  have hsplit : Real.log (4.856048 : ℝ) = 2 * Real.log 2 + Real.log (1 - (-0.214012)) := by
    rw [show (4.856048 : ℝ) = 2 ^ 2 * (1 - (-0.214012)) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have hser := Real.abs_log_sub_add_sum_range_le (x := (-0.214012 : ℝ)) (by norm_num) 12
  rw [abs_le] at hser
  obtain ⟨h1, _⟩ := hser
  rw [hsplit]
  have h2 := Real.log_two_gt_d9
  set L := Real.log (1 - (-0.214012 : ℝ))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h1
  norm_num at h1
  linarith

private lemma log_hi : Real.log 4.856049 < (1.5802252 : ℝ) := by
  have hsplit : Real.log (4.856049 : ℝ) = 2 * Real.log 2 + Real.log (1 - (-0.21401225)) := by
    rw [show (4.856049 : ℝ) = 2 ^ 2 * (1 - (-0.21401225)) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have hser := Real.abs_log_sub_add_sum_range_le (x := (-0.21401225 : ℝ)) (by norm_num) 12
  rw [abs_le] at hser
  obtain ⟨_, h1⟩ := hser
  rw [hsplit]
  have h2 := Real.log_two_lt_d9
  set L := Real.log (1 - (-0.21401225 : ℝ))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h1
  norm_num at h1
  linarith

theorem neutronPhaseSpace_bounds :
    (1.6360988 : ℝ) < neutronPhaseSpace ∧ neutronPhaseSpace < 1.6360997 := by
  obtain ⟨hE1, hE2⟩ := cutoff_bounds
  unfold neutronPhaseSpace phaseFactor
  set E0 := neutronCutoffExact
  have ht1 : (6.4059030 : ℝ) < E0 ^ 2 := by
    have := mul_lt_mul'' hE1 hE1 (by norm_num) (by norm_num)
    nlinarith
  have ht2 : E0 ^ 2 < (6.4059036 : ℝ) := by
    have := mul_lt_mul'' hE2 hE2 (by linarith) (by linarith)
    nlinarith
  have hs1 : (2.3250597 : ℝ) < √(E0 ^ 2 - 1) := by
    rw [Real.lt_sqrt (by norm_num)]
    linarith
  have hs2 : √(E0 ^ 2 - 1) < (2.3250600 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    linarith
  have h4 : E0 ^ 4 = (E0 ^ 2) ^ 2 := by ring
  have hp1 : (0.2736343 : ℝ) < (2 * E0 ^ 4 - 9 * E0 ^ 2 - 8) / 60 := by
    rw [h4]
    nlinarith [mul_pos (sub_pos.2 ht1) (show (0 : ℝ) < 2 * (E0 ^ 2 + 6.4059030) - 9 by linarith)]
  have hp2 : (2 * E0 ^ 4 - 9 * E0 ^ 2 - 8) / 60 < (0.2736345 : ℝ) := by
    rw [h4]
    nlinarith [mul_pos (sub_pos.2 ht2) (show (0 : ℝ) < 2 * (E0 ^ 2 + 6.4059036) - 9 by linarith)]
  have hL1 : (1.5802249 : ℝ) < Real.log (E0 + √(E0 ^ 2 - 1)) :=
    lt_trans log_lo (Real.log_lt_log (by norm_num) (by linarith))
  have hL2 : Real.log (E0 + √(E0 ^ 2 - 1)) < (1.5802252 : ℝ) :=
    lt_trans (Real.log_lt_log (by linarith) (by linarith)) log_hi
  have hm1 := mul_lt_mul'' hs1 hp1 (by norm_num) (by norm_num)
  have hm2 := mul_lt_mul'' hs2 hp2 (Real.sqrt_nonneg _) (by linarith)
  have hn1 := mul_lt_mul'' hE1 hL1 (by norm_num) (by norm_num)
  have hn2 := mul_lt_mul'' hE2 hL2 (by linarith) (by linarith)
  constructor
  · linarith
  · linarith

theorem neutronCoulombLinear_bounds :
    (2.3922138 : ℝ) < neutronCoulombLinear ∧ neutronCoulombLinear < 2.3922145 := by
  obtain ⟨hE1, hE2⟩ := cutoff_bounds
  unfold neutronCoulombLinear coulombLinear
  set E0 := neutronCutoffExact
  have ht1 : (6.4059030 : ℝ) < E0 ^ 2 := by
    have := mul_lt_mul'' hE1 hE1 (by norm_num) (by norm_num)
    nlinarith
  have ht2 : E0 ^ 2 < (6.4059036 : ℝ) := by
    have := mul_lt_mul'' hE2 hE2 (by linarith) (by linarith)
    nlinarith
  have hd1 : (1.530988555 : ℝ) ^ 3 < (E0 - 1) ^ 3 :=
    pow_lt_pow_left₀ (by linarith) (by norm_num) (by norm_num)
  have hd2 : (E0 - 1) ^ 3 < (1.530988656 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ (by linarith) (by linarith) (by norm_num)
  have hq1 : (6.4059030 + 3 * 2.530988555 + 6 : ℝ) < E0 ^ 2 + 3 * E0 + 6 := by linarith
  have hq2 : E0 ^ 2 + 3 * E0 + 6 < (6.4059036 + 3 * 2.530988656 + 6 : ℝ) := by linarith
  have hm1 := mul_lt_mul'' hd1 hq1 (by norm_num) (by norm_num)
  have hm2 := mul_lt_mul'' hd2 hq2 (pow_nonneg (by linarith) 3) (by linarith)
  constructor
  · rw [lt_div_iff₀ (by norm_num)]
    linarith
  · rw [div_lt_iff₀ (by norm_num)]
    linarith

/-- Shared bound step: `954.32 < τ(f) < 954.34`-type bounds from bounds on `f`. -/
private lemma seconds_bounds {f lo hi a b : ℝ} (hlo : lo < f) (hhi : f < hi) (hl : 0 < lo)
    (ha : a * (91 * (3.0456507e-12 ^ 2 * hi)) < 33 * (1.28808866e-21 * 3.14159265358979323846 ^ 3))
    (hb : 33 * (1.28808867e-21 * 3.14159265358979323847 ^ 3) < b * (91 * (3.0456453e-12 ^ 2 * lo)))
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    a < neutronContinuumSeconds f ∧ neutronContinuumSeconds f < b := by
  have he := PMElementaryParticles.Values.electronTime_tight
  have hG := SharedUnits.fermiME_tight
  have hpi := SharedUnits.pi_b
  have hpi1 : (3.14159265358979323846 : ℝ) ^ 3 < Real.pi ^ 3 :=
    pow_lt_pow_left₀ hpi.1 (by norm_num) (by norm_num)
  have hpi2 : Real.pi ^ 3 < (3.14159265358979323847 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hpi.2 Real.pi_pos.le (by norm_num)
  have hG1 : (3.0456453e-12 : ℝ) ^ 2 < SharedUnits.fermiME ^ 2 :=
    pow_lt_pow_left₀ hG.1 (by norm_num) (by norm_num)
  have hG2 : SharedUnits.fermiME ^ 2 < (3.0456507e-12 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hG.2 (by linarith) (by norm_num)
  have hA1 := mul_lt_mul'' he.1 hpi1 (by norm_num) (by norm_num)
  have hA2 := mul_lt_mul'' he.2 hpi2 (by linarith) (by positivity)
  have hB1 := mul_lt_mul'' hG1 hlo (by norm_num) hl.le
  have hB2 := mul_lt_mul'' hG2 hhi (by positivity) (by linarith)
  have hB0 : 0 < 91 * (SharedUnits.fermiME ^ 2 * f) := by
    have : 0 < SharedUnits.fermiME ^ 2 * f := lt_trans (by positivity) hB1
    linarith
  have hka := mul_le_mul_of_nonneg_left hB2.le ha0
  have hkb := mul_le_mul_of_nonneg_left hB1.le hb0
  unfold neutronContinuumSeconds
  constructor
  · rw [lt_div_iff₀ hB0]
    linarith
  · rw [div_lt_iff₀ hB0]
    linarith

/-- **The E8 neutron on the continuum route, no Coulomb pull: `954.32–954.34 s`.** -/
theorem neutronLifetimeContinuumSeconds_bounds :
    (954.32 : ℝ) < neutronLifetimeContinuumSeconds ∧ neutronLifetimeContinuumSeconds < 954.34 := by
  obtain ⟨h1, h2⟩ := neutronPhaseSpace_bounds
  exact seconds_bounds h1 h2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **With the Fermi factor's leading term: `923.37–923.39 s`** (measured `878.4 s`). -/
theorem neutronLifetimeContinuumCoulombSeconds_bounds :
    (923.37 : ℝ) < neutronLifetimeContinuumCoulombSeconds ∧
      neutronLifetimeContinuumCoulombSeconds < 923.39 := by
  obtain ⟨f1, f2⟩ := neutronPhaseSpace_bounds
  obtain ⟨c1, c2⟩ := neutronCoulombLinear_bounds
  have hpi := SharedUnits.pi_b
  have ha := SharedUnits.a_b
  have hpa1 := mul_lt_mul'' (mul_lt_mul'' hpi.1 ha.1 (by norm_num) (by norm_num)) c1
    (by norm_num) (by norm_num)
  have hpa2 := mul_lt_mul'' (mul_lt_mul'' hpi.2 ha.2 Real.pi_pos.le (by linarith)) c2
    (mul_nonneg Real.pi_pos.le (by linarith)) (by linarith)
  exact seconds_bounds (lo := 1.6360988 + 3.14159265358979323846 * 0.007297352562 * 2.3922138)
    (hi := 1.6360997 + 3.14159265358979323847 * 0.007297352563 * 2.3922145)
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end PMHadrons.NeutronContinuum
