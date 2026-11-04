import PMAction.DetuningMass
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# How the link sets fermion masses: the Higgs couplings decide

Paper II's detuned domain wall gives a light fermion of mass `m` with `m(m + 1) = δ²`
(`PMAction.DetuningMass.mass_relation`), in units of the lattice cutoff. The link vacuum value
`v` must set the detuning. Two laws are possible, and the Higgs couplings to fermions decide
between them. The coupling modifier is `κ = (v/m)·dm/dv`; the Standard Model value is `1`.

* Law A, the link sets the detuning cost: `δ² = y v`. Then `κ = (m + 1)/(2m + 1)` (`kappa_cost`),
  and for fermions far below the cutoff (`m ≤ 1/100`) `0.99 < κ ≤ 1` (`kappa_cost_light`).
  The mass law is `m(m + 1) = y v`, the Standard Model's linear law with a relative correction of
  order `m`.
* Law B, the link sets the detuning amplitude: `δ = y v`. Then `κ = 2(m + 1)/(2m + 1)`
  (`kappa_amp`), and for light fermions `1.98 < κ ≤ 2` (`kappa_amp_light`).
* `tau_decides`: against `κ_τ = 0.92 ± 0.08` (CMS, 2022), law A's pull is at most `1.0` and
  law B's exceeds `13`. The data select law A: the detuning cost, not its amplitude, is linear in
  the link. This agrees with the event law, which prices the squared amplitude.
-/

noncomputable section
namespace PMConstants.FermionMassLaw

/-- Law A: `δ² = y v`. -/
def massA (y v : ℝ) : ℝ := Real.sqrt (y * v + 1/4) - 1/2
/-- Law B: `δ = y v`. -/
def massB (y v : ℝ) : ℝ := Real.sqrt ((y * v)^2 + 1/4) - 1/2

theorem massA_detuning {y v : ℝ} (h : 0 ≤ y * v) :
    massA y v = PMAction.DetuningMass.lightMass (Real.sqrt (y * v)) := by
  unfold massA PMAction.DetuningMass.lightMass; rw [Real.sq_sqrt h]

theorem massB_detuning (y v : ℝ) : massB y v = PMAction.DetuningMass.lightMass (y * v) := rfl

lemma deriv_A {y v : ℝ} (h : 0 < y * v + 1/4) :
    HasDerivAt (massA y) (y / (2 * Real.sqrt (y * v + 1/4))) v := by
  have h1 : HasDerivAt (fun w => y * w + 1/4) y v := by
    have := (HasDerivAt.const_mul y (hasDerivAt_id' v)).add_const (1/4 : ℝ)
    rwa [mul_one] at this
  have h2 := (h1.sqrt h.ne').sub_const (1/2 : ℝ)
  have hf : massA y = fun x => Real.sqrt (y * x + 1/4) - 1/2 := rfl
  rw [hf]; exact h2

lemma deriv_B {y v : ℝ} :
    HasDerivAt (massB y) (2 * y^2 * v / (2 * Real.sqrt ((y * v)^2 + 1/4))) v := by
  have hp : 0 < y^2 * v^2 + 1/4 := by positivity
  have h1 : HasDerivAt (fun w => y^2 * w^2 + 1/4) (2 * y^2 * v) v := by
    have := ((hasDerivAt_pow 2 v).const_mul (y^2)).add_const (1/4 : ℝ)
    have e : (2 * y^2 * v : ℝ) = y^2 * ((2 : ℕ) * v^(2-1)) := by push_cast; ring
    rw [e]; exact this
  have h2 := (h1.sqrt hp.ne').sub_const (1/2 : ℝ)
  have hf : massB y = fun x => Real.sqrt (y^2 * x^2 + 1/4) - 1/2 := by
    funext x; unfold massB; rw [mul_pow]
  rw [hf, mul_pow]; exact h2

/-- Coupling modifier from a derivative value. -/
def kappa (v m dm : ℝ) : ℝ := v / m * dm

theorem kappa_cost {y v : ℝ} (hyv : 0 < y * v) :
    kappa v (massA y v) (y / (2 * Real.sqrt (y * v + 1/4))) =
      (massA y v + 1) / (2 * massA y v + 1) := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ y * v + 1/4 by linarith)
  have hsp : 1/2 < Real.sqrt (y * v + 1/4) := by
    rw [show (1/2 : ℝ) = Real.sqrt (1/4) by
      rw [show (1/4 : ℝ) = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hm : 0 < massA y v := by unfold massA; linarith
  have hv : v ≠ 0 := by rintro rfl; simp at hyv
  unfold kappa
  have e : 2 * massA y v + 1 = 2 * Real.sqrt (y * v + 1/4) := by unfold massA; ring
  rw [← e]
  have hmm : massA y v * (massA y v + 1) = y * v := by unfold massA; nlinarith
  have hd : 0 < 2 * massA y v + 1 := by linarith
  rw [div_mul_div_comm, mul_comm v y, ← hmm]
  field_simp

theorem kappa_amp {y v : ℝ} (hyv : y * v ≠ 0) :
    kappa v (massB y v) (2 * y^2 * v / (2 * Real.sqrt ((y * v)^2 + 1/4))) =
      2 * (massB y v + 1) / (2 * massB y v + 1) := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ (y * v)^2 + 1/4 by positivity)
  have hpos : 0 < (y * v)^2 := by positivity
  have hsp : 1/2 < Real.sqrt ((y * v)^2 + 1/4) := by
    rw [show (1/2 : ℝ) = Real.sqrt (1/4) by
      rw [show (1/4 : ℝ) = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hm : 0 < massB y v := by unfold massB; linarith
  unfold kappa
  have e : 2 * massB y v + 1 = 2 * Real.sqrt ((y * v)^2 + 1/4) := by unfold massB; ring
  rw [← e]
  have hmm : massB y v * (massB y v + 1) = (y * v)^2 := by unfold massB; nlinarith
  have hd : 0 < 2 * massB y v + 1 := by linarith
  rw [div_mul_div_comm, show v * (2 * y^2 * v) = 2 * (y * v)^2 by ring, ← hmm]
  field_simp

theorem kappa_cost_light {m : ℝ} (h0 : 0 ≤ m) (h1 : m ≤ 1/100) :
    0.99 < (m + 1) / (2 * m + 1) ∧ (m + 1) / (2 * m + 1) ≤ 1 := by
  have hd : 0 < 2 * m + 1 := by linarith
  constructor
  · rw [lt_div_iff₀ hd]; linarith
  · rw [div_le_one hd]; linarith

theorem kappa_amp_light {m : ℝ} (h0 : 0 ≤ m) (h1 : m ≤ 1/100) :
    1.98 < 2 * (m + 1) / (2 * m + 1) ∧ 2 * (m + 1) / (2 * m + 1) ≤ 2 := by
  have hd : 0 < 2 * m + 1 := by linarith
  constructor
  · rw [lt_div_iff₀ hd]; linarith
  · rw [div_le_iff₀ hd]; linarith

theorem tau_decides {m : ℝ} (h0 : 0 ≤ m) (h1 : m ≤ 1/100) :
    |(m + 1) / (2 * m + 1) - 0.92| / 0.08 ≤ 1.0 ∧
      13 < |2 * (m + 1) / (2 * m + 1) - 0.92| / 0.08 := by
  obtain ⟨a1, a2⟩ := kappa_cost_light h0 h1
  obtain ⟨b1, b2⟩ := kappa_amp_light h0 h1
  constructor
  · rw [abs_of_pos (by linarith), div_le_iff₀ (by norm_num)]; linarith
  · rw [abs_of_pos (by linarith), lt_div_iff₀ (by norm_num)]; linarith

/-- The coupling modifier of law A, from its actual derivative. -/
theorem law_cost {y v : ℝ} (hyv : 0 < y * v) :
    ∃ d, HasDerivAt (massA y) d v ∧ kappa v (massA y v) d = (massA y v + 1) / (2 * massA y v + 1) :=
  ⟨_, deriv_A (by linarith), kappa_cost hyv⟩

/-- The coupling modifier of law B, from its actual derivative. -/
theorem law_amp {y v : ℝ} (hyv : y * v ≠ 0) :
    ∃ d, HasDerivAt (massB y) d v ∧ kappa v (massB y v) d = 2 * (massB y v + 1) / (2 * massB y v + 1) :=
  ⟨_, deriv_B, kappa_amp hyv⟩

end PMConstants.FermionMassLaw
