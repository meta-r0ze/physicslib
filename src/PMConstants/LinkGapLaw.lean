import PMAction.DetuningGap
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The link sets the wall gap in cutoff units

The particle mass is `PMSubstrate.OccupancyCost.cost`. The bridge from the cutoff-unit
wall gap to an occupancy cost is open.

Paper II's detuned domain wall gives a light wall branch of gap `m` with `m(m + 1) = δ²`
(`PMAction.DetuningGap.gap_relation`), in units of the lattice cutoff. The link vacuum value
`v` must set the detuning. Two laws are possible, and the Higgs couplings to fermions decide
between them. The coupling modifier is `κ = (v/m)·dm/dv`; the Standard Model value is `1`.

* Law A, the link sets the detuning cost: `δ² = y v`. Then `κ = (m + 1)/(2m + 1)` (`kappa_cost`),
  and for fermions far below the cutoff (`m ≤ 1/100`) `0.99 < κ ≤ 1` (`kappa_cost_light`).
  The gap law is `m(m + 1) = y v`, the Standard Model's linear law with a relative correction of
  order `m`.
* Law B, the link sets the detuning amplitude: `δ = y v`. Then `κ = 2(m + 1)/(2m + 1)`
  (`kappa_amp`), and for light fermions `1.98 < κ ≤ 2` (`kappa_amp_light`).
**The event law selects law A, with no measured input.** Under the event law a displacement is
priced by its square: the link cost is `(toll·m/4)‖φ̂ − U_εφ̂‖²` (`PMAction.CommonResponse`,
`PMConstants.LinkFromEvents`). The link's vacuum value is therefore a cost, so it is proportional
to the *square* of the detuning it induces, `v = c δ²`. At such a link law A returns the wall's
own gap, `PMAction.DetuningGap.lightGap δ` (`gapA_event_priced`), while law B returns
`lightGap (δ²)` (`gapB_event_priced`); the two agree only at `δ = 0` and `δ = 1`
(`laws_agree_iff`). So the detuning cost, not its amplitude, is linear in the link. `VevEntry`
selects the same law independently, from Economy: hypercharge balance forces an odd number of
doublet insertions and Economy admits exactly one, so the gap parameter is linear in `v`
(`VevEntry.economy_law_A`).

The measured check against `κ_τ` is a comparison and lives in
`tools/e8p/E8PConstants/PMConstants/FermionLawPulls.lean`.
-/

noncomputable section
namespace PMConstants.LinkGapLaw

/-- Law A: `δ² = y v`. -/
def gapA (y v : ℝ) : ℝ := Real.sqrt (y * v + 1/4) - 1/2
/-- Law B: `δ = y v`. -/
def gapB (y v : ℝ) : ℝ := Real.sqrt ((y * v)^2 + 1/4) - 1/2

theorem gapA_detuning {y v : ℝ} (h : 0 ≤ y * v) :
    gapA y v = PMAction.DetuningGap.lightGap (Real.sqrt (y * v)) := by
  unfold gapA PMAction.DetuningGap.lightGap; rw [Real.sq_sqrt h]

theorem gapB_detuning (y v : ℝ) : gapB y v = PMAction.DetuningGap.lightGap (y * v) := rfl

lemma deriv_A {y v : ℝ} (h : 0 < y * v + 1/4) :
    HasDerivAt (gapA y) (y / (2 * Real.sqrt (y * v + 1/4))) v := by
  have h1 : HasDerivAt (fun w => y * w + 1/4) y v := by
    have := (HasDerivAt.const_mul y (hasDerivAt_id' v)).add_const (1/4 : ℝ)
    rwa [mul_one] at this
  have h2 := (h1.sqrt h.ne').sub_const (1/2 : ℝ)
  have hf : gapA y = fun x => Real.sqrt (y * x + 1/4) - 1/2 := rfl
  rw [hf]; exact h2

lemma deriv_B {y v : ℝ} :
    HasDerivAt (gapB y) (2 * y^2 * v / (2 * Real.sqrt ((y * v)^2 + 1/4))) v := by
  have hp : 0 < y^2 * v^2 + 1/4 := by positivity
  have h1 : HasDerivAt (fun w => y^2 * w^2 + 1/4) (2 * y^2 * v) v := by
    have := ((hasDerivAt_pow 2 v).const_mul (y^2)).add_const (1/4 : ℝ)
    have e : (2 * y^2 * v : ℝ) = y^2 * ((2 : ℕ) * v^(2-1)) := by push_cast; ring
    rw [e]; exact this
  have h2 := (h1.sqrt hp.ne').sub_const (1/2 : ℝ)
  have hf : gapB y = fun x => Real.sqrt (y^2 * x^2 + 1/4) - 1/2 := by
    funext x; unfold gapB; rw [mul_pow]
  rw [hf, mul_pow]; exact h2

/-- Coupling modifier from a derivative value. -/
def kappa (v m dm : ℝ) : ℝ := v / m * dm

theorem kappa_cost {y v : ℝ} (hyv : 0 < y * v) :
    kappa v (gapA y v) (y / (2 * Real.sqrt (y * v + 1/4))) =
      (gapA y v + 1) / (2 * gapA y v + 1) := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ y * v + 1/4 by linarith)
  have hsp : 1/2 < Real.sqrt (y * v + 1/4) := by
    rw [show (1/2 : ℝ) = Real.sqrt (1/4) by
      rw [show (1/4 : ℝ) = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hm : 0 < gapA y v := by unfold gapA; linarith
  have hv : v ≠ 0 := by rintro rfl; simp at hyv
  unfold kappa
  have e : 2 * gapA y v + 1 = 2 * Real.sqrt (y * v + 1/4) := by unfold gapA; ring
  rw [← e]
  have hmm : gapA y v * (gapA y v + 1) = y * v := by unfold gapA; nlinarith
  have hd : 0 < 2 * gapA y v + 1 := by linarith
  rw [div_mul_div_comm, mul_comm v y, ← hmm]
  field_simp

theorem kappa_amp {y v : ℝ} (hyv : y * v ≠ 0) :
    kappa v (gapB y v) (2 * y^2 * v / (2 * Real.sqrt ((y * v)^2 + 1/4))) =
      2 * (gapB y v + 1) / (2 * gapB y v + 1) := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ (y * v)^2 + 1/4 by positivity)
  have hpos : 0 < (y * v)^2 := by positivity
  have hsp : 1/2 < Real.sqrt ((y * v)^2 + 1/4) := by
    rw [show (1/2 : ℝ) = Real.sqrt (1/4) by
      rw [show (1/4 : ℝ) = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hm : 0 < gapB y v := by unfold gapB; linarith
  unfold kappa
  have e : 2 * gapB y v + 1 = 2 * Real.sqrt ((y * v)^2 + 1/4) := by unfold gapB; ring
  rw [← e]
  have hmm : gapB y v * (gapB y v + 1) = (y * v)^2 := by unfold gapB; nlinarith
  have hd : 0 < 2 * gapB y v + 1 := by linarith
  rw [div_mul_div_comm, show v * (2 * y^2 * v) = 2 * (y * v)^2 by ring, ← hmm]
  field_simp

theorem kappa_cost_light {m : ℝ} (h0 : 0 ≤ m) (h1 : m ≤ 1/100) :
    0.99 < (m + 1) / (2 * m + 1) ∧ (m + 1) / (2 * m + 1) ≤ 1 := by
  have hd : 0 < 2 * m + 1 := by linarith
  constructor
  · rw [lt_div_iff₀ hd]; linarith
  · rw [div_le_one hd]; linarith

/-! ## The event law prices a displacement by its square

So the link's value is the cost `v = c δ²` of the detuning `δ` it induces, and the law that
returns the wall's own gap at that link is law A. -/

/-- **Law A at an event-priced link is the wall's mass.** -/
theorem gapA_event_priced {c δ : ℝ} (hc : 0 < c) (hδ : 0 ≤ δ) :
    gapA c⁻¹ (c * δ ^ 2) = PMAction.DetuningGap.lightGap δ := by
  rw [gapA_detuning (by positivity)]
  congr 1
  rw [inv_mul_eq_div, mul_comm, mul_div_assoc, div_self hc.ne', mul_one, Real.sqrt_sq hδ]

/-- **Law B at the same link is not.** It returns the mass of a wall detuned by `δ²`. -/
theorem gapB_event_priced {c δ : ℝ} (hc : 0 < c) :
    gapB c⁻¹ (c * δ ^ 2) = PMAction.DetuningGap.lightGap (δ ^ 2) := by
  rw [gapB_detuning]
  congr 1
  rw [inv_mul_eq_div, mul_comm, mul_div_assoc, div_self hc.ne', mul_one]

/-- **The two laws agree only at `δ = 0` and `δ = 1`.** Elsewhere the event-law pricing
distinguishes them, with no measured input. -/
theorem laws_agree_iff {c δ : ℝ} (hc : 0 < c) (hδ : 0 ≤ δ) :
    gapA c⁻¹ (c * δ ^ 2) = gapB c⁻¹ (c * δ ^ 2) ↔ δ = 0 ∨ δ = 1 := by
  rw [gapA_event_priced hc hδ, gapB_event_priced hc]
  unfold PMAction.DetuningGap.lightGap
  constructor
  · intro h
    have hs : Real.sqrt (δ ^ 2 + 1/4) = Real.sqrt ((δ ^ 2) ^ 2 + 1/4) := by linarith
    have e1 := Real.sq_sqrt (show (0:ℝ) ≤ δ ^ 2 + 1/4 by positivity)
    have e2 := Real.sq_sqrt (show (0:ℝ) ≤ (δ ^ 2) ^ 2 + 1/4 by positivity)
    have h2 : δ ^ 2 + 1/4 = (δ ^ 2) ^ 2 + 1/4 := by rw [← e1, ← e2, hs]
    have h4 : δ ^ 2 * (δ - 1) * (δ + 1) = 0 := by nlinarith [h2]
    rcases mul_eq_zero.mp h4 with h5 | h5
    · rcases mul_eq_zero.mp h5 with h6 | h6
      · exact Or.inl (by nlinarith [h6])
      · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  · rintro (rfl | rfl) <;> norm_num

theorem kappa_amp_light {m : ℝ} (h0 : 0 ≤ m) (h1 : m ≤ 1/100) :
    1.98 < 2 * (m + 1) / (2 * m + 1) ∧ 2 * (m + 1) / (2 * m + 1) ≤ 2 := by
  have hd : 0 < 2 * m + 1 := by linarith
  constructor
  · rw [lt_div_iff₀ hd]; linarith
  · rw [div_le_iff₀ hd]; linarith

/-- The coupling modifier of law A, from its actual derivative. -/
theorem law_cost {y v : ℝ} (hyv : 0 < y * v) :
    ∃ d, HasDerivAt (gapA y) d v ∧ kappa v (gapA y v) d = (gapA y v + 1) / (2 * gapA y v + 1) :=
  ⟨_, deriv_A (by linarith), kappa_cost hyv⟩

/-- The coupling modifier of law B, from its actual derivative. -/
theorem law_amp {y v : ℝ} (hyv : y * v ≠ 0) :
    ∃ d, HasDerivAt (gapB y) d v ∧ kappa v (gapB y v) d = 2 * (gapB y v + 1) / (2 * gapB y v + 1) :=
  ⟨_, deriv_B, kappa_amp hyv⟩

end PMConstants.LinkGapLaw
