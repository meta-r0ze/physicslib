import PMConstants.ReferenceStabilizer
import PMConstants.ScalarBudget

/-!
# How many directions the electroweak actions can move the reference

`ReferenceStabilizer` showed that the electroweak generators fixing the reference's neutral carrier
are exactly the multiples of `Q`. This module counts the rest.

Write a real electroweak generator as `gen a z b = weakGen [[a, z̄], [z, -a]] + b·Y/2` with `a, b`
real and `z` complex (every Hermitian traceless `A` has this form). Its action on the neutral
carrier has components `a - b/2` (along the carrier) and `z` (into the electron carrier).

* `fixes_iff`: `gen a z b` fixes the neutral carrier exactly when `a = b/2` and `z = 0`, i.e.
  `gen = b·Q`.
* `displacement_surjective`: the displacement `(a - b/2, z) ∈ ℝ × ℂ` takes every value.
* `displacement_dim`: that space has real dimension `3`. Of the four real electroweak directions,
  one fixes the reference and three move it.
* `budget_is_moved_count`: the scalar budget `B` that `ScalarBudget.budget_unique` singles out is
  exactly this count.

Reading: under Conservation the scalar regulator must restore every independent direction in which
the maintained reference can be displaced, and under Economy none in which it cannot (the same
logic as `MinimalRefresh`). That gives one unit of budget per moved direction, `3`. This is a third
reading of the `3`, beside the colour axes `σ - χ` and the generation count; it is the one that
refers to the scalar's own task. Premise: one unit of regulatory budget per independent moved
direction.
-/

noncomputable section
namespace PMConstants.ReferenceDirections
open PMConstants Matrix GeneratorNormalization PacketTraceForm ReferenceAnchor ReferenceStabilizer

def gen (a : ℝ) (z : ℂ) (b : ℝ) : PacketGaugeActions.M :=
  weakGen !![(a : ℂ), star z; z, -(a : ℂ)] + (b : ℂ) • hyperGen

theorem gen_hermitian_traceless (a : ℝ) (z : ℂ) :
    (!![(a : ℂ), star z; z, -(a : ℂ)])ᴴ = !![(a : ℂ), star z; z, -(a : ℂ)] ∧
      (!![(a : ℂ), star z; z, -(a : ℂ)]).trace = 0 := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  · simp [Matrix.trace, Fin.sum_univ_two]

/-- The displacement of the neutral reference carrier. -/
def displacement (a : ℝ) (z : ℂ) (b : ℝ) : ℝ × ℂ := (a - b / 2, z)

theorem fixes_iff (a : ℝ) (z : ℂ) (b : ℝ) :
    Fixes (gen a z b) (lepton 0) ↔ displacement a z b = 0 := by
  obtain ⟨hh, ht⟩ := gen_hermitian_traceless a z
  rw [gen, electroweak_stabilizer _ hh ht b]
  constructor
  · intro h
    have h0 := congrFun (congrFun h (lepton 0)) (lepton 0)
    have h1 := congrFun (congrFun h (lepton 1)) (lepton 0)
    simp only [Matrix.add_apply, Matrix.smul_apply, weak_lepton, hyper_lepton] at h0 h1
    simp only [t3, weak_lepton] at h0 h1
    norm_num at h0 h1
    simp only [displacement, Prod.mk_eq_zero]
    refine ⟨?_, h1⟩
    have : ((a : ℂ) - b / 2) = 0 := by linear_combination h0
    exact_mod_cast this
  · intro h
    simp only [displacement, Prod.mk_eq_zero] at h
    obtain ⟨ha, hz⟩ := h
    have ha' : a = b / 2 := by linarith
    subst hz; subst ha'
    rw [t3, smul_add, ← weakGen_smul]
    congr 2
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

theorem displacement_surjective : Function.Surjective fun p : ℝ × ℂ × ℝ =>
    displacement p.1 p.2.1 p.2.2 := by
  rintro ⟨x, z⟩
  exact ⟨(x, z, 0), by simp [displacement]⟩

theorem displacement_dim : Module.finrank ℝ (ℝ × ℂ) = 3 := by
  rw [Module.finrank_prod, Module.finrank_self, Complex.finrank_real_complex]

/-- The four real electroweak directions. -/
theorem generator_dim : Module.finrank ℝ (ℝ × ℂ × ℝ) = 4 := by
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self, Complex.finrank_real_complex]

/-- **The scalar budget is the number of directions that move the reference.** -/
theorem budget_is_moved_count (B : ℕ) :
    ((0.1286 : ℚ) < ((B : ℚ) - 1/43) / 23 ∧ ((B : ℚ) - 1/43) / 23 < 0.1300) ↔
      B = Module.finrank ℝ (ℝ × ℂ) := by
  rw [displacement_dim]; exact ScalarBudget.budget_unique B

end PMConstants.ReferenceDirections
