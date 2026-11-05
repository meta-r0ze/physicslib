import PMConstants.Depth
import PMSubstrate.E8Values
import Mathlib.Tactic

/-!
# Bulk propagation and the thermal floor

Composition fixes the attenuation law after a per-step survival probability
has been specified. It does not identify that probability with α or 1-α.
Half of the odd clock period is not a count of discrete full hops.
The proposed thermal law is evaluated with all mass-normalization factors kept.
-/

noncomputable section
namespace PMConstants.Bulk

theorem discrete_attenuation (f : ℕ → ℝ) (p : ℝ) (h0 : f 0 = 1)
    (h1 : f 1 = p) (hcomp : ∀ m n, f (m+n) = f m * f n) :
    ∀ n, f n = p^n := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih => rw [hcomp, ih, h1, pow_succ]

/-- No integer full-hop count is half a 43-state clock. -/
theorem no_integer_half_period : ¬ ∃ n : ℕ, 2*n = 43 := by omega

/-- The shortest graph distance between clock vertices is at most 21.
The continuous circumference/diameter model is a separate construction. -/
theorem cyclic_distance_bound (x : Fin 43) : min x.val (43-x.val) ≤ 21 := by
  have := x.isLt
  omega

/-- A positive half-step is uniquely fixed once its square is the full-step
survival. Requiring such a subdivision is an extra propagation model. -/
theorem half_step_unique {p q : ℝ} (_hp : 0 ≤ p) (hq : 0 ≤ q) (hsq : q^2 = p) :
    q = Real.sqrt p := by
  have h := Real.sqrt_sq hq
  rw [hsq] at h
  exact h.symm

def halfDepth (p : ℝ) : ℝ := (Real.sqrt p)^PMSubstrate.E8Values.Delta

theorem half_depth_squared {p : ℝ} (hp : 0 ≤ p) : (halfDepth p)^2 = p^PMSubstrate.E8Values.Delta := by
  unfold halfDepth
  rw [← pow_mul, Nat.mul_comm PMSubstrate.E8Values.Delta 2, pow_mul, Real.sq_sqrt hp]

def floorRatio (α : ℝ) : ℝ := Real.pi * α /
  ((PMSubstrate.E8Values.nu : ℝ) * (PMSubstrate.E8Values.Delta : ℝ)^3)
def floorMass (α me : ℝ) : ℝ := me * floorRatio α
def vacuumDensity (α me : ℝ) : ℝ := α/2 * (floorMass α me)^4

theorem thermal_positive {α me : ℝ} (hα : 0 < α) (hme : 0 < me) :
    0 < floorMass α me ∧ 0 < vacuumDensity α me := by
  have hf : 0 < floorRatio α := by
    unfold floorRatio
    rw [PMSubstrate.E8Values.nu_eq, PMSubstrate.E8Values.Delta_eq]
    positivity
  have hm : 0 < floorMass α me := mul_pos hme hf
  exact ⟨hm, mul_pos (by linarith) (pow_pos hm 4)⟩

/-- The thermal/electron ratio and thermal/Planck ratio are different. -/
theorem floor_planck_ratio {me g : ℝ} (hme : me ≠ 0) (hg : 0 < g) (α : ℝ) :
    floorMass α me / Depth.planck me g = floorRatio α * Real.sqrt g := by
  have hs : Real.sqrt g ≠ 0 := (Real.sqrt_pos.mpr hg).ne'
  unfold floorMass Depth.planck
  field_simp

theorem density_planck_ratio {me g : ℝ} (hme : me ≠ 0) (hg : 0 < g) (α : ℝ) :
    vacuumDensity α me / (Depth.planck me g)^4 =
      α/2 * (floorRatio α)^4 * g^2 := by
  change (α/2 * (floorMass α me)^4) / (Depth.planck me g)^4 = _
  rw [mul_div_assoc, ← div_pow, floor_planck_ratio hme hg, mul_pow]
  have hs : (Real.sqrt g)^4 = g^2 := by
    calc
      (Real.sqrt g)^4 = ((Real.sqrt g)^2)^2 := by ring
      _ = g^2 := by rw [Real.sq_sqrt hg.le]
  rw [hs]
  ring

/-- The inverse thermal ratio must include the electron/Planck hierarchy. -/
theorem inverse_floor_planck_ratio {α me g : ℝ} (hα : α ≠ 0) (hme : me ≠ 0)
    (hg : 0 < g) :
    Depth.planck me g / floorMass α me =
      (1 / Real.sqrt g) * ((16 * 43^3) / (Real.pi * α)) := by
  have hp : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hs : Real.sqrt g ≠ 0 := (Real.sqrt_pos.mpr hg).ne'
  unfold Depth.planck floorMass floorRatio
  rw [PMSubstrate.E8Values.nu_eq, PMSubstrate.E8Values.Delta_eq]
  field_simp
  norm_num

end PMConstants.Bulk
