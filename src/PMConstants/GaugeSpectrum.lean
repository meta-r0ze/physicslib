import PMConstants.Electroweak

/-!
# The neutral quadratic response and derived gauge mass relations

For the specified scalar kinetic response, the neutral quadratic penalty is
proportional to `(g W - g' B)^2`. Its flat direction is a mixed neutral field,
not pure temporal or pure hypercharge transport. The eigenvectors and masses
below are conditional on this response law and canonical normalization.
No gauge group, response normalization or coupling value is inferred from E8.
-/
noncomputable section
namespace PMConstants.GaugeSpectrum
open Matrix Electroweak

def neutral (g gp : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![g^2, -g*gp; -g*gp, gp^2]

theorem neutral_quadratic (g gp : ℝ) (x : Fin 2 → ℝ) :
    x ⬝ᵥ (neutral g gp *ᵥ x) = (g*x 0-gp*x 1)^2 := by
  simp [neutral, dotProduct, mulVec, Fin.sum_univ_succ]
  ring

theorem flat_direction (g gp : ℝ) : neutral g gp *ᵥ ![gp, g] = 0 := by
  ext i; fin_cases i <;> simp [neutral, mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem heavy_direction (g gp : ℝ) :
    neutral g gp *ᵥ ![g, -gp] = (g^2+gp^2) • ![g, -gp] := by
  ext i; fin_cases i <;> simp [neutral, mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem neutral_nonnegative (g gp : ℝ) (x : Fin 2 → ℝ) :
    0 ≤ x ⬝ᵥ (neutral g gp *ᵥ x) := by rw [neutral_quadratic]; positivity

theorem zero_cost_iff (g gp : ℝ) (x : Fin 2 → ℝ) :
    x ⬝ᵥ (neutral g gp *ᵥ x) = 0 ↔ g*x 0 = gp*x 1 := by
  rw [neutral_quadratic, sq_eq_zero_iff, sub_eq_zero]

theorem response_eigenvalues (g gp : ℝ) :
    (neutral g gp).det = 0 ∧ (neutral g gp).trace = g^2+gp^2 := by
  constructor
  · simp [neutral, det_fin_two]; ring
  · simp [neutral, trace, Fin.sum_univ_succ]

def wMassSquared (a me : ℝ) : ℝ := weakSquared a * (vev a me)^2 / 4
def zMassSquared (a me : ℝ) : ℝ :=
  (weakSquared a+hyperchargeSquared a) * (vev a me)^2 / 4

/-- The phase-flat eigenmode exists for arbitrary couplings. The workload
ratio still needs a separate substrate-to-response matching argument. -/
theorem mass_split (a me : ℝ) :
    wMassSquared a me = (1-clockRatio)*zMassSquared a me := by
  unfold wMassSquared zMassSquared weakSquared hyperchargeSquared
  norm_num [clockRatio, footprint, overhead]
  ring

theorem w_mass_law (a me : ℝ) :
    wMassSquared a me * clockRatio = Real.pi*a*(vev a me)^2 := by
  unfold wMassSquared weakSquared
  norm_num [clockRatio, footprint, overhead]
  ring

theorem z_mass_law (a me : ℝ) :
    zMassSquared a me * (clockRatio*(1-clockRatio)) = Real.pi*a*(vev a me)^2 := by
  unfold zMassSquared weakSquared hyperchargeSquared
  norm_num [clockRatio, footprint, overhead]
  ring

end PMConstants.GaugeSpectrum
