import PMConstants.ElectroweakE8
import PMSubstrate.ProtocolToll

/-!
# The VEV's topological factor is a series impedance

The VEV formula is `v = S α⁻¹ (1 + α/D_eff)(1 − Y/(σ − χ)) m_e` with slot count
`S = χΔ² − (ν + DΔ)` and `D_eff = D + χ/(Dπ)` (`ElectroweakE8.vevRatio`). `VevCorrections` shows
the data fix the linear form `1 + x` and the boundary term `χ/(Dπ)`. This module rewrites the
factor with the Ohmic conventions the library already uses (`PMSubstrate.ProtocolToll`: parallel
admittances add, a unit admittance is one open channel; series impedances add).

* `series`: `(S/α)(1 + α/E) = S (α⁻¹ + 1/E)`. Each slot's impedance is the node's `α⁻¹ = Z_geo`
  in series with `1/E`.
* `fan_eq`: `D` unit channels in parallel with a boundary admittance `b` have admittance `D + b`,
  so `1/D_eff` is the impedance of the `D` axes (unit channels) in parallel with the boundary
  admittance `χ/(Dπ)`.
* `vev_series`: `vevRatio α = S · (Z_geo + 1/(D unit axes ∥ boundary)) · (1 − Y/(σ − χ))`.

Reading: the slot's handoff is the node's impedance `α⁻¹` (one repair of the footprint over the
full solid angle, `VevPremises.handoff_is_footprint_repair`) followed by one repair, the
electron's single event (`RootRepairRule.electron_one_event`), delivered through the `D` axes and
the boundary in parallel. Series addition is exactly first order, which is why the compounded
forms `exp x` and `1/(1 − x)` fail (`VevCorrections.exp_excluded`, `geometric_excluded`).

Open: the boundary admittance `χ/(Dπ)` (the data single it out among `a/(bπ)`,
`VevCorrections.boundary_unique`), and that the margin factor is one spatial axis's share
(`VevNoise`).
-/

noncomputable section
namespace PMConstants.VevImpedance
open PMSubstrate.ProtocolToll

/-- **Series form.** `(S/α)(1 + α/E) = S (α⁻¹ + 1/E)`. -/
theorem series (S α E : ℝ) (hα : α ≠ 0) : S / α * (1 + α / E) = S * (α⁻¹ + 1 / E) := by
  have h : S / α * (α / E) = S / E := by
    rw [div_mul_div_comm, mul_comm α E, mul_div_mul_right S E hα]
  rw [mul_add, mul_one, h]; ring

/-- The admittance of the `D` axes as unit channels in parallel with a boundary admittance `b`. -/
def fanAdmittance (b : ℝ) : ℝ :=
  parallelAdmittance (fun _ : Fin PMSubstrate.E8Values.D => (1 : ℝ)) + b

theorem fan_eq (b : ℝ) : fanAdmittance b = (PMSubstrate.E8Values.D : ℝ) + b := by
  simp only [fanAdmittance, parallelAdmittance, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]

/-- The boundary admittance in `D_eff`. -/
def boundary : ℝ :=
  (PMSubstrate.E8Values.chi : ℝ) / ((PMSubstrate.E8Values.D : ℝ) * Real.pi)

theorem effectiveDimension_eq : ElectroweakE8.effectiveDimension = fanAdmittance boundary := by
  rw [fan_eq]; rfl

/-- **The VEV as slot count times series impedance times margin.** -/
theorem vev_series (α : ℝ) (hα : α ≠ 0) :
    ElectroweakE8.vevRatio α =
      ((PMSubstrate.E8Values.chi : ℝ) * (PMSubstrate.E8Values.Delta : ℝ) ^ 2 -
          ((PMSubstrate.E8Values.nu : ℝ) +
            (PMSubstrate.E8Values.D : ℝ) * (PMSubstrate.E8Values.Delta : ℝ))) *
        (α⁻¹ + 1 / fanAdmittance boundary) *
        (1 - ElectroweakE8.bareYukawa /
          ((PMSubstrate.E8Values.sigma : ℝ) - (PMSubstrate.E8Values.chi : ℝ))) := by
  rw [ElectroweakE8.vevRatio, series _ _ _ hα, effectiveDimension_eq]

end PMConstants.VevImpedance
