import PMConstants.VevImpedance
import PMConstants.VevCorrections
import PMSubstrate.CapacityBarbier

/-!
# The VEV's boundary admittance: `χ` closures in parallel around a width-`D` boundary

`VevImpedance.vev_series` writes the topological factor as the node impedance `α⁻¹` in series with
the fan-out: the `D` axes as unit channels in parallel with a boundary admittance `b`, and the data
single out `b = χ/(Dπ)` (`VevCorrections.boundary_unique`). This module builds `b` from the same
three ingredients as the node impedance `Z_geo` and tests the alternatives.

* Boundary length (`barbier_boundary`): a causal envelope of constant width `w` has boundary
  `π w` (`PMSubstrate.Capacity.barbier`; at width `Δ` this is the capacity term `πΔ`).
  At the fan-out the width is `D`, one unit per axis.
* Closures: the boundary must turn `χ` full times to close (`PMSubstrate.Descartes`; the map term
  `χ` of `Z_geo`).
* Ohm (`PMSubstrate.ProtocolToll`): `χ` closure channels in parallel, each of impedance `πD`, have
  admittance `χ/(πD)` (`parallelClosures`). `boundary_is_parallel_closures`: this is `b`.

**Tests against the Fermi window.** Within the same construction every alternative fails:
* `series_excluded`: the `χ` closures in series, `1/(χπD) = 1/(8π)`;
* `cycle_width_excluded`: width `Δ` (the clock cycle, as the Governor term spreads `χ`),
  `χ/(πΔ) = 2/(43π)`;
* `one_closure_excluded`: a single closure, `1/(πD) = 1/(4π)`;
* `sigma_excluded`, `nu_excluded`: the wires `σ` or the channels `ν` in place of `χ`;
* `no_pi_excluded`: the closures without the boundary length, `χ/D`;
* `selected_fits`: `χ` closures in parallel around width `D` lies in the window.

With `D = 4`, `χ/(πD)` equals `χ/(4π)` (the closures shared over the full solid angle); the data do
not separate the two.

Status: this is what persists, in the sense `VevAccounting` uses for the slot count: within the
construction from Barbier, Descartes and Ohm, the measured Fermi constant admits exactly one form.
With `VevImpedance` (series structure), `VevReadout` (linear form) and `VevEvent` (one-axis margin
share), every factor of the VEV is accounted for.
-/

noncomputable section
namespace PMConstants.VevBoundary
open PMConstants.VevCorrections PMSubstrate.E8Values

/-- A constant-width envelope of width `w` has boundary length `π w` (Barbier). -/
theorem barbier_boundary (w : ℝ) : ∫ _ in (0)..(2 * Real.pi), w / 2 = Real.pi * w :=
  PMSubstrate.Capacity.barbier (fun _ => w / 2) continuous_const w (fun _ => by ring)

/-- `n` closure channels in parallel, each of impedance `πw` (the boundary of a width-`w`
envelope). -/
def parallelClosures (n w : ℝ) : ℝ := n / (Real.pi * w)

/-- The same channels in series. -/
def seriesClosures (n w : ℝ) : ℝ := 1 / (n * (Real.pi * w))

theorem boundary_is_parallel_closures :
    VevImpedance.boundary = parallelClosures (chi : ℝ) (D : ℝ) := by
  unfold VevImpedance.boundary parallelClosures; ring

/-- The Fermi window for `D_eff = 4 + r`. -/
def Fits (r : ℝ) : Prop := 246.21957 < withDimension (4 + r) ∧ withDimension (4 + r) < 246.21971

lemma excluded {r : ℝ} (a b : ℕ) (hr : r = (a : ℝ) / ((b : ℝ) * Real.pi)) (hb : 0 < b)
    (hb2 : b ≤ 200) (hne : 2 * a ≠ b) : ¬ Fits r := by
  rw [Fits, hr]; exact fun h => hne ((boundary_unique a b hb hb2).1 h)

theorem selected_fits : Fits (parallelClosures (chi : ℝ) (D : ℝ)) := by
  rw [Fits, show parallelClosures (chi : ℝ) (D : ℝ) = ((2 : ℕ) : ℝ) / (((4 : ℕ) : ℝ) * Real.pi) by
    simp only [parallelClosures, chi_eq, D_eq]; push_cast; ring]
  exact (boundary_unique 2 4 (by norm_num) (by norm_num)).2 (by norm_num)

theorem series_excluded : ¬ Fits (seriesClosures (chi : ℝ) (D : ℝ)) :=
  excluded 1 8 (by simp only [seriesClosures, chi_eq, D_eq]; push_cast; ring)
    (by norm_num) (by norm_num) (by norm_num)

theorem cycle_width_excluded : ¬ Fits (parallelClosures (chi : ℝ) (Delta : ℝ)) :=
  excluded 2 43 (by simp only [parallelClosures, chi_eq, Delta_eq]; push_cast; ring)
    (by norm_num) (by norm_num) (by norm_num)

theorem one_closure_excluded : ¬ Fits (parallelClosures 1 (D : ℝ)) :=
  excluded 1 4 (by simp only [parallelClosures, D_eq]; push_cast; ring)
    (by norm_num) (by norm_num) (by norm_num)

theorem sigma_excluded : ¬ Fits (parallelClosures (sigma : ℝ) (D : ℝ)) :=
  excluded 5 4 (by simp only [parallelClosures, sigma_eq, D_eq]; push_cast; ring)
    (by norm_num) (by norm_num) (by norm_num)

theorem nu_excluded : ¬ Fits (parallelClosures (nu : ℝ) (D : ℝ)) :=
  excluded 16 4 (by simp only [parallelClosures, nu_eq, D_eq]; push_cast; ring)
    (by norm_num) (by norm_num) (by norm_num)

theorem no_pi_excluded : ¬ Fits ((chi : ℝ) / (D : ℝ)) := by
  intro h
  rw [Fits, show (chi : ℝ) / (D : ℝ) = 1 / 2 by rw [chi_eq, D_eq]; norm_num] at h
  have := dimension_window (by norm_num) h
  norm_num at this

end PMConstants.VevBoundary
