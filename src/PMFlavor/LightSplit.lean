import PMFlavor.CompositeMass
import Mathlib.Tactic.Module

/-!
# The light-pair split needs two wall asymmetries

`tools/composite_mass_scan.py`: with equal light carriers the composite of `CompositeMass` is
excluded for leptons and up quarks, so the two light generations' composite masses must differ.
`ExchangeChirality`: the class swap fixing `v` combined with the wall exchange is a symmetry of the
incidence (`swap_with_exchange`), and only the weak current, on one wall, breaks it.

* `composite_expansion2`: with on-site flips `δ_F` on wall `false` and `δ_T` on wall `true`, and
  carriers `κ` (wall `false`) and `κ'` (wall `true`) with the crossing's support,
  `M = δ_F δ_T Y⁻¹ + δ_F · diag(κ'/y) + δ_T · diag(κ/y) + (second order, cyclic)`. Generation `g`'s
  diagonal entry is `δ_T κ_F(e g) + δ_F κ_T(e g)` (over `y`): one term from each order of
  `PMConstants.GenerationMass`, each with the label class `e g`.
* `light_split`: if the carrier amplitudes keep the swap × exchange symmetry
  (`κ_F(s) = κ_T(c)`, `κ_T(s) = κ_F(c)`), the difference of the two light diagonal entries is
  `(δ_T − δ_F) · (κ_F(s) − κ_T(s))`.
* `split_needs_both`: so it vanishes if the on-site flip is the same on both walls or the carrier
  is. A split needs both to be wall-asymmetric.
* `near_maximal`: with `x = δ_F/δ_T` and `u = κ_T(s)/κ_F(s)` in `[0, 1]` the light ratio is
  `(1 + x u)/(u + x)`; a ratio `R` forces `u + x ≤ 2/R`. The scan (`tools/composite_mass_scan.py`,
  `min_split`) needs `R ≳ 200` for leptons and `≳ 500` for up quarks, while down fits with `R = 1`.
  So for leptons and up quarks both asymmetries are near maximal (each `≲ 1%`): the on-site flip and
  the carrier each sit almost entirely on one wall. A perturbative source (a weak-coupling-order
  correction on one wall) is excluded.

`WallSeesaw` and `CompositeMass` take one `δ` for both walls; with that the light pair stays
degenerate at this order whatever the carriers do. So the light-pair split needs a source for
`δ_T ≠ δ_F`, a wall-dependent on-site chirality flip, which the library does not yet have
(`PMAction.ZeroModeCoupling` places the residual on-site mass at `r ≠ 1`, but the same on both
walls). `near_maximal` rules out a perturbative source for leptons and up quarks: the source must
put each term almost entirely on one wall, and differ between sectors (down needs no split). Derived
sizes would give the light ratio `(δ_T κ_F + δ_F κ_T)/(δ_T κ_T + δ_F κ_F)` (class `s`) in each
sector, a test.
-/

noncomputable section
namespace PMFlavor.LightSplit
open Matrix PMFlavor.CyclicSeesaw PMFlavor.CompositeMass

/-- **The light mass with wall-dependent on-site flips and carriers.** -/
theorem composite_expansion2 (y κ κ' : Fin 3 → ℂ) (δF δT : ℂ) (hy : ∀ j, y j ≠ 0) :
    (δF • (1 : Matrix (Fin 3) (Fin 3) ℂ) + cyc κ) * (cyc y)⁻¹ * (δT • 1 + cyc κ') =
      (δF * δT) • cycInv y + δF • diagonal (fun j => (y j)⁻¹ * κ' j)
        + δT • diagonal ![κ 2 * (y 2)⁻¹, κ 0 * (y 0)⁻¹, κ 1 * (y 1)⁻¹]
        + diagonal ![κ 2 * (y 2)⁻¹, κ 0 * (y 0)⁻¹, κ 1 * (y 1)⁻¹] * cyc κ' := by
  rw [inv_cyc y hy]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    cyc_mul_cycInv, cycInv_mul_cyc]
  module

/-- **The light split factors** under the swap × exchange symmetry of the carriers. -/
theorem light_split (δT δF kFs kTs kFc kTc : ℂ) (h1 : kFs = kTc) (h2 : kTs = kFc) :
    (δT * kFs + δF * kTs) - (δT * kFc + δF * kTc) = (δT - δF) * (kFs - kTs) := by
  subst h1 h2; ring

/-- **A split needs both asymmetries.** -/
theorem split_needs_both (δT δF kFs kTs kFc kTc : ℂ) (h1 : kFs = kTc) (h2 : kTs = kFc)
    (h : δT = δF ∨ kFs = kTs) :
    δT * kFs + δF * kTs = δT * kFc + δF * kTc := by
  rw [← sub_eq_zero, light_split δT δF kFs kTs kFc kTc h1 h2]
  rcases h with h | h <;> simp [h]

/-- **A large split forces both asymmetries near maximal.** With `x = δ_F/δ_T`, `u = κ_T(s)/κ_F(s)`
in `[0, 1]`, the light ratio is `(1 + x u)/(u + x)`; if it is at least `R`, then `u + x ≤ 2/R`. -/
theorem near_maximal (x u R : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hR : 0 < R) (h : R * (u + x) ≤ 1 + x * u) : u + x ≤ 2 / R := by
  rw [le_div_iff₀ hR]
  nlinarith [mul_le_one₀ hx1 hu0 hu1]

end PMFlavor.LightSplit
