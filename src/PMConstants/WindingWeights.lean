import PMConstants.VacuumModulus
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The winding-sector weights are positive: what `θ = 0` still needs

`VacuumModulus.strict_modulus` makes `θ = 0` the unique least-cost vacuum once the trivial winding
sector and the unit winding sector both have positive weight (`w₀ > 0`, `w₁ > 0`). This module
derives those two positivity premises from persistence plus one geometric fact.

**Persistence.** Every history of the gauge links has finite cost, so its survival weight
`exp(−β S)` is strictly positive (`β ≥ 0`, `S ≥ 0`: PM's D₄ action, `LatticeGibbs`, with the
link measure `LatticeGibbsU1` / `UnitaryHaar`). A sector's weight is the integral of that weight
over the sector's histories:

* `weight_nonneg`: every sector weight is `≥ 0`.
* `weight_pos`: a sector of positive measure has strictly positive weight.
* `measure_pos_of_open`: if the link measure charges every nonempty open set (true for Haar
  measure on a compact group), a sector containing a nonempty open set of histories has positive
  measure.
* `theta_zero_unique`: with the trivial and unit sectors each containing a nonempty open set of
  histories, `‖Z(θ)‖ < Z(0)` for every `θ ≠ 0` in `(−π, π]`, so `θ = 0` is the unique least-cost
  vacuum (`VacuumModulus.strict_modulus`).

**The geometric premise that remains.** Each of the sectors `0` and `1` contains a nonempty open
set of link histories. For a lattice topological charge that is locally constant on its domain of
definition (the standard construction on admissible fields), every nonempty sector has nonempty
interior, so the premise reduces to the existence of a unit-winding history on the region. That
is a statement about lattice gauge geometry, not a persistence choice. The sector-exchange
premise of `SectorExchange` (`θ̄ = θ`) is separate and unchanged.
-/

noncomputable section
namespace PMConstants.WindingWeights
open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

/-- The survival weight of a set `A` of link histories: `∫_A exp(−β S) dμ`. -/
def weight (β : ℝ) (S : Ω → ℝ) (A : Set Ω) : ℝ := ∫ x in A, Real.exp (-(β * S x)) ∂μ

omit [IsFiniteMeasure μ] in
theorem weight_nonneg (β : ℝ) (S : Ω → ℝ) (A : Set Ω) : 0 ≤ weight μ β S A :=
  integral_nonneg fun _ => (Real.exp_pos _).le

/-- **A sector of positive measure has strictly positive weight.** -/
theorem weight_pos {β : ℝ} {S : Ω → ℝ} {A : Set Ω} (hβ : 0 ≤ β) (hS : ∀ x, 0 ≤ S x)
    (hSm : Measurable S) (hA : 0 < μ A) : 0 < weight μ β S A := by
  unfold weight
  have hmeas : Measurable fun x => Real.exp (-(β * S x)) :=
    Real.measurable_exp.comp (hSm.const_mul β).neg
  have hint : IntegrableOn (fun x => Real.exp (-(β * S x))) A μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hmeas.aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg hβ (hS x))
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun x => (Real.exp_pos _).le) hint]
  have hsupp : Function.support (fun x => Real.exp (-(β * S x))) = Set.univ :=
    Set.eq_univ_of_forall fun x => (Real.exp_pos _).ne'
  rw [hsupp, Set.univ_inter]
  exact hA

omit [IsFiniteMeasure μ] in
/-- A set containing a nonempty open set has positive measure, for a measure that charges open
sets (Haar measure on a compact group does). -/
theorem measure_pos_of_open [TopologicalSpace Ω] [μ.IsOpenPosMeasure] {A U : Set Ω}
    (hU : IsOpen U) (hne : U.Nonempty) (hUA : U ⊆ A) : 0 < μ A :=
  lt_of_lt_of_le (hU.measure_pos μ hne) (measure_mono hUA)

/-- **`θ = 0` is the unique least-cost vacuum** once the trivial and the unit winding sectors each
contain a nonempty open set of histories. -/
theorem theta_zero_unique [TopologicalSpace Ω] [μ.IsOpenPosMeasure] {β : ℝ} {S : Ω → ℝ}
    (hβ : 0 ≤ β) (hS : ∀ x, 0 ≤ S x) (hSm : Measurable S)
    (sector : ℤ → Set Ω) (T : Finset ℤ) (h0 : (0 : ℤ) ∈ T) (h1 : (1 : ℤ) ∈ T)
    {U₀ U₁ : Set Ω} (hU₀ : IsOpen U₀) (hne₀ : U₀.Nonempty) (hsub₀ : U₀ ⊆ sector 0)
    (hU₁ : IsOpen U₁) (hne₁ : U₁.Nonempty) (hsub₁ : U₁ ⊆ sector 1)
    (θ : ℝ) (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi) (hne : θ ≠ 0) :
    ‖HermitianMass.Z T (fun n => weight μ β S (sector n)) θ‖ <
      ∑ n ∈ T, weight μ β S (sector n) :=
  VacuumModulus.strict_modulus T _ (fun n => weight_nonneg μ β S (sector n)) h0 h1
    (weight_pos μ hβ hS hSm (measure_pos_of_open μ hU₀ hne₀ hsub₀))
    (weight_pos μ hβ hS hSm (measure_pos_of_open μ hU₁ hne₁ hsub₁)) θ hθ hne

end PMConstants.WindingWeights
