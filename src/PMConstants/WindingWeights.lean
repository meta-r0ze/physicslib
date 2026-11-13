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
existence is lattice gauge geometry; the admissible set it lives in is an input (below).

* `chargeSector_open`, `theta_zero_admissible`: a charge that is continuous (locally constant) on
  an open admissible set has open sectors, so the premise becomes "some admissible history has
  charge `1`". Without an admissible set there are no integer sectors at all: the SU(N) link space
  is connected and every lattice pure gauge is gauge-equivalent to the identity
  (`PMAction.MassGap.SlabGeometry`: time is an open path, no winding cycle).

**The admissible set needs no cutoff.** Lüscher's lattice charge (Commun. Math. Phys. 85 (1982);
Phillips–Stone, Commun. Math. Phys. 103 (1986)) is defined on every field outside an
*exceptional* set of measure zero, is an integer, and does not change under deformations that
avoid that set. So `Adm` = the non-exceptional fields: open, of full measure, with `Q` locally
constant, which are exactly the premises above. A hard plaquette bound (Margin) is not needed, and
would conflict with `PMAction.Admission` (a local, conserving, priced factor is admitted unless a
persistence reason excludes it; the repair cost `1 − cos` is finite on every plaquette). For
`U(1)` the exceptional fields are those with some plaquette at `−1`, exactly where the least-cost
repair of the plaquette phase is tied between two directions.

Cited, not formalised here: the construction on PM's region (the literature works on a periodic
box; PM's region sits in the persisting vacuum, so its boundary is pure gauge), and the existence
of a non-exceptional history of charge `1` (every integer sector is nonempty on a large enough
region; the substrate is unbounded).

With quark masses, `ThetaBarSelection` applies the same weights to `θ̄ = θ − arg det M`, so no
sector-exchange (Hermiticity) premise is needed for `θ̄ = 0`.
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

/-! ### Charge sectors on an admissible set

A lattice topological charge is defined on an **admissible** set of histories (every plaquette
within a fixed bound of the identity; Lüscher's construction), open in the full history space, and
is locally constant there. Its sectors are then open, so the open-set premise above reduces to:
each of the charges `0` and `1` is taken by some admissible history. -/

/-- The histories of charge `n`: admissible histories `x` with `Q x = n`. -/
def chargeSector (Adm : Set Ω) (Q : Adm → ℤ) (n : ℤ) : Set Ω := Subtype.val '' (Q ⁻¹' {n})

omit [MeasurableSpace Ω] in
/-- **A locally constant charge on an open admissible set has open sectors.** -/
theorem chargeSector_open [TopologicalSpace Ω] {Adm : Set Ω} (hAdm : IsOpen Adm) (Q : Adm → ℤ)
    (hQ : Continuous Q) (n : ℤ) : IsOpen (chargeSector Adm Q n) :=
  hAdm.isOpenMap_subtype_val _ ((isOpen_discrete {n}).preimage hQ)

/-- **`θ = 0` is the unique least-cost vacuum once an admissible history of charge `1` exists**
(charge `0` is taken by the identity history). -/
theorem theta_zero_admissible [TopologicalSpace Ω] [μ.IsOpenPosMeasure] {β : ℝ} {S : Ω → ℝ}
    (hβ : 0 ≤ β) (hS : ∀ x, 0 ≤ S x) (hSm : Measurable S)
    {Adm : Set Ω} (hAdm : IsOpen Adm) (Q : Adm → ℤ) (hQ : Continuous Q)
    (x₀ x₁ : Adm) (hx₀ : Q x₀ = 0) (hx₁ : Q x₁ = 1)
    (T : Finset ℤ) (h0 : (0 : ℤ) ∈ T) (h1 : (1 : ℤ) ∈ T)
    (θ : ℝ) (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi) (hne : θ ≠ 0) :
    ‖HermitianMass.Z T (fun n => weight μ β S (chargeSector Adm Q n)) θ‖ <
      ∑ n ∈ T, weight μ β S (chargeSector Adm Q n) :=
  theta_zero_unique μ hβ hS hSm (chargeSector Adm Q) T h0 h1
    (chargeSector_open hAdm Q hQ 0) ⟨_, x₀, hx₀, rfl⟩ subset_rfl
    (chargeSector_open hAdm Q hQ 1) ⟨_, x₁, hx₁, rfl⟩ subset_rfl θ hθ hne

end PMConstants.WindingWeights
