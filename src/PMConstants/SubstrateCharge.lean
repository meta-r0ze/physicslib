import PMConstants.WindingWeights
import PMAction.InertiaStability

/-!
# The winding charge from the substrate, without Lüscher's construction

`WindingWeights.theta_zero_admissible` needs an integer charge that is continuous on an open set of
admissible histories, with histories of charge `0` and `1`; it cites Lüscher's lattice charge for
that. The substrate supplies its own.

A history `x` carries the Hermitian operator `H x` whose filled (negative) modes count the carriers
on a wall (`PMAction.WallTransfer`). The charge is the transfer count relative to the trivial
history, `negCount (H x) − N₀`.

* `admissible_open`: the histories where `H x` is invertible (no mode at zero) form an open set.
* `charge_continuous`: on them the charge is locally constant, hence continuous
  (`PMAction.InertiaStability.negCount_locallyConstant`, Sylvester's law of inertia). It can change
  only where a mode crosses zero: the substrate's exceptional set.
* `theta_zero_substrate`: so `θ = 0` is the unique least-cost vacuum, given an invertible history
  with one more filled mode than the trivial one.

What remains is that existence (a unit-transfer history on a finite region); Lüscher's charge is no
longer needed.
-/

noncomputable section
namespace PMConstants.SubstrateCharge
open MeasureTheory PMAction.InertiaStability

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Invertible histories form an open set.** -/
theorem admissible_open {Ω : Type*} [TopologicalSpace Ω] (H : Ω → Matrix n n ℂ)
    (hc : Continuous H) : IsOpen {x | (H x).det ≠ 0} :=
  (hc.matrix_det).isOpen_preimage _ isOpen_compl_singleton

/-- The transfer charge relative to `N₀` filled modes. -/
def charge {Ω : Type*} (H : Ω → Matrix n n ℂ) (hherm : ∀ x, (H x).IsHermitian) (N₀ : ℕ)
    (x : {x | (H x).det ≠ 0}) : ℤ :=
  (negCount (hherm x.1) : ℤ) - N₀

/-- **The transfer charge is continuous on invertible histories.** -/
theorem charge_continuous {Ω : Type*} [TopologicalSpace Ω] (H : Ω → Matrix n n ℂ)
    (hc : Continuous H) (hherm : ∀ x, (H x).IsHermitian) (N₀ : ℕ) :
    Continuous (charge H hherm N₀) := by
  have hl := negCount_locallyConstant (X := {x | (H x).det ≠ 0}) (fun x => H x.1)
    (hc.comp continuous_subtype_val) (fun x => hherm x.1) (fun x => x.2)
  exact (hl.comp fun k : ℕ => (k : ℤ) - N₀).continuous

/-- **`θ = 0` from the substrate's own charge.** -/
theorem theta_zero_substrate {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] {β : ℝ} {S : Ω → ℝ}
    (hβ : 0 ≤ β) (hS : ∀ x, 0 ≤ S x) (hSm : Measurable S)
    (H : Ω → Matrix n n ℂ) (hc : Continuous H) (hherm : ∀ x, (H x).IsHermitian) (N₀ : ℕ)
    (x₀ x₁ : Ω) (hd₀ : (H x₀).det ≠ 0) (hd₁ : (H x₁).det ≠ 0)
    (hq₀ : negCount (hherm x₀) = N₀) (hq₁ : negCount (hherm x₁) = N₀ + 1)
    (T : Finset ℤ) (h0 : (0 : ℤ) ∈ T) (h1 : (1 : ℤ) ∈ T)
    (θ : ℝ) (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi) (hne : θ ≠ 0) :
    ‖HermitianMass.Z T (fun k => WindingWeights.weight μ β S
        (WindingWeights.chargeSector {x | (H x).det ≠ 0} (charge H hherm N₀) k)) θ‖ <
      ∑ k ∈ T, WindingWeights.weight μ β S
        (WindingWeights.chargeSector {x | (H x).det ≠ 0} (charge H hherm N₀) k) :=
  WindingWeights.theta_zero_admissible μ hβ hS hSm (admissible_open H hc) (charge H hherm N₀)
    (charge_continuous H hc hherm N₀) ⟨x₀, hd₀⟩ ⟨x₁, hd₁⟩
    (by simp [charge, hq₀]) (by simp [charge, hq₁]) T h0 h1 θ hθ hne

end PMConstants.SubstrateCharge
