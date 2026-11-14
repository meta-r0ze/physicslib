import PMConstants.SubstrateCharge
import PMAction.WilsonCertificate

/-!
# The unit-winding witness from an inertia certificate

`SubstrateCharge.theta_zero_substrate` needs two invertible histories whose negative-mode counts
are `N₀` and `N₀ + 1`. `PMAction.WilsonCertificate.wilson_certificate` reduces each of those to an
inequality and sign check on `B = Qᴴ H Q`.

* `witness_of_certificate`: a strictly row-dominant `B = Qᴴ H Q` with `N` negative diagonal entries
  gives `det H ≠ 0` and `negCount H = N`.
* `theta_zero_of_certificates`: so `theta_zero_substrate` holds with its four count hypotheses
  replaced by two certificates.

**External premise** (the only numerical input). For the two Wilson kernels of
`tools/unit_transfer_certificate.py` (`L = 3`, the trivial history and the unit history
`(n₁₂, n₃₄) = (1, −1)`, dimension `324`), there are `Q₀`, `Q₁` with `Bᵢ = Qᵢᴴ H Qᵢ` strictly
row-dominant, with `162` and `163` negative diagonal entries. The script checks these inequalities
and signs in ball arithmetic (python-flint, 128 bits; floating point only proposes `Q`); the 9th-root
phases at `L = 3` make an exact check in Lean's kernel impractical (`L = 2`, where the phases are
Gaussian, has no index: `32` and `32`). Still a premise as well: that the script's matrices are the
library's two backgrounds (the Wilson kernel `γ₅(D_W − M)` at `M = r = 1` of `PMAction.DomainWall`,
with the link transports of `PMAction.Machine.MatterContinuum`). The vacuum-selection premise of
`ThetaBarSelection` stays separate.
-/

noncomputable section
namespace PMConstants.UnitTransferWitness
open MeasureTheory Matrix Finset PMAction.InertiaStability PMAction.InertiaCertificate

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **A certificate fixes invertibility and the negative-mode count.** -/
theorem witness_of_certificate {H Q B : Matrix n n ℂ} (hH : H.IsHermitian)
    (basis : B = Qᴴ * H * Q) (gap : ∀ i, ∑ j ∈ univ.erase i, ‖B i j‖ < ‖B i i‖) (N : ℕ)
    (hcount : (univ.filter fun i => (B i i).re < 0).card = N) :
    H.det ≠ 0 ∧ negCount hH = N := by
  obtain ⟨h1, h2⟩ := wilson_certificate hH basis gap
  exact ⟨h1, h2.trans hcount⟩

/-- **`θ = 0` from two inertia certificates.** -/
theorem theta_zero_of_certificates {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] {β : ℝ} {S : Ω → ℝ}
    (hβ : 0 ≤ β) (hS : ∀ x, 0 ≤ S x) (hSm : Measurable S)
    (H : Ω → Matrix n n ℂ) (hc : Continuous H) (hherm : ∀ x, (H x).IsHermitian) (N₀ : ℕ)
    (x₀ x₁ : Ω) (Q₀ B₀ Q₁ B₁ : Matrix n n ℂ)
    (hb₀ : B₀ = Q₀ᴴ * H x₀ * Q₀) (hg₀ : ∀ i, ∑ j ∈ univ.erase i, ‖B₀ i j‖ < ‖B₀ i i‖)
    (hn₀ : (univ.filter fun i => (B₀ i i).re < 0).card = N₀)
    (hb₁ : B₁ = Q₁ᴴ * H x₁ * Q₁) (hg₁ : ∀ i, ∑ j ∈ univ.erase i, ‖B₁ i j‖ < ‖B₁ i i‖)
    (hn₁ : (univ.filter fun i => (B₁ i i).re < 0).card = N₀ + 1)
    (T : Finset ℤ) (h0 : (0 : ℤ) ∈ T) (h1 : (1 : ℤ) ∈ T)
    (θ : ℝ) (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi) (hne : θ ≠ 0) :
    ‖HermitianMass.Z T (fun k => WindingWeights.weight μ β S
        (WindingWeights.chargeSector {x | (H x).det ≠ 0}
          (SubstrateCharge.charge H hherm N₀) k)) θ‖ <
      ∑ k ∈ T, WindingWeights.weight μ β S
        (WindingWeights.chargeSector {x | (H x).det ≠ 0}
          (SubstrateCharge.charge H hherm N₀) k) := by
  obtain ⟨hd₀, hq₀⟩ := witness_of_certificate (hherm x₀) hb₀ hg₀ N₀ hn₀
  obtain ⟨hd₁, hq₁⟩ := witness_of_certificate (hherm x₁) hb₁ hg₁ (N₀ + 1) hn₁
  exact SubstrateCharge.theta_zero_substrate μ hβ hS hSm H hc hherm N₀ x₀ x₁ hd₀ hd₁ hq₀ hq₁
    T h0 h1 θ hθ hne

end PMConstants.UnitTransferWitness
