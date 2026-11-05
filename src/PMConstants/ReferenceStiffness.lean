import PMAction.ReferenceSampling
import PMConstants.ReferenceCharge
import PMConstants.GaugeGroupFactor

/-!
# Reference stiffness from the event-priced D₄ continuum limit

`ReferenceCharge` takes as premise that a refresh's stiffness is the comparison response of
its reference carrier, and then shows the lepton-doublet reference gives the manuscript weak
fraction. Paper II's `ReferenceSampling` now derives that premise from the gauge action:
if a sector's `W` refreshes read the orthonormal reference states `E`, the event-priced D₄
density converges to `(toll·m·W/(4r)) Σ‖F E‖²_F`, and in generator components this is the
reference trace `κ_R = tr(Eᴴ TᵃTᵃ E)` times `g²`.

* `canonical_ref_iff`: the reference-sampled limit is canonical exactly when
  `g² = r/(κ_R·toll·m·W)`.
* `doublet_weak_trace`, `doublet_hyper_trace`: on the lepton doublet (`r = 2`, `E = 1`) the
  weak generators `σᵃ/2` have `tr(TᵃTᵇ) = δᵃᵇ/2` and `Y/2 = −1/2` has `tr = 1/2`; these are
  `ReferenceCharge.reference_indices` for `L`: `weakIndex (ref L) = hyperIndex (ref L) = 1/2`.
* `event_mixing`: the event-priced couplings of two sectors give
  `g'²/(g² + g'²) = refMixing κ_W κ_Y`, independent of toll·m.
* `lepton_event_mixing`: with both electroweak refreshes reading the lepton doublet and the
  ledgers `43` and `N_sys − 43`, the chain gives exactly `clockRatio = 1849/8295`.
* `lepton_weak_limit`: the concrete reference-sampled weak limit on the doublet.

Premises (not derived): pricing by the common readout event, both refreshes reading the
reserved lepton-doublet reference (`SharedReference`), the ledgers, and cubic link
consistency. The full 16-carrier embedding is represented by the doublet's own generators.
-/

noncomputable section
namespace PMConstants.ReferenceStiffness
open Matrix PMAction VaryingFields LinkConsistency ReferenceSampling
open scoped Matrix.Norms.L2Operator

/-- **Canonical normalization for a reference-sampled sector.** -/
theorem canonical_ref_iff {r : ℕ} {toll κ W g : ℝ} {m : ℕ} (hr : 0 < r) (ht : 0 < toll)
    (hm : 0 < m) (hκ : 0 < κ) (hW : 0 < W) (hg : g ≠ 0) :
    (toll * m * W / (2 * r) / 2) * (κ * g ^ 2) = 1 / 4 ↔ g ^ 2 = r / (κ * toll * m * W) :=
  GaugeGroupFactor.canonical_iff (N := r) hr ht hm hκ hW hg

/-! ## The lepton doublet -/

/-- Weak generators `σᵃ/2` on the doublet. -/
def weakT : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ := ![
  !![0, 1/2; 1/2, 0], !![0, -Complex.I/2; Complex.I/2, 0], !![1/2, 0; 0, -1/2]]

/-- Hypercharge `Y/2 = −1/2` on the lepton doublet. -/
def hyperT : Fin 1 → Matrix (Fin 2) (Fin 2) ℂ := fun _ => !![-1/2, 0; 0, -1/2]

theorem weakT_hermitian (a : Fin 3) : (weakT a)ᴴ = weakT a := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [weakT, conjTranspose_apply]

theorem hyperT_hermitian (a : Fin 1) : (hyperT a)ᴴ = hyperT a := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hyperT, conjTranspose_apply]

set_option maxHeartbeats 1000000 in
theorem doublet_weak_trace (a b : Fin 3) :
    trace ((1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (weakT a * weakT b) * 1) =
      if a = b then ((1 / 2 : ℝ) : ℂ) else 0 := by
  fin_cases a <;> fin_cases b <;> simp [weakT, trace, Fin.sum_univ_two]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]
  all_goals norm_num

theorem doublet_hyper_trace (a b : Fin 1) :
    trace ((1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (hyperT a * hyperT b) * 1) =
      if a = b then ((1 / 2 : ℝ) : ℂ) else 0 := by
  fin_cases a; fin_cases b
  simp [hyperT, trace, Fin.sum_univ_two]; norm_num

/-- These are Paper III's reference indices of the lepton doublet. -/
theorem traces_are_reference_indices :
    GaugeReadoutWeights.weakIndex (ReferenceCharge.ref .L) = 1 / 2 ∧
      GaugeReadoutWeights.hyperIndex (ReferenceCharge.ref .L) = 1 / 2 := by
  constructor <;>
    norm_num [GaugeReadoutWeights.weakIndex, GaugeReadoutWeights.hyperIndex, ReferenceCharge.ref]

/-- The doublet as its own reference: `E = 1` is an isometry. -/
theorem doublet_isometry : (1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * 1 = 1 := by simp

/-- **Reference-sampled weak limit on the doublet.** For a `C^{1,1}` `su(2)` connection whose
field strength at `x` is `F_{μν} = g Σ_a f^a_{μν} i σᵃ/2`, links cubically consistent with it,
and `W` refreshes reading the doublet, the event-priced density converges to
`(toll·m·W/8)·(g²/2)·Σ_{μν} Σ_a (f^a_{μν})²`. -/
theorem lepton_weak_limit {A : V → V →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ}
    {DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ)} {x : V} {L K : ℝ}
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hL0 : 0 ≤ L)
    (hL : ∀ y, ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    (hskew : ∀ y v, star (A y v) = -A y v)
    (U : V → V → ℝ → Matrix (Fin 2) (Fin 2) ℂ) (hU : ∀ y v h, U y v h ∈ unitary _)
    (hK : 0 ≤ K) (hc : CubicConsistent U A x K) (toll : ℝ) (m : ℕ) (W g : ℝ)
    (f : Fin 4 → Fin 4 → Fin 3 → ℝ)
    (hF : ∀ μ ν, fieldStrength A DA x μ ν = ∑ a, ((g * f μ ν a : ℝ) : ℂ) • (Complex.I • weakT a)) :
    Filter.Tendsto (fun h => refDensity U x (1 : Matrix (Fin 2) (Fin 2) ℂ) toll m W h)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((toll * m * W / (2 * (2 : ℕ)) / 2) *
        ((1 / 2) * g ^ 2 * ∑ μ, ∑ ν, ∑ a, f μ ν a ^ 2))) := by
  have h := ref_limit hA hL0 hL hskew U hU hK hc 1 doublet_isometry toll m W
  have e : (∑ μ, ∑ ν, ∑ i, ∑ k,
      ‖(fieldStrength A DA x μ ν * 1 : Matrix (Fin 2) (Fin 2) ℂ) i k‖ ^ 2) =
      (1 / 2) * g ^ 2 * ∑ μ, ∑ ν, ∑ a, f μ ν a ^ 2 := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    rw [hF, ref_generators 1 weakT weakT_hermitian (1 / 2) doublet_weak_trace g (f μ ν),
      Finset.mul_sum]
  rwa [e] at h

/-! ## Electroweak mixing -/

/-- **Mixing from event-priced reference couplings.** -/
theorem event_mixing {r : ℕ} {toll κW κY : ℝ} {m : ℕ} (hr : 0 < r) (ht : 0 < toll) (hm : 0 < m)
    (hW : 0 < κW) (hY : 0 < κY) :
    GaugeGroupFactor.eventCoupling r κY toll m (footprint - (PMSubstrate.E8Values.Delta : ℝ)) /
        (GaugeGroupFactor.eventCoupling r κW toll m (PMSubstrate.E8Values.Delta : ℝ) +
          GaugeGroupFactor.eventCoupling r κY toll m (footprint - (PMSubstrate.E8Values.Delta : ℝ))) =
      ReferenceCharge.refMixing κW κY := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hf : (0 : ℝ) < footprint - (PMSubstrate.E8Values.Delta : ℝ) := by
    rw [PMSubstrate.E8Values.Delta_eq]
    norm_num [footprint, overhead]
  simp only [GaugeGroupFactor.eventCoupling, ReferenceCharge.refMixing]
  field_simp
  ring

/-- **The lepton-doublet reference gives the manuscript weak fraction from the continuum
chain.** Both refreshes read the doublet (`κ_W = κ_Y = 1/2`, the doublet traces above). -/
theorem lepton_event_mixing {toll : ℝ} {m : ℕ} (ht : 0 < toll) (hm : 0 < m) :
    GaugeGroupFactor.eventCoupling 2 (1 / 2) toll m (footprint - (PMSubstrate.E8Values.Delta : ℝ)) /
        (GaugeGroupFactor.eventCoupling 2 (1 / 2) toll m (PMSubstrate.E8Values.Delta : ℝ) +
          GaugeGroupFactor.eventCoupling 2 (1 / 2) toll m (footprint - (PMSubstrate.E8Values.Delta : ℝ))) = clockRatio ∧
      clockRatio = 1849 / 8295 := by
  constructor
  · have h := event_mixing (r := 2) (κW := 1 / 2) (κY := 1 / 2) (by norm_num) ht hm
      (by norm_num) (by norm_num)
    have h2 : ReferenceCharge.refMixing (1 / 2) (1 / 2) = clockRatio := by
      have h1 := traces_are_reference_indices
      rw [show ReferenceCharge.refMixing (1 / 2) (1 / 2) = ReferenceCharge.refMixing
          (GaugeReadoutWeights.weakIndex (ReferenceCharge.ref .L))
          (GaugeReadoutWeights.hyperIndex (ReferenceCharge.ref .L)) by rw [h1.1, h1.2]]
      exact ReferenceCharge.lepton_reference_mixing
    exact h.trans h2
  · norm_num [clockRatio, footprint, overhead]

end PMConstants.ReferenceStiffness
