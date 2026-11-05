import PMAction.SummedReference
import PMConstants.ReferenceStiffness
import PMConstants.EventStiffness

/-!
# All three gauge couplings from the event-priced D₄ chain

Paper II's `SummedReference`: if every refresh reads all `r` states of its reference, the
event-priced D₄ action converges to `(toll·m·W/4) Σ‖F E‖²_F`; in components with reference
trace `κ_R` the canonical coupling is `g² = 1/(κ_R·toll·m·W)` (`chainCoupling`). The reference
multiplicity drops out.

Charge-unit references have `κ_R = 1/2`: the lepton doublet for weak and hypercharge
(`ReferenceStiffness.doublet_weak_trace`, `doublet_hyper_trace`) and a fundamental colour
triplet for colour (`colour_limit` takes its trace normalization as hypothesis). Then:

* `chain_electric`: `e² = g²g'²/(g² + g'²) = 2/(toll·m·N_sys)`.
* `chain_mixing`: `g'²/(g² + g'²) = clockRatio = 1849/8295`.
* `chain_calibration`: `e² = 4πα` fixes `toll·m = 1/(2πα N_sys)`.
* `chain_couplings`: then `g_W² = 4πα N_sys/43`, `g_Y² = 4πα N_sys/(129+5+16η)`,
  `g_3² = 4πα N_sys/(12η)`: exactly `EventStiffness.couplings_from_alpha`.
* `chain_strong_ratio`: `α_s/α = g_3²/e² = N_sys/(12η)`, the current strong formula.
* `mean_read_strong_factor`: with the mean read instead, the reference multiplicities
  (`2` for the doublet, `3` for the triplet) no longer cancel and the strong ratio is
  multiplied by `3/2`; the electroweak mixing is unchanged. So the current strong formula
  selects the summed read.

Premises (not derived): pricing by the common readout event, summed reads of charge-unit
references (`L` for both electroweak refreshes, a colour triplet for colour), the ledgers
and cubic link consistency.
-/

noncomputable section
namespace PMConstants.ChainCouplings
open Matrix PMAction VaryingFields LinkConsistency ReferenceSampling SummedReference
open scoped Matrix.Norms.L2Operator

/-- Canonical summed-read coupling `g² = 1/(κ_R·toll·m·W)`. -/
def chainCoupling (κ toll : ℝ) (m : ℕ) (W : ℝ) : ℝ := 1 / (κ * toll * m * W)

theorem chain_canonical {toll κ W g : ℝ} {m : ℕ} (ht : 0 < toll) (hm : 0 < m)
    (hκ : 0 < κ) (hW : 0 < W) (hg : g ≠ 0) :
    (toll * m * W / 4) * (κ * g ^ 2) = 1 / 4 ↔ g ^ 2 = chainCoupling κ toll m W :=
  sum_canonical_iff ht hm hκ hW hg

lemma hf : (0 : ℝ) < footprint - 43 := by norm_num [footprint, overhead]
lemma hfp : (0 : ℝ) < footprint := by norm_num [footprint, overhead]

/-- Electric coupling of the two electroweak refreshes. -/
def electric (toll : ℝ) (m : ℕ) : ℝ :=
  chainCoupling (1 / 2) toll m 43 * chainCoupling (1 / 2) toll m (footprint - 43) /
    (chainCoupling (1 / 2) toll m 43 + chainCoupling (1 / 2) toll m (footprint - 43))

theorem chain_electric {toll : ℝ} {m : ℕ} (ht : 0 < toll) (hm : 0 < m) :
    electric toll m = 2 / (toll * m * footprint) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have := hf
  have := hfp
  simp only [electric, chainCoupling]
  field_simp
  ring

theorem chain_mixing {toll : ℝ} {m : ℕ} (ht : 0 < toll) (hm : 0 < m) :
    chainCoupling (1 / 2) toll m (footprint - 43) /
        (chainCoupling (1 / 2) toll m 43 + chainCoupling (1 / 2) toll m (footprint - 43)) =
      clockRatio := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have := hf
  have := hfp
  simp only [chainCoupling, clockRatio]
  rw [PMSubstrate.E8Values.Delta_eq]
  field_simp
  ring

theorem chain_calibration {toll α : ℝ} {m : ℕ} (ht : 0 < toll) (hm : 0 < m) (hα : 0 < α)
    (he : electric toll m = 4 * Real.pi * α) :
    toll * m = 1 / (2 * Real.pi * α * footprint) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have := hfp
  rw [chain_electric ht hm] at he
  have hp : 0 < 2 * Real.pi * α * footprint := by positivity
  rw [eq_div_iff hp.ne']
  have htm : 0 < toll * m * footprint := by positivity
  field_simp at he
  nlinarith [Real.pi_pos]

/-- **The chain reproduces `EventStiffness.couplings_from_alpha`.** -/
theorem chain_couplings {toll α : ℝ} {m : ℕ} (hα : 0 < α)
    (hcal : toll * m = 1 / (2 * Real.pi * α * footprint)) :
    chainCoupling (1 / 2) toll m 43 = 4 * Real.pi * α * footprint / 43 ∧
      chainCoupling (1 / 2) toll m (129 + 5 + 16 * overhead) =
        4 * Real.pi * α * footprint / (129 + 5 + 16 * overhead) ∧
      chainCoupling (1 / 2) toll m ColourChannels.colourLedger =
        4 * Real.pi * α * footprint / ColourChannels.colourLedger := by
  have := hfp
  have hc : (0 : ℝ) < ColourChannels.colourLedger := by
    rw [ColourChannels.colour_ledger]; norm_num
  have hy : (0 : ℝ) < 129 + 5 + 16 * overhead := by norm_num [overhead]
  have e : ∀ W : ℝ, chainCoupling (1 / 2) toll m W = 2 / (toll * m * W) := fun W => by
    simp only [chainCoupling]; field_simp
  simp only [e, hcal]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- The hypercharge ledger is `N_sys − 43`. -/
theorem hyper_ledger : footprint - 43 = 129 + 5 + 16 * overhead := by
  norm_num [footprint]; ring

/-- **Strong-to-electric ratio from the chain:** `α_s/α = N_sys/(12η)`. -/
theorem chain_strong_ratio {toll : ℝ} {m : ℕ} (ht : 0 < toll) (hm : 0 < m) :
    chainCoupling (1 / 2) toll m ColourChannels.colourLedger / electric toll m =
      footprint / ColourChannels.colourLedger := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have := hfp
  have hc : (0 : ℝ) < ColourChannels.colourLedger := by
    rw [ColourChannels.colour_ledger]; norm_num
  rw [chain_electric ht hm]
  simp only [chainCoupling]
  field_simp

/-- **Mean reads instead.** Couplings are `r/(κ·toll·m·W)` (`GaugeGroupFactor.eventCoupling`);
with the doublet (`r = 2`) for electroweak and the triplet (`r = 3`) for colour the strong ratio
gains the factor `3/2`, while the mixing is unchanged. -/
theorem mean_read_strong_factor {toll : ℝ} {m : ℕ} (ht : 0 < toll) (hm : 0 < m) :
    GaugeGroupFactor.eventCoupling 3 (1 / 2) toll m ColourChannels.colourLedger /
        (GaugeGroupFactor.eventCoupling 2 (1 / 2) toll m 43 *
            GaugeGroupFactor.eventCoupling 2 (1 / 2) toll m (footprint - 43) /
          (GaugeGroupFactor.eventCoupling 2 (1 / 2) toll m 43 +
            GaugeGroupFactor.eventCoupling 2 (1 / 2) toll m (footprint - 43))) =
      3 / 2 * (footprint / ColourChannels.colourLedger) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have := hf
  have := hfp
  have hc : (0 : ℝ) < ColourChannels.colourLedger := by
    rw [ColourChannels.colour_ledger]; norm_num
  simp only [GaugeGroupFactor.eventCoupling]
  field_simp
  ring

/-- **Colour limit.** A `C^{1,1}` `su(3)` connection whose field strength at `x` is
`g Σ_a f^a_{μν} i Tᵃ` with fundamental charge-unit generators (`tr TᵃTᵇ = δᵃᵇ/2`), links
cubically consistent with it, and summed reads of the triplet: the event-priced density
converges to `(toll·m·W/4)·(g²/2)·Σ(f^a_{μν})²`, canonical iff `g² = 2/(toll·m·W)`. -/
theorem colour_limit {G : Type*} [Fintype G] [DecidableEq G]
    {A : V → V →L[ℝ] Matrix (Fin 3) (Fin 3) ℂ}
    {DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin 3) (Fin 3) ℂ)} {x : V} {L K : ℝ}
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hL0 : 0 ≤ L)
    (hL : ∀ y, ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    (hskew : ∀ y v, star (A y v) = -A y v)
    (U : V → V → ℝ → Matrix (Fin 3) (Fin 3) ℂ) (hU : ∀ y v h, U y v h ∈ unitary _)
    (hK : 0 ≤ K) (hc : CubicConsistent U A x K) (toll : ℝ) (m : ℕ) (W g : ℝ)
    (T : G → Matrix (Fin 3) (Fin 3) ℂ) (hT : ∀ a, (T a)ᴴ = T a)
    (htr : ∀ a b, trace (T a * T b) = if a = b then ((1 / 2 : ℝ) : ℂ) else 0)
    (f : Fin 4 → Fin 4 → G → ℝ)
    (hF : ∀ μ ν, fieldStrength A DA x μ ν = ∑ a, ((g * f μ ν a : ℝ) : ℂ) • (Complex.I • T a)) :
    Filter.Tendsto (fun h => sumDensity U x (1 : Matrix (Fin 3) (Fin 3) ℂ) toll m W h)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((toll * m * W / 4) * ((1 / 2) * g ^ 2 * ∑ μ, ∑ ν, ∑ a, f μ ν a ^ 2))) := by
  have h := sum_limit (r := 3) hA hL0 hL hskew U hU hK hc 1 (by simp) (by norm_num) toll m W
  have htr' : ∀ a b, trace ((1 : Matrix (Fin 3) (Fin 3) ℂ)ᴴ * (T a * T b) * 1) =
      if a = b then ((1 / 2 : ℝ) : ℂ) else 0 := fun a b => by simpa using htr a b
  have e : (∑ μ, ∑ ν, ∑ i, ∑ k,
      ‖(fieldStrength A DA x μ ν * 1 : Matrix (Fin 3) (Fin 3) ℂ) i k‖ ^ 2) =
      (1 / 2) * g ^ 2 * ∑ μ, ∑ ν, ∑ a, f μ ν a ^ 2 := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    rw [hF, ref_generators 1 T hT (1 / 2) htr' g (f μ ν), Finset.mul_sum]
  rwa [e] at h

end PMConstants.ChainCouplings
