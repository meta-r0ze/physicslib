import PMAction.LinkConsistency
import PMAction.CommonResponse
import PMConstants.EventStiffness
import PMConstants.GaugeReadoutWeights

/-!
# Gauge group factors from the event-priced D₄ action

`GaugeStiffness` takes `β = c₀W` and Paper II's Abelian normalization `g² = 1/(2β)` for every
sector and leaves the non-Abelian group factor as part of its premise. Here the triangle
holonomies of any unitary link family are priced by Paper II's common readout event
(`CommonResponse.stateFlag`, toll and repair length `m`, `W` refreshes), with the reference
carrier sampled uniformly over the `N` basis carriers, and summed with the D₄ per-volume
weight `1/12`.

* `avg_flag`: the sampled flag of a unitary holonomy `P` is `Re tr(1 − P)/(2N)`.
* `event_density_eq`: the event-priced density is the D₄ link density with
  `β = toll·m·W/(2N) = c₀W/N`.
* `event_limit`: for cubically consistent links of a `C^{1,1}` `u(N)` connection
  (`LinkConsistency`), the event-priced density converges to `(c₀W/(2N)) Σ_{μν}‖F_{μν}‖²_F`.
* `frobenius_generators`: `‖g Σ_a f_a (iTᵃ)‖²_F = κ g² Σ_a f_a²` for `tr TᵃTᵇ = κ δᵃᵇ`;
  `event_limit_components` states the limit in components.
* `mean_square_rule`: for one Abelian generator, the Abelian rule holds exactly when the
  mean-square sampled charge `κ/N` is one.
* `canonical_iff`: writing `‖F‖²_F = κ g² Σ_a (F^a)²` (generators with `tr TᵃTᵇ = κ δᵃᵇ`),
  the limit is the canonical `¼ Σ (F^a)²` exactly when `g² = N/(κ·toll·m·W)`.
* `abelian_case`: `N = 1`, `κ = 1` gives `g² = 1/(toll·m·W)`, which is
  `EventStiffness.coupling_from_events`. The Abelian event-stiffness rule is thus the
  continuum limit of the event-priced D₄ action, for varying fields too.
* `fundamental_factor`: in charge units on the fundamental (`κ = 1/2`) the same pricing gives
  `g² = 2N · GaugeStiffness.gsq (c₀W)`: factor `4` for `SU(2)`, `6` for `SU(3)` relative to the
  Abelian rule. `summed_sampler`: summing instead of averaging over carriers removes the `N`,
  leaving the factor `2`.

* `uniform_packet_mixing`: on the sixteen-carrier packet with the actual trace indices and
  current ledgers, the event-priced couplings give exactly the uniform-readout mixing
  `5547/37777` of `GaugeReadoutWeights`, not the manuscript value.

Premises (not derived; the common toll is PM's cost definition, `PMSubstrate.NetCost`, so
the open part of the pricing is the common repair length `m`):
the pricing of holonomies by the common readout event, the uniform
carrier sampler, the refresh count `W`, the generator normalization `κ`, and cubic link
consistency. No coupling value is changed here. (`CompactCouplings.event_limit_c2` replaces the
`C^{1,1}` and cubic-consistency premises by: the links are the transports of a compactly
supported C² connection.)
-/

noncomputable section
namespace PMConstants.GaugeGroupFactor
open Matrix PMAction VaryingFields LinkConsistency CommonResponse
open scoped Matrix.Norms.L2Operator

variable {N : ℕ}

/-- Uniformly sampled readout flag over the `N` basis carriers. -/
def avgFlag (P : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (∑ a : Fin N, stateFlag P (Pi.single a 1)) / N

theorem avg_flag (P : Matrix (Fin N) (Fin N) ℂ) (hP : P ∈ unitary (Matrix (Fin N) (Fin N) ℂ)) :
    avgFlag P = (trace (1 - P)).re / (2 * N) := by
  unfold avgFlag
  simp_rw [basis_case P hP, InterferenceReadout.flag_formula P hP]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  simp [trace, Finset.sum_sub_distrib, Complex.re_sum]
  ring

/-- Event-priced D₄ density: `W` refreshes per triangle, each a sampled readout flag repaired
by `m` events at the common toll, with per-volume weight `1/12`. -/
def eventDensity (U : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ) (x : V) (toll : ℝ) (m : ℕ)
    (W h : ℝ) : ℝ :=
  (1 / 12) * ∑ p ∈ D4Gauge.tri,
    W * responseCost toll m (avgFlag (holonomy U x (rv p.1) (rv p.2) h)) / h ^ 4

lemma holonomy_unitary (U : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ)
    (hU : ∀ y v h, U y v h ∈ unitary (Matrix (Fin N) (Fin N) ℂ)) (x a b : V) (h : ℝ) :
    holonomy U x a b h ∈ unitary (Matrix (Fin N) (Fin N) ℂ) := by
  unfold holonomy
  exact (unitary _).mul_mem ((unitary _).mul_mem (hU _ _ _) (hU _ _ _)) (Unitary.star_mem (hU _ _ _))

/-- **The event-priced density is the D₄ link density with `β = toll·m·W/(2N)`.** -/
theorem event_density_eq (U : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ)
    (hU : ∀ y v h, U y v h ∈ unitary (Matrix (Fin N) (Fin N) ℂ)) (x : V) (toll : ℝ) (m : ℕ)
    (W h : ℝ) :
    eventDensity U x toll m W h = linkDensity U x (toll * m * W / (2 * N)) h := by
  unfold eventDensity linkDensity
  simp only [avg_flag _ (holonomy_unitary U hU _ _ _ _), responseCost]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- **Continuum limit of the event-priced action.** -/
theorem event_limit {A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {x : V} {L K : ℝ}
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hL0 : 0 ≤ L)
    (hL : ∀ y, ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    (hskew : ∀ y v, star (A y v) = -A y v)
    (U : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ)
    (hU : ∀ y v h, U y v h ∈ unitary (Matrix (Fin N) (Fin N) ℂ))
    (hK : 0 ≤ K) (hc : CubicConsistent U A x K) (toll : ℝ) (m : ℕ) (W : ℝ) :
    Filter.Tendsto (fun h => eventDensity U x toll m W h) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((toll * m * W / (2 * N) / 2) *
        ∑ μ, ∑ ν, ∑ i, ∑ j, ‖fieldStrength A DA x μ ν i j‖ ^ 2)) := by
  have := d4_link_tendsto hA hL0 hL hskew U hU hK hc (toll * m * W / (2 * N))
  simpa only [event_density_eq U hU] using this

/-- **Canonical normalization.** With `Σ‖F‖²_F = κ g² Σ_a (F^a)²`, the limit
`(β/2)·κ g² Σ (F^a)²` equals the canonical `¼ Σ (F^a)²` exactly when `g² = N/(κ·toll·m·W)`. -/
theorem canonical_iff {toll κ W g : ℝ} {m : ℕ} (hN : 0 < N) (ht : 0 < toll) (hm : 0 < m)
    (hκ : 0 < κ) (hW : 0 < W) (hg : g ≠ 0) :
    (toll * m * W / (2 * N) / 2) * (κ * g ^ 2) = 1 / 4 ↔ g ^ 2 = N / (κ * toll * m * W) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hg2 : 0 < g ^ 2 := by positivity
  constructor
  · intro h
    field_simp
    field_simp at h
    linarith
  · intro h
    rw [h]
    field_simp
    norm_num

/-- **Abelian case:** `N = 1`, unit charge reproduces `EventStiffness.coupling_from_events`. -/
theorem abelian_case (toll : ℝ) (m : ℕ) (W : ℝ) :
    ((1 : ℕ) : ℝ) / (1 * toll * m * W) = GaugeStiffness.gsq (EventStiffness.c0 toll m * W) := by
  rw [EventStiffness.coupling_from_events]; simp

/-- **Fundamental representation in charge units** (`κ = 1/2`): factor `2N` relative to the
Abelian rule used in `GaugeStiffness`. -/
theorem fundamental_factor (toll : ℝ) (m : ℕ) (W : ℝ) :
    (N : ℝ) / ((1 / 2) * toll * m * W) =
      2 * N * GaugeStiffness.gsq (EventStiffness.c0 toll m * W) := by
  rw [EventStiffness.coupling_from_events]
  by_cases h : toll * m * W = 0
  · have h' : (1 / 2) * toll * m * W = 0 := by
      rw [show (1 / 2) * toll * m * W = (1 / 2) * (toll * m * W) by ring, h, mul_zero]
    rw [h', h]; simp
  · field_simp

theorem su2_factor (toll : ℝ) (m : ℕ) (W : ℝ) :
    ((2 : ℕ) : ℝ) / ((1 / 2) * toll * m * W) =
      4 * GaugeStiffness.gsq (EventStiffness.c0 toll m * W) := by
  rw [fundamental_factor]; norm_num

theorem su3_factor (toll : ℝ) (m : ℕ) (W : ℝ) :
    ((3 : ℕ) : ℝ) / ((1 / 2) * toll * m * W) =
      6 * GaugeStiffness.gsq (EventStiffness.c0 toll m * W) := by
  rw [fundamental_factor]; norm_num

/-- **Summed sampler.** Summing the flags over the `N` carriers instead of averaging multiplies
`β` by `N`; the coupling condition becomes `g² = 1/(κ·toll·m·W)`, so the fundamental charge-unit
factor is `2` for every `N`. -/
theorem summed_sampler (P : Matrix (Fin N) (Fin N) ℂ) (hP : P ∈ unitary (Matrix (Fin N) (Fin N) ℂ))
    (hN : 0 < N) :
    (∑ a : Fin N, stateFlag P (Pi.single a 1)) = N * ((trace (1 - P)).re / (2 * N)) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [← avg_flag P hP, avgFlag]
  field_simp

/-! ## The generator trace identity behind `κ` -/

lemma frob_trace (M : Matrix (Fin N) (Fin N) ℂ) :
    ∑ i, ∑ j, ‖M i j‖ ^ 2 = (trace (Mᴴ * M)).re := by
  simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  ring

/-- **Frobenius norm in generator components.** For Hermitian generators with
`tr(TᵃTᵇ) = κ δᵃᵇ` and real components, `‖g Σ_a f_a (i Tᵃ)‖²_F = κ g² Σ_a f_a²`. -/
theorem frobenius_generators {G : Type*} [Fintype G] [DecidableEq G]
    (T : G → Matrix (Fin N) (Fin N) ℂ) (hT : ∀ a, (T a)ᴴ = T a) (κ : ℝ)
    (htr : ∀ a b, trace (T a * T b) = if a = b then (κ : ℂ) else 0) (g : ℝ) (f : G → ℝ) :
    ∑ i, ∑ j, ‖(∑ a, ((g * f a : ℝ) : ℂ) • (Complex.I • T a)) i j‖ ^ 2 =
      κ * g ^ 2 * ∑ a, f a ^ 2 := by
  rw [frob_trace]
  have hM : (∑ a, ((g * f a : ℝ) : ℂ) • (Complex.I • T a))ᴴ =
      ∑ a, ((g * f a : ℝ) : ℂ) • (-Complex.I • T a) := by
    rw [conjTranspose_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [conjTranspose_smul, conjTranspose_smul, hT]
    simp [Complex.conj_ofReal, smul_smul]
  rw [hM, Finset.sum_mul, trace_sum]
  simp_rw [Finset.mul_sum, trace_sum, smul_mul_smul, trace_smul, htr]
  simp only [smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hI : -Complex.I * Complex.I = 1 := by rw [neg_mul, Complex.I_mul_I, neg_neg]
  rw [hI, one_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- **Abelian rule from mean-square charge.** For one diagonal Abelian generator with charges
`q`, `κ = Σ_k q_k²`; the event-priced coupling `N/(κ·toll·m·W)` equals the Abelian rule
`GaugeStiffness.gsq (c₀W)` exactly when the mean-square sampled charge is one. -/
theorem mean_square_rule {toll W κ : ℝ} {m : ℕ} (hN : 0 < N) (hp : toll * m * W ≠ 0)
    (hκ : κ ≠ 0) :
    (N : ℝ) / (κ * toll * m * W) = GaugeStiffness.gsq (EventStiffness.c0 toll m * W) ↔
      κ / N = 1 := by
  rw [EventStiffness.coupling_from_events]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have e : κ * toll * m * W = κ * (toll * m * W) := by ring
  rw [e, div_eq_div_iff (mul_ne_zero hκ hp) hp, div_eq_one_iff_eq hN']
  constructor
  · intro h
    have := mul_right_cancel₀ hp (by linarith [h] : (N : ℝ) * (toll * m * W) = κ * (toll * m * W))
    exact this.symm
  · intro h; rw [h]; ring

/-- **Event-priced limit in generator components.** If the field strength at `x` has
components `F_{μν} = g Σ_a f^a_{μν} (i Tᵃ)` with `tr(TᵃTᵇ) = κ δᵃᵇ`, the event-priced density
converges to `(toll·m·W/(4N)) · κ g² Σ_{μν} Σ_a (f^a_{μν})²`; by `canonical_iff` this is the
canonical Yang–Mills density exactly when `g² = N/(κ·toll·m·W)`. -/
theorem event_limit_components {G : Type*} [Fintype G] [DecidableEq G]
    {A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {x : V} {L K : ℝ}
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hL0 : 0 ≤ L)
    (hL : ∀ y, ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    (hskew : ∀ y v, star (A y v) = -A y v)
    (U : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ)
    (hU : ∀ y v h, U y v h ∈ unitary (Matrix (Fin N) (Fin N) ℂ))
    (hK : 0 ≤ K) (hc : CubicConsistent U A x K) (toll : ℝ) (m : ℕ) (W : ℝ)
    (T : G → Matrix (Fin N) (Fin N) ℂ) (hT : ∀ a, (T a)ᴴ = T a) (κ : ℝ)
    (htr : ∀ a b, trace (T a * T b) = if a = b then (κ : ℂ) else 0) (g : ℝ)
    (f : Fin 4 → Fin 4 → G → ℝ)
    (hF : ∀ μ ν, fieldStrength A DA x μ ν = ∑ a, ((g * f μ ν a : ℝ) : ℂ) • (Complex.I • T a)) :
    Filter.Tendsto (fun h => eventDensity U x toll m W h) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((toll * m * W / (2 * N) / 2) * (κ * g ^ 2 * ∑ μ, ∑ ν, ∑ a, f μ ν a ^ 2))) := by
  have h := event_limit hA hL0 hL hskew U hU hK hc toll m W
  have e : (∑ μ, ∑ ν, ∑ i, ∑ j, ‖fieldStrength A DA x μ ν i j‖ ^ 2) =
      κ * g ^ 2 * ∑ μ, ∑ ν, ∑ a, f μ ν a ^ 2 := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    rw [hF, frobenius_generators T hT κ htr g (f μ ν), Finset.mul_sum]
  rwa [e] at h

/-! ## Electroweak mixing from the event-priced D₄ chain -/

/-- Event-priced coupling of a sector: `N` sampled carriers, packet trace index `κ`, refresh
ledger `W` (from `canonical_iff`). -/
def eventCoupling (n : ℝ) (κ toll : ℝ) (m : ℕ) (W : ℝ) : ℝ := n / (κ * toll * m * W)

/-- **The chain gives exactly the uniform-readout mixing.** On the sixteen-carrier packet with
the actual trace indices (`2` weak, `10/3` for `Y/2`) and the current ledgers (`43`,
`N_sys − 43`), the event-priced couplings of `canonical_iff` give
`g'²/(g² + g'²) = GaugeReadoutWeights.mixing uniformWeights = 5547/37777`, independent of the
common toll·m. The manuscript value therefore needs a non-uniform readout preparation
(`GaugeReadoutWeights.target_mixing_iff`) or different ledgers; the continuum chain does not
supply it. -/
theorem uniform_packet_mixing {toll : ℝ} {m : ℕ} (ht : 0 < toll) (hm : 0 < m) :
    eventCoupling 16 (10 / 3) toll m (footprint - 43) /
        (eventCoupling 16 2 toll m 43 + eventCoupling 16 (10 / 3) toll m (footprint - 43)) =
      GaugeReadoutWeights.mixing GaugeReadoutWeights.uniformWeights ∧
    GaugeReadoutWeights.mixing GaugeReadoutWeights.uniformWeights = 5547 / 37777 := by
  refine ⟨?_, GaugeReadoutWeights.uniform_mixing⟩
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hf : (0 : ℝ) < footprint - 43 := by norm_num [footprint, overhead]
  have htm : 0 < toll * m := by positivity
  simp only [eventCoupling, GaugeReadoutWeights.mixing, GaugeReadoutWeights.weakIndex,
    GaugeReadoutWeights.hyperIndex, GaugeReadoutWeights.uniformWeights]
  field_simp
  ring

end PMConstants.GaugeGroupFactor
