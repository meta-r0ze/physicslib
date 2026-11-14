import PMAction.Machine.OpenReferenceFlow
import PMAction.Machine.ReferenceMaintenance
import PMAction.Machine.CarrierEvents
import PMAction.BranchPulseContract
import PMConstants.CertifiedConstants
import PMConstants.DepthEvents
import PMSubstrate.ProtocolToll

/-!
# The handoff probability is the admittance `α`

`DepthEvents` derives the gravitational attenuation `α^{43/2}` from the event law, with one premise
left: the probability of the handoff event that carries a signal across one layer is the coupling
`α`. This module reduces that identification to two conventions the library already uses.

PM's `α` is an admittance: `α = 1/Z_geo`, the inverse of the node's impedance
(`PMSubstrate.causalCoupling`). `ProtocolToll` treats channels as Ohmic: admittances of parallel
channels add (`parallel_current`), and a unit admittance is one open channel
(`protocol_from_unit_channels`). Landauer's reading of a channel is the same: its dimensionless
conductance is its transmission probability, `G/G₀ = Σ Tᵢ`.

**Transmission is admittance.** The probability that a layer passes the signal on is a linear
function of the layer's admittance (parallel channels add their transmissions), normalized so that
one unit-admittance channel passes it with certainty. At the register level this is derived
(`node_current`, `through_eq_conductance` below): a node's conductance in units of one open
channel is its through weight.

* `transmission_of_linear`: any such map is the identity, `T(y) = y`.
* `handoff_is_alpha`: so a layer of impedance `Z_geo` hands off with probability `1/Z_geo = α`.
* `attenuation_from_admittance`: crossing `n` layers has probability `α^n`
  (`DepthEvents.required_handoffs`), which is the input of `DepthEvents.gravity_from_events`.

Status: the identification `p = α` is replaced by "transmission is linear in admittance, unit
channel open", which is how the library already reads channels. Linearity is Landauer's
single-channel relation and holds for `T ≤ 1`; `α < 1` (`causalCoupling_bounds`).

Why a gravitational handoff sees this admittance: under Closure a node cannot price a crossing by
what it carries, since no internal label distinguishes a gravitational handoff from any other
transition (`PMSubstrate.ClosureSymmetry`). So every crossing sees the node's one impedance
`Z_geo`, the same one that sets the electromagnetic `α⁻¹`. `closure_one_price`: a price on
crossing labels that no relabeling changes takes one value on all of them. The residual factor `16 − 2/3 − α` is
unchanged.

**At the register level (open reference flow).** What the receiver can do with an arriving bit:
* `PMAction.OpenReferenceFlow.exchange_reflects`, `bypass_transmits`: exchange puts the bit in the
  node's live register, which the next tick carries back toward its source; bypass keeps it on
  the through-stream, past the node. `receiver_exchange_or_bypass`,
  `repair_receiver_after_exchange`: one maintenance swap turns the exchanged state into the
  bypassed one. So a crossing is the bit ending the tick on the through-stream.
* `gravity_handoff_of_route_mixture`: an exclusive mixture of a closed route (transmission `0`)
  and an open one (transmission `1`) passes with the open route's weight; with that weight the
  node admittance, Closure gives `p = α`. `two_pass_alternative`: requiring two successes is also
  normalized and label-blind but gives a different law, so the single-pass form is a statement.
* Excluded: a uniformly prepared carrier followed by its reflection (`reflected_event_ne_alpha`,
  weights `k/8`), and fixed per-branch costs (`one_tick_cost_endpoint`: an interior probability
  never beats both deterministic endpoints).
* The coherent branch-exchange pulse moves weight `sin² t` between the two registers at every label
  (`pulse_calibration_transfers`), so a calibration at the reference transfers to the
  gravitational crossing under the same pulse. Its through weight is `cos² t`, which is
  Landauer's transmission: the reading above is `cos² t = 1/Z_geo`. A node of impedance
  `Z_geo ≈ 137` then mostly exchanges (renews its live state, `OpenReferenceFlow.open_restores`)
  and passes `α` on.

* `direct_crossing`: at speed one a bit is `n` layers deep after `n` ticks exactly when every node
  passed it (`full_displacement_iff`: an exchange reverses its direction, and it can never make up
  the lost ticks). So among the `2ⁿ` branch histories only the all-pass one crosses, and with an
  independent through weight `w` per node its probability is `w ^ n = DepthEvents.crossProb w n`
  (`direct_crossing_prob`). This is `DepthEvents`' survival law at the register level: the factor
  per layer is the through weight; the exchanged histories return toward the source.

* `node_current`: with incoming populations `nL`, `nR`, the net current across a node of through
  weight `w` is `w (nR − nL)`; an open channel (`w = 1`) conducts with unit admittance. So the
  through weight is the node's conductance in units of one open channel
  (`through_eq_conductance`): Landauer's relation, derived from the two streams rather than
  assumed. With the node's admittance `1/Z_geo = α` in those units (how `ProtocolToll` reads
  channels), the through weight is `α` (`handoff_from_conductance`), which fixes the pulse:
  `cos² t = α`. The premise "transmission is linear in admittance" above is this computation.
-/

noncomputable section
namespace PMConstants.HandoffAdmittance
open PMConstants

/-- **A normalized linear transmission law is the identity.** -/
theorem transmission_of_linear (T : ℝ →ₗ[ℝ] ℝ) (h1 : T 1 = 1) (y : ℝ) : T y = y := by
  have : T y = y • T 1 := by rw [← T.map_smul, smul_eq_mul, mul_one]
  rw [this, h1, smul_eq_mul, mul_one]

/-- **The handoff probability is `α`.** -/
theorem handoff_is_alpha (T : ℝ →ₗ[ℝ] ℝ) (h1 : T 1 = 1) :
    T (1 / PMSubstrate.geometricIndex) = PMSubstrate.causalCoupling :=
  transmission_of_linear T h1 _

/-- The handoff probability is a probability. -/
theorem handoff_bounds (T : ℝ →ₗ[ℝ] ℝ) (h1 : T 1 = 1) :
    0 < T (1 / PMSubstrate.geometricIndex) ∧ T (1 / PMSubstrate.geometricIndex) < 1 := by
  rw [handoff_is_alpha T h1]; exact PMSubstrate.causalCoupling_bounds

/-- **Attenuation over `n` layers is `α^n`.** -/
theorem attenuation_from_admittance (T : ℝ →ₗ[ℝ] ℝ) (h1 : T 1 = 1) (n : ℕ) :
    DepthEvents.crossProb (T (1 / PMSubstrate.geometricIndex)) n =
      PMSubstrate.causalCoupling ^ n := by
  rw [handoff_is_alpha T h1, DepthEvents.required_handoffs]

/-- **Under Closure a node has one price for every crossing.** If relabeling what a crossing
carries never changes its price (no internal label distinguishes the carried signal), all
crossings have the same price. -/
theorem closure_one_price {L : Type*} [DecidableEq L] (price : L → ℝ)
    (h : ∀ σ : Equiv.Perm L, ∀ a, price (σ a) = price a) (a b : L) : price a = price b := by
  have := h (Equiv.swap a b) a
  rw [Equiv.swap_apply_left] at this
  exact this.symm

/-- If a crossing is an exclusive mixture of closed and open routes, its
probability follows from the route weights and the two endpoint responses.
Closure transfers the calibrated admittance to the gravitational label. -/
theorem gravity_handoff_of_route_mixture {L : Type*} [DecidableEq L]
    (y p : L → ℝ) (gravity reference : L)
    (hinv : ∀ σ : Equiv.Perm L, ∀ a, y (σ a) = y a)
    (href : y reference = PMSubstrate.causalCoupling)
    (closed opened : ℝ) (hc : closed = 0) (ho : opened = 1)
    (hmix : p gravity = (1 - y gravity) * closed + y gravity * opened) :
    p gravity = PMSubstrate.causalCoupling := by
  rw [hmix, hc, ho, mul_zero, mul_one, zero_add,
    closure_one_price y hinv gravity reference, href]

/-- Two independent successful passes also give a label-blind, normalized
probability law. It differs strictly from a single pass at the substrate coupling. -/
theorem two_pass_alternative :
    DepthEvents.crossProb 0 2 = 0 ∧ DepthEvents.crossProb 1 2 = 1 ∧
    (∀ y ∈ Set.Icc (0 : ℝ) 1, DepthEvents.crossProb y 2 ∈ Set.Icc (0 : ℝ) 1) ∧
    DepthEvents.crossProb PMSubstrate.causalCoupling 2 < PMSubstrate.causalCoupling := by
  simp only [DepthEvents.required_handoffs, pow_two]
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · intro y hy
    exact ⟨mul_nonneg hy.1 hy.1, by simpa using mul_le_mul hy.2 hy.2 hy.1 zero_le_one⟩
  · obtain ⟨hp, hlt⟩ := PMSubstrate.causalCoupling_bounds
    simpa using mul_lt_mul_of_pos_left hlt hp

/-- A uniformly prepared incoming glue-class carrier followed by its reversible reflection
cannot give α for any sharp outgoing event: every event has weight k/8. -/
theorem reflected_event_ne_alpha (c : Fin 3) (outgoing : Finset (PMAction.CarrierEvents.Carrier c)) :
    PMSubstrate.NetCost.prob (outgoing.map (PMAction.CarrierEvents.reflect c).symm.toEmbedding) ≠
      PMSubstrate.causalCoupling := by
  rw [PMSubstrate.NetCost.prob, Finset.card_map, PMAction.CarrierEvents.carrier_card]
  have h := CertifiedConstants.alpha_bounds
  change _ < PMSubstrate.causalCoupling ∧ PMSubstrate.causalCoupling < _ at h
  by_cases he : outgoing.card = 0
  · rw [he]
    norm_num
    linarith [h.1]
  · have hk : (1 : ℝ) ≤ (outgoing.card : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr he
    push_cast
    linarith [h.2]

/-- For a prepared left basis state, detecting its right partner after the
exchange pulse gives the same probability at every carrier label. Calibration
at one label therefore transfers to any other under this same pulse/readout. -/
theorem pulse_calibration_transfers {n : Type*} [Fintype n] [DecidableEq n]
    (t : ℝ) (reference carrier : n)
    (href : Complex.normSq (PMAction.BranchMixerSynthesis.xPulse t (.inr reference) (.inl reference)) =
      PMSubstrate.causalCoupling) :
    Complex.normSq (PMAction.BranchMixerSynthesis.xPulse t (.inr carrier) (.inl carrier)) =
      PMSubstrate.causalCoupling := by
  rw [PMAction.BranchPulseContract.transfer_weight] at href ⊢
  exact href

/-- At the receiver, exchange and bypass deliver the same incoming bit to
different registers. Both comparisons use the same stream and a blank other input. -/
theorem receiver_exchange_or_bypass (s : PMAction.OpenReferenceFlow.State ℤ Bool)
    (blank : (s (-1)).1 = false) :
    PMAction.OpenReferenceFlow.evolution 0 PMAction.OpenReferenceFlow.line s 0 =
        ((s 1).2, false) ∧
    PMAction.OpenReferenceFlow.streamShift PMAction.OpenReferenceFlow.line s 0 =
        (false, (s 1).2) := by
  change ((s 1).2, (s (-1)).1) = _ ∧ ((s (-1)).1, (s 1).2) = _
  rw [blank]
  exact ⟨rfl, rfl⟩

/-- If the next task requires a blank live bit and the incoming bit in the
record, one maintenance swap after exchange achieves the bypass state. -/
theorem repair_receiver_after_exchange (s : PMAction.OpenReferenceFlow.State ℤ Bool) :
    PMAction.ReferenceMaintenance.event (0 : ℤ)
      (PMAction.OpenReferenceFlow.evolution 0 PMAction.OpenReferenceFlow.line s) =
    PMAction.OpenReferenceFlow.streamShift PMAction.OpenReferenceFlow.line s := by
  funext x
  by_cases hx : x = 0 <;>
    simp [PMAction.ReferenceMaintenance.event, PMAction.OpenReferenceFlow.evolution_apply,
      PMAction.OpenReferenceFlow.streamShift, hx]

/-- With probability-independent branch costs an interior probability cannot
strictly beat both deterministic endpoints. This includes fixed repair tolls. -/
theorem one_tick_cost_endpoint (p missed delivered : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    min missed delivered ≤ (1 - p) * missed + p * delivered := by
  rcases le_total missed delivered with h | h
  · rw [min_eq_left h]
    nlinarith [mul_nonneg hp.1 (sub_nonneg.mpr h)]
  · rw [min_eq_right h]
    nlinarith [mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr h)]

/-! ## The direct crossing at the register level -/

/-- Displacement of a bit over a branch history: at each tick the node either passes it
(`true`, direction kept) or exchanges it (`false`, direction reversed, `exchange_reflects`), then
the bit moves one site in its direction. -/
def disp : ℤ → List Bool → ℤ
  | _, [] => 0
  | d, b :: bs => (if b then d else -d) + disp (if b then d else -d) bs

lemma disp_bound : ∀ (bs : List Bool) (d : ℤ), (d = 1 ∨ d = -1) →
    -(bs.length : ℤ) ≤ disp d bs ∧ disp d bs ≤ bs.length
  | [], _, _ => by simp [disp]
  | b :: bs, d, hd => by
    have hd' : (if b then d else -d) = 1 ∨ (if b then d else -d) = -1 := by
      cases b <;> simp <;> omega
    have ih := disp_bound bs _ hd'
    simp only [disp, List.length_cons]
    push_cast
    rcases hd' with h | h <;> rw [h] at ih ⊢ <;> omega

/-- **Speed one selects the direct history.** A bit moving in direction `d` covers `d · n` in `n`
ticks exactly when every node passes it. -/
theorem full_displacement_iff : ∀ (bs : List Bool) (d : ℤ), (d = 1 ∨ d = -1) →
    (disp d bs = d * bs.length ↔ ∀ b ∈ bs, b = true)
  | [], _, _ => by simp [disp]
  | b :: bs, d, hd => by
    cases b
    · have hb := disp_bound bs (-d) (by omega)
      simp only [disp, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      constructor
      · intro h; exfalso; push_cast at h; rcases hd with rfl | rfl <;> omega
      · intro h; exact absurd (h false (by simp)) (by decide)
    · have ih := full_displacement_iff bs d hd
      simp only [disp, ↓reduceIte, List.length_cons, List.mem_cons, forall_eq_or_imp, true_and]
      push_cast
      rw [← ih]
      constructor <;> intro h <;> linarith

/-- **The direct crossing.** Of the `2ⁿ` branch histories over `n` ticks, the only one that puts
the bit `n` layers deep is the all-pass one. With an independent through weight `w` per node its
probability is `w ^ n`, which is `DepthEvents.crossProb w n`. -/
theorem direct_crossing (n : ℕ) (bs : List Bool) (hn : bs.length = n) :
    disp (-1) bs = -(n : ℤ) ↔ bs = List.replicate n true := by
  have h := full_displacement_iff bs (-1) (Or.inr rfl)
  rw [hn] at h
  rw [show -(n : ℤ) = -1 * n by ring, h, ← hn, List.eq_replicate_iff]
  simp

theorem direct_crossing_prob (w : ℝ) (n : ℕ) :
    ((List.replicate n true).map fun b => if b then w else 1 - w).prod =
      DepthEvents.crossProb w n := by
  simp [DepthEvents.required_handoffs]

/-! ## The through weight is the node's conductance (Landauer, derived) -/

/-- The left-moving flux leaving a node on its left side when the two incoming streams carry
populations `nL` (from the left) and `nR` (from the right): the right stream's passed part and the
left stream's exchanged (returned) part. -/
def leftOutflow (w nL nR : ℝ) : ℝ := w * nR + (1 - w) * nL

/-- **The node current.** The net current across the node is the through weight times the
population difference: `w (nR − nL)`. -/
theorem node_current (w nL nR : ℝ) : leftOutflow w nL nR - nL = w * (nR - nL) := by
  unfold leftOutflow; ring

/-- An open channel (`w = 1`) has unit conductance. -/
theorem open_channel_unit (nL nR : ℝ) : leftOutflow 1 nL nR - nL = 1 * (nR - nL) :=
  node_current 1 nL nR

/-- **The conductance is the through weight.** If the node conducts with admittance `y` in units
of one open channel, its through weight is `y`. -/
theorem through_eq_conductance {w y : ℝ}
    (h : ∀ nL nR, leftOutflow w nL nR - nL = y * (nR - nL)) : w = y := by
  have := h 0 1
  rw [node_current] at this
  simpa using this

/-- **The handoff weight is `α`.** A node of admittance `1/Z_geo = α` (in units of one open
channel, `PMSubstrate.ProtocolToll`) has through weight `α`, so `n` layers pass `α ^ n`
(`direct_crossing`, `direct_crossing_prob`). -/
theorem handoff_from_conductance {w : ℝ}
    (h : ∀ nL nR, leftOutflow w nL nR - nL = PMSubstrate.causalCoupling * (nR - nL)) (n : ℕ) :
    w = PMSubstrate.causalCoupling ∧
      DepthEvents.crossProb w n = PMSubstrate.causalCoupling ^ n := by
  have hw := through_eq_conductance h
  exact ⟨hw, by rw [hw, DepthEvents.required_handoffs]⟩

end PMConstants.HandoffAdmittance
