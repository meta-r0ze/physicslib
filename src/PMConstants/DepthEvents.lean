import PMConstants.Bulk
import PMSubstrate.ClockPlane

/-!
# The gravitational attenuation from the event law: why `α`, and why `α^{43/2}`

`Bulk` and `Depth` left two choices open: the per-step survival (`α` or `1 − α`) and the
half-integer depth `43/2`, which is not a count of full hops (`Bulk.no_integer_half_period`).

**Survival.** Under the event law nothing changes state without an event: a carrier moves only
through a reflection event (Paper II, `CarrierEvents`). A signal crossing a layer therefore
requires one handoff event. If that event occurs with probability `p` per layer, independently,
`required_handoffs`: the probability of crossing `n` layers is `p^n`, and with no event the signal
does not advance at all (`no_event_no_advance`). The law `(1 − α)^n` counts the histories in which
no interaction occurs, which are exactly the histories in which the signal stays put. With the
handoff probability equal to the coupling `α`, the attenuation is `α^n`. At the register level
(`HandoffAdmittance.direct_crossing`): at speed one only the history in which every node passes
the bit on reaches depth `n` in `n` ticks, so the per-layer factor is the node's through weight.

**Half depth.** The only integer-count object is the closed causal loop of `Δ = 43` handoffs, with
probability `α^43`. A loop is an outbound trip followed by a return. The update is real, hence
time-reversal symmetric (`CPPhases.real_update_commutes_conj`), so the two legs have equal
probability; the loop probability is their product. `one_way_from_loop`: the one-way transmission
is then uniquely `√(α^43) = α^{43/2}`, the exponent the paper uses, without any half-hop.

**The loop.** `clock_loop_minimal`: in the clock's glue group `ℤ/43` (`PMSubstrate.ClockPlane`,
the cycle Paper I visits in one period) every nonzero step has order exactly `43`, since `43` is
prime. A closed loop of unit handoffs along the clock returns only after a multiple of `Δ = 43`,
so the shortest closed causal loop is the `Δ`-handoff loop used above.

**Why the gravity loop is a clock loop.** A signal moves at speed one: one layer, so one handoff,
per tick (Paper I's causal cone, `2t + 1` positions at tick `t`). A loop is closed when the signal
is back in the same state, which includes the clock phase: no external clock can relabel it
(Postulate I). `closed_loop_handoffs`: a loop of `n` ticks with one handoff each returns to its
phase only if `43 ∣ n`, so it has at least `Δ = 43` handoffs, and the clock cycle attains it.

The handoff probability is the coupling `α`: a node's through weight is its conductance in units of
one open channel (`HandoffAdmittance.node_current`, `through_eq_conductance`), which is the node
admittance `1/Z_geo = α` (`handoff_from_conductance`). Remaining premise: the residual factor
`16 − 2/3 − α` (its `2/3` read as the boundary's colour-axis charge quanta,
`BoundaryStorage.storage_is_charge_quantum`).
-/

noncomputable section
namespace PMConstants.DepthEvents
open PMConstants

/-- Probability of crossing `n` layers when each crossing requires an event of probability `p`. -/
def crossProb (p : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => crossProb p n * p

theorem required_handoffs (p : ℝ) (n : ℕ) : crossProb p n = p ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [crossProb, ih, pow_succ]

/-- Without the event the position is unchanged: the advance contributed by a no-event history
is zero, so `(1 − p)` weights only non-advancing histories. -/
def advance (event : Bool) : ℕ := if event then 1 else 0

theorem no_event_no_advance : advance false = 0 := rfl

theorem one_way_from_loop {α out back : ℝ} (hα : 0 ≤ α) (ho : 0 ≤ out)
    (hsym : out = back) (hloop : out * back = α ^ PMSubstrate.E8Values.Delta) :
    out = α ^ ((PMSubstrate.E8Values.Delta : ℝ) / (PMSubstrate.E8Values.chi : ℝ)) := by
  subst hsym
  have h2 : out ^ 2 = α ^ PMSubstrate.E8Values.Delta := by rw [sq]; exact hloop
  have hs : out = Real.sqrt (α ^ PMSubstrate.E8Values.Delta) := by
    rw [← h2, Real.sqrt_sq ho]
  rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hα]
  rw [PMSubstrate.E8Values.Delta_eq, PMSubstrate.E8Values.chi_eq]
  norm_num

theorem gravity_from_events {α : ℝ} (hα : 0 ≤ α) {out : ℝ} (ho : 0 ≤ out)
    (hloop : out * out = crossProb α PMSubstrate.E8Values.Delta) :
    Depth.gravity α = residual α * out := by
  rw [required_handoffs] at hloop
  rw [Depth.gravity, one_way_from_loop hα ho rfl hloop]

/-- **The shortest closed loop along the clock has `Δ = 43` steps.** Every nonzero element of the
clock's glue group `ℤ/43` has additive order `43`. -/
theorem clock_loop_minimal (x : ZMod 43) (hx : x ≠ 0) : addOrderOf x = 43 := by
  have : Fact (Nat.Prime 43) := ⟨by norm_num⟩
  have h : 43 • x = 0 := by
    have := card_nsmul_eq_zero (x := x)
    rwa [ZMod.card] at this
  exact addOrderOf_eq_prime h hx

/-- **A closed loop at one handoff per tick has at least `Δ` handoffs.** Returning to the same
clock phase after `n` ticks needs `n ≡ 0 (mod 43)`. -/
theorem closed_loop_handoffs (n : ℕ) (hn : 0 < n) (hret : (n : ZMod 43) = 0) : 43 ≤ n :=
  Nat.le_of_dvd hn ((ZMod.natCast_eq_zero_iff n 43).mp hret)

/-- The clock cycle attains it. -/
theorem clock_cycle_closes : ((43 : ℕ) : ZMod 43) = 0 := ZMod.natCast_self 43

end PMConstants.DepthEvents
