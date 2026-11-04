import PMConstants.Bulk

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
handoff probability equal to the coupling `α`, the attenuation is `α^n`.

**Half depth.** The only integer-count object is the closed causal loop of `Δ = 43` handoffs, with
probability `α^43`. A loop is an outbound trip followed by a return. The update is real, hence
time-reversal symmetric (`CPPhases.real_update_commutes_conj`), so the two legs have equal
probability; the loop probability is their product. `one_way_from_loop`: the one-way transmission
is then uniquely `√(α^43) = α^{43/2}`, the exponent the paper uses, without any half-hop.

Remaining premises: the handoff probability is the coupling `α`, and the residual factor
`16 − 2/3 − α`.
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
    (hsym : out = back) (hloop : out * back = α ^ 43) :
    out = α ^ ((43 : ℝ) / 2) := by
  subst hsym
  have h2 : out ^ 2 = α ^ 43 := by rw [sq]; exact hloop
  have hs : out = Real.sqrt (α ^ 43) := by
    rw [← h2, Real.sqrt_sq ho]
  rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hα]
  norm_num

theorem gravity_from_events {α : ℝ} (hα : 0 ≤ α) {out : ℝ} (ho : 0 ≤ out)
    (hloop : out * out = crossProb α 43) :
    Depth.gravity α = residual α * out := by
  rw [required_handoffs] at hloop
  rw [Depth.gravity, one_way_from_loop hα ho rfl hloop]

end PMConstants.DepthEvents
