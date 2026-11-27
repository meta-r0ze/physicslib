import PMKAutomaton.AutonomousRing
import PMElementaryParticles.ReversalEvents

/-!
# The unit reversal window is not a full-state particle cycle

AutonomousRing proves native stream-direction parity for arbitrary updates.
Here it is attached to the existing RingRates/ReversalEvents observation
account. one_site_exact has one reversal in an n-tick window, and that
window cannot return the located packet state. This is not a failure of
that theorem: its horizon was never a certified full native orbit period.

The requested electron test adds exact full-state return AND one reversal
in that period. Those conditions conflict before localization, identity,
or single-marker robustness are tested. There is no electron-selected rule
family to census. Changing to a quotient cycle or a fixed-window rate would
require an explicit identity and clock-normalization construction, not an
implicit division of the even reversal count by two.

SpacetimeProgram.program_registration_bound concerns the existing two bit
rings over the fixed 43-tick window (bound 86). It is not a bound of 86 on
an arbitrary autonomous cycle whose length varies. One packet can reverse
at most once per tick. No lepton ordering or need for a particular number
of dimensions follows from an empty selected rule family.

The autonomous Boolean model is an exact stream/marker model, not yet a
physical realization of a labelled E8 excitation or its stationary vacuum.
No code-dependent Hamming distance is used as a mass cost.
-/

namespace PMElementaryParticles.AutonomousCycleBoundary
open PMKAutomaton
open PMElementaryParticles.ReversalEvents PMElementaryParticles.RingRates
open PMElementaryParticles.IsolatedExcitation

theorem count_eq_native {n : ℕ} (either : Bool) (r : Fin n → IsolatedRequests)
    (x0 : Fin n) (t : ℕ) : count either r x0 t =
      AutonomousRing.reversals (step either r) Prod.snd (x0,false) t := by
  rw [AutonomousRing.reversals_eq_sum]
  simp only [count,reversal,trace,Function.iterate_succ_apply']
  rfl

theorem one_site_not_closed {n : ℕ} (either : Bool) (s x0 : Fin n) :
    (step either (oneFiringN n s))^[n] (x0,false) ≠ (x0,false) := by
  intro hc
  have hr : AutonomousRing.reversals (step either (oneFiringN n s)) Prod.snd (x0,false) n = 1 := by
    rw [← count_eq_native,← registrations_eq_reversals,one_site_exact]
  exact AutonomousRing.no_one_reversal_cycle _ _ _ _ hc hr

/-- The statement includes 43; there is no special finite-size exception. -/
theorem ring43_unit_not_closed (s x0 : Fin 43) :
    (step true (oneFiringN 43 s))^[43] (x0,false) ≠ (x0,false) :=
  one_site_not_closed true s x0

end PMElementaryParticles.AutonomousCycleBoundary
