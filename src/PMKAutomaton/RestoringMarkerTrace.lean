import PMKAutomaton.LocalController

/-!
# The native two-visit live-to-live restoration event

A single live marker enters from site -1. With the other incoming
ports empty, the live marker at the downstream exit is exactly the
joint occurrence of the entry and exit swaps. This determines the event
whose histories would have to be weighted to obtain an effective transfer.
-/

namespace PMKAutomaton.LocalController

/-- The live marker returns through the record stream precisely if both
guards exchange their unequal inputs, evaluated at the actual phases. -/
theorem restoring_marker_live (rule : Rule) (s : State)
    (hlive : (s.2.2 (-1)).1 = true) (hentry : (s.2.2 1).2 = false)
    (hfar : (s.2.2 (-3)).1 = false) (hsource : (s.2.2 (-1)).2 = false) :
    let entered := rawTick rule s
    ((rawTick rule entered).2.2 (-1)).1 =
      (rule s.1 (s.2.1 0).1 (true, false) &&
        rule entered.1 (entered.2.1 (-1)).1 (false, true)) := by
  intro entered
  have he : (entered.2.2 0).2 = rule s.1 (s.2.1 0).1 (true, false) := by
    change (applyGuard (rule s.1 (s.2.1 0).1) ((s.2.2 (-1)).1, (s.2.2 1).2)).2 = _
    rw [hlive, hentry]
    cases h : rule s.1 (s.2.1 0).1 (true, false) <;> simp [applyGuard, h]
  have hf : (entered.2.2 (-2)).1 = false := by
    change (applyGuard (rule s.1 (s.2.1 (-2)).1) ((s.2.2 (-3)).1, (s.2.2 (-1)).2)).1 = _
    rw [hfar, hsource]
    simp [applyGuard]
  change (applyGuard (rule entered.1 (entered.2.1 (-1)).1)
    ((entered.2.2 (-2)).1, (entered.2.2 0).2)).1 = _
  rw [he, hf]
  cases rule s.1 (s.2.1 0).1 (true, false)
  · simp [applyGuard]
  · cases h : rule entered.1 (entered.2.1 (-1)).1 (false, true) <;> simp [applyGuard, h]

/-- The two reversible open-compatible controllers disagree on the
restoring exit under a mixed entry request and a ready exit request. -/
theorem restoring_marker_mixed (s : State)
    (hlive : (s.2.2 (-1)).1 = true) (hentry : (s.2.2 1).2 = false)
    (hfar : (s.2.2 (-3)).1 = false) (hsource : (s.2.2 (-1)).2 = false)
    (hentryRequest : (s.2.1 0).1 = (true, false))
    (hexitRequest : (s.2.1 (-1)).1 = (true, true)) :
    ((rawTick exchangeOnBoth (rawTick exchangeOnBoth s)).2.2 (-1)).1 = false ∧
      ((rawTick exchangeOnEither (rawTick exchangeOnEither s)).2.2 (-1)).1 = true := by
  have retained (rule : Rule) : ((rawTick rule s).2.1 (-1)).1 = (s.2.1 (-1)).1 := rfl
  constructor
  · rw [restoring_marker_live exchangeOnBoth s hlive hentry hfar hsource]
    simp [retained, hentryRequest, exchangeOnBoth]
  · rw [restoring_marker_live exchangeOnEither s hlive hentry hfar hsource]
    simp [retained, hentryRequest, hexitRequest, exchangeOnEither]

end PMKAutomaton.LocalController
