import PMElementaryParticles.RingRates
import PMElementaryParticles.RecordPortIdentification

/-!
# Structural survivor facts on the 43-ring

This file records the parts of the 43-ring survivor restatement that are
proved. The one-firing-site floor is `RingRates.ring43_one`; the saturating
adjacent-site trapping case is checked explicitly.

The general first-arrival floor for an arbitrary nonempty firing pattern is not
completed here. Consequently the full 43-ring Toll/Margin/Map survivor table is
not restated as a theorem yet; the 3-ring table remains a toy-ring computation.
-/

noncomputable section

namespace PMElementaryParticles.RingSurvivors

open PMElementaryParticles.IsolatedExcitation
open PMElementaryParticles.RingRates
open PMElementaryParticles.HeavyFlipControl
open PMElementaryParticles.ProtocolInventory

/-- The empty firing pattern registers nothing, for any ring size and horizon. -/
theorem empty_pattern_zero (n T : ℕ) (either : Bool) (x0 : Fin n) :
    localizedSumN n either (fun _ => (false, false)) x0 T = 0 :=
  empty_uniform_flags_zero n T either x0

/-- One firing site has the exact per-period count `1` on the 43-ring. -/
theorem one_site_floor (s x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 s) x0 43 = 1 :=
  ring43_one s x0

/-- The positive minimum for a one-site pattern is exactly one. -/
theorem one_site_min_positive (s x0 : Fin 43) :
    0 < localizedSumN 43 true (oneFiringN 43 s) x0 43 ∧
      localizedSumN 43 true (oneFiringN 43 s) x0 43 = 1 := by
  rw [one_site_floor s x0]
  norm_num

/-- Two adjacent firing sites with the packet starting at the lower site trap
the packet: one registration on every tick of the 43-tick period. -/
def trappingRequests : Fin 43 → IsolatedRequests :=
  fun x => if x = 0 ∨ x = 1 then (true, true) else (false, false)

set_option maxHeartbeats 0 in
theorem trapping_saturates :
    localizedSumN 43 true trappingRequests 0 43 = 43 := by
  decide +kernel

/-- The 43-ring total of a two-bit record when each differing bit ring uses
one firing site and every equal ring is empty. Its value is the Hamming
distance, the minimum one-site total.  This is a minimum, not the general
survivor theorem. -/
def oneSiteTotal (c : PMConstants.PacketGaugeActions.Channels)
    (colourReference : Bool) (s : Fin 2 → Fin 43) (x0 : Fin 43) : ℝ :=
  ∑ b : Fin 2,
    if bitOf (labelRecord c) b ≠ bitOf (refRecord colourReference) b then
      (localizedSumN 43 true (oneFiringN 43 (s b)) x0 43 : ℝ)
    else 0

theorem oneSiteTotal_eq_hamming (c : PMConstants.PacketGaugeActions.Channels)
    (colourReference : Bool) (s : Fin 2 → Fin 43) (x0 : Fin 43) :
    oneSiteTotal c colourReference s x0 =
      (hamming (labelRecord c) (refRecord colourReference) : ℝ) := by
  rcases hL : labelRecord c with ⟨l1, l2⟩
  rcases hR : refRecord colourReference with ⟨r1, r2⟩
  cases l1 <;> cases l2 <;> cases r1 <;> cases r2 <;>
    simp [oneSiteTotal, bitOf, hamming, hL, hR, Fin.sum_univ_two,
      one_site_floor]

end PMElementaryParticles.RingSurvivors
