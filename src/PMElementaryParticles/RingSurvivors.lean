import PMElementaryParticles.RingRates
import PMElementaryParticles.RecordPortIdentification

/-!
# Structural survivor facts on the 43-ring

The packet starts on the live stream at `x0`. While it meets no exchanging site
it moves one site per tick (`quiet_walk`). Every site is reached within `n`
ticks (`reach`), so the first exchanging site on its path registers it
(`first_arrival_floor`). Hence a bit ring registers in one period if and only
if some site exchanges (`sum_zero_iff`, `ring43_toll_iff`).

On the 43-ring this gives the Toll and least-Toll statements without
enumerating firing patterns:

* Toll excludes exactly the firing patterns with no exchanging site on a
  differing bit ring;
* every Toll-admissible two-ring pattern has total at least the Hamming
  distance to the reference (`ringTotal_ge_hamming`), and one firing site per
  differing ring attains it (`ringTotal_oneSite`);
* two adjacent firing sites saturate the period (`trapping_saturates`), the
  case that the Margin ceiling excludes.
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

/-! ## First-arrival floor on the `n`-ring -/

section FirstArrival

variable {n : ℕ}

/-- One port step is the stream shift followed by the on-site exchange. -/
theorem portStep_apply (either : Bool) (r : Fin n → IsolatedRequests)
    (P : PMKAutomaton.RingReceiver.PortField n) (x : Fin n) :
    PMKAutomaton.RingReceiver.portStep either r P x =
      PMKAutomaton.LocalController.applyGuard
        (fun _ => PMKAutomaton.RingReceiver.exchange either (r x))
        (PMKAutomaton.RingReceiver.arrivals P x) := rfl

theorem localized_live (y z : Fin n) :
    (localizedPortsN n y activePacket z).1 = decide (z = y) := by
  by_cases h : z = y <;> simp [localizedPortsN, h, active_activePacket]

theorem localized_record (y z : Fin n) :
    (localizedPortsN n y activePacket z).2 = false := by
  by_cases h : z = y <;> simp [localizedPortsN, h]

/-- A packet on the live stream at `y` arrives at `finRotate n y`. -/
theorem arrivals_localized (y x : Fin n) :
    PMKAutomaton.RingReceiver.arrivals (localizedPortsN n y activePacket) x =
      (decide (x = finRotate n y), false) := by
  change ((localizedPortsN n y activePacket ((finRotate n)⁻¹ x)).1,
      (localizedPortsN n y activePacket (finRotate n x)).2) = _
  rw [localized_live, localized_record]
  simp [Equiv.Perm.inv_eq_iff_eq]

/-- With no exchange at the arrival site, the packet moves one site. -/
theorem portStep_quiet (either : Bool) (r : Fin n → IsolatedRequests) (y : Fin n)
    (hq : PMKAutomaton.RingReceiver.exchange either (r (finRotate n y)) = false) :
    PMKAutomaton.RingReceiver.portStep either r (localizedPortsN n y activePacket) =
      localizedPortsN n (finRotate n y) activePacket := by
  funext x
  rw [portStep_apply, arrivals_localized]
  by_cases hx : x = finRotate n y
  · subst hx
    simp [PMKAutomaton.LocalController.applyGuard, hq, localizedPortsN,
      active_activePacket]
  · simp [PMKAutomaton.LocalController.applyGuard, hx, localizedPortsN]

/-- Until its first exchanging site, the packet walks the ring. -/
theorem quiet_walk (either : Bool) (r : Fin n → IsolatedRequests) (x0 : Fin n)
    (j : ℕ) (hq : ∀ i < j,
      PMKAutomaton.RingReceiver.exchange either (r ((finRotate n)^[i + 1] x0)) = false) :
    (PMKAutomaton.RingReceiver.portStep either r)^[j] (localizedPortsN n x0 activePacket) =
      localizedPortsN n ((finRotate n)^[j] x0) activePacket := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj := hq j (Nat.lt_succ_self j)
    rw [Function.iterate_succ_apply' (⇑(finRotate n))] at hj
    rw [Function.iterate_succ_apply' (⇑(PMKAutomaton.RingReceiver.portStep either r)),
      ih (fun i hi => hq i (Nat.lt_succ_of_lt hi)),
      Function.iterate_succ_apply' (⇑(finRotate n))]
    exact portStep_quiet either r _ hj

theorem finRotate_iterate (k m : ℕ) (x : Fin (k + 1)) :
    (finRotate (k + 1))^[m] x = x + (m : Fin (k + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, finRotate_succ_apply, Nat.cast_succ, add_assoc]

/-- Every site is reached within one lap. -/
theorem reach (k : ℕ) (x0 s : Fin (k + 1)) :
    ∃ m < k + 1, (finRotate (k + 1))^[m + 1] x0 = s := by
  refine ⟨(s - x0 - 1).val, (s - x0 - 1).isLt, ?_⟩
  rw [finRotate_iterate, Nat.cast_succ, Fin.cast_val_eq_self]
  abel

/-- The arrival at the first exchanging site registers. -/
theorem flag_at_arrival (either : Bool) (r : Fin n → IsolatedRequests) (x0 : Fin n)
    (j : ℕ) (hq : ∀ i < j,
      PMKAutomaton.RingReceiver.exchange either (r ((finRotate n)^[i + 1] x0)) = false)
    (hs : PMKAutomaton.RingReceiver.exchange either (r ((finRotate n)^[j + 1] x0)) = true) :
    localizedFlagNatN n either r x0 j ((finRotate n)^[j + 1] x0) = 1 := by
  rw [Function.iterate_succ_apply' (⇑(finRotate n))] at hs ⊢
  unfold localizedFlagNatN
  rw [quiet_walk either r x0 j hq, arrivals_localized]
  simp [hs]

/-- Floor: any exchanging site gives at least one registration within `n` ticks. -/
theorem first_arrival_floor (either : Bool) (r : Fin n → IsolatedRequests) (x0 : Fin n)
    (hfire : ∃ s, PMKAutomaton.RingReceiver.exchange either (r s) = true)
    (T : ℕ) (hT : n ≤ T) :
    1 ≤ localizedSumN n either r x0 T := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := x0.isLt; omega⟩
  obtain ⟨s, hs⟩ := hfire
  obtain ⟨m, hm, hms⟩ := reach k x0 s
  have hPm : PMKAutomaton.RingReceiver.exchange either
      (r ((finRotate (k + 1))^[m + 1] x0)) = true := by rw [hms]; exact hs
  have hex : ∃ i, PMKAutomaton.RingReceiver.exchange either
      (r ((finRotate (k + 1))^[i + 1] x0)) = true := ⟨m, hPm⟩
  obtain ⟨j, hjP, hjmin⟩ : ∃ j, PMKAutomaton.RingReceiver.exchange either
      (r ((finRotate (k + 1))^[j + 1] x0)) = true ∧ ∀ i < j,
      ¬ PMKAutomaton.RingReceiver.exchange either
        (r ((finRotate (k + 1))^[i + 1] x0)) = true :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  have hjm : j ≤ m := by
    by_contra h
    exact hjmin m (by omega) hPm
  have hq : ∀ i < j, PMKAutomaton.RingReceiver.exchange either
      (r ((finRotate (k + 1))^[i + 1] x0)) = false := fun i hi => by
    simpa using hjmin i hi
  have hjT : j < T := by omega
  calc 1 = localizedFlagNatN (k + 1) either r x0 j ((finRotate (k + 1))^[j + 1] x0) :=
        (flag_at_arrival either r x0 j hq hjP).symm
    _ ≤ ∑ x, localizedFlagNatN (k + 1) either r x0 j x :=
        Finset.single_le_sum (f := fun x => localizedFlagNatN (k + 1) either r x0 j x)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    _ ≤ localizedSumN (k + 1) either r x0 T :=
        Finset.single_le_sum (f := fun t => ∑ x, localizedFlagNatN (k + 1) either r x0 t x)
          (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hjT)

/-- No exchanging site: no registration, for every horizon. -/
theorem no_fire_zero (either : Bool) (r : Fin n → IsolatedRequests) (x0 : Fin n) (T : ℕ)
    (h : ∀ s, PMKAutomaton.RingReceiver.exchange either (r s) = false) :
    localizedSumN n either r x0 T = 0 := by
  unfold localizedSumN
  apply Finset.sum_eq_zero
  intro t _
  apply Finset.sum_eq_zero
  intro x _
  simp [localizedFlagNatN, h x]

/-- Over at least one period, the count is zero iff no site exchanges. -/
theorem sum_zero_iff (either : Bool) (r : Fin n → IsolatedRequests) (x0 : Fin n)
    (T : ℕ) (hT : n ≤ T) :
    localizedSumN n either r x0 T = 0 ↔
      ∀ s, PMKAutomaton.RingReceiver.exchange either (r s) = false := by
  constructor
  · intro h0 s
    by_contra hs
    have := first_arrival_floor either r x0 ⟨s, by simpa using hs⟩ T hT
    omega
  · exact no_fire_zero either r x0 T

end FirstArrival

/-! ## Toll and least Toll on the 43-ring -/

/-- Toll floor on one 43-site bit ring (OR guard): it registers in one period
iff some site carries a request. -/
theorem ring43_toll_iff (r : Fin 43 → IsolatedRequests) (x0 : Fin 43) :
    0 < localizedSumN 43 true r x0 43 ↔
      ∃ s, PMKAutomaton.RingReceiver.exchange true (r s) = true := by
  rw [Nat.pos_iff_ne_zero, ne_eq, sum_zero_iff true r x0 43 le_rfl]
  simp

/-- Two-ring total over one period: differing record bits use their ring. -/
def ringTotal (c : PMConstants.PacketGaugeActions.Channels) (colourReference : Bool)
    (r : Fin 2 → Fin 43 → IsolatedRequests) (x0 : Fin 43) : ℕ :=
  ∑ b : Fin 2,
    if bitOf (labelRecord c) b ≠ bitOf (refRecord colourReference) b then
      localizedSumN 43 true (r b) x0 43
    else 0

/-- Least Toll, lower bound: every Toll-admissible pattern costs at least the
Hamming distance to the reference. -/
theorem ringTotal_ge_hamming (c : PMConstants.PacketGaugeActions.Channels)
    (colourReference : Bool) (r : Fin 2 → Fin 43 → IsolatedRequests) (x0 : Fin 43)
    (hfloor : ∀ b, bitOf (labelRecord c) b ≠ bitOf (refRecord colourReference) b →
      ∃ s, PMKAutomaton.RingReceiver.exchange true (r b s) = true) :
    hamming (labelRecord c) (refRecord colourReference) ≤
      ringTotal c colourReference r x0 := by
  have key : ∀ b : Fin 2,
      (if bitOf (labelRecord c) b ≠ bitOf (refRecord colourReference) b then 1 else 0) ≤
        (if bitOf (labelRecord c) b ≠ bitOf (refRecord colourReference) b then
          localizedSumN 43 true (r b) x0 43 else 0) := by
    intro b
    split_ifs with h
    · exact first_arrival_floor true (r b) x0 (hfloor b h) 43 le_rfl
    · exact le_rfl
  calc hamming (labelRecord c) (refRecord colourReference) =
        ∑ b : Fin 2,
          (if bitOf (labelRecord c) b ≠ bitOf (refRecord colourReference) b then 1 else 0) := by
        simp [hamming, bitOf, Fin.sum_univ_two]
    _ ≤ ringTotal c colourReference r x0 := Finset.sum_le_sum fun b _ => key b

/-- Least Toll, attained: one firing site per ring gives exactly the Hamming
distance. -/
theorem ringTotal_oneSite (c : PMConstants.PacketGaugeActions.Channels)
    (colourReference : Bool) (s : Fin 2 → Fin 43) (x0 : Fin 43) :
    ringTotal c colourReference (fun b => oneFiringN 43 (s b)) x0 =
      hamming (labelRecord c) (refRecord colourReference) := by
  rcases hL : labelRecord c with ⟨l1, l2⟩
  rcases hR : refRecord colourReference with ⟨r1, r2⟩
  cases l1 <;> cases l2 <;> cases r1 <;> cases r2 <;>
    simp [ringTotal, bitOf, hamming, hL, hR, Fin.sum_univ_two, one_site_floor]

end PMElementaryParticles.RingSurvivors
