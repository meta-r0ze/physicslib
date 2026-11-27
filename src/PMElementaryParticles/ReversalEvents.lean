import PMElementaryParticles.SpacetimeProgram

/-!
# Registration and stream reversal

A localized packet has a site and a direction. False means the live forward
stream. True means the retained backward stream. A tick first shifts along
that stream, then swaps streams exactly when the receiver exchanges.
Registrations count both directions of reversal. The result holds for every
request field, either guard and every finite horizon. It is not a probability
or the coherent phase flag `DiagonalReadout.flag`.

`footprint` is the requested reversal reading of OccupancyCost. Its event
field counts all reversals of both bit rings. Its cost equality is a theorem
about that defined account. Kinematics alone does not prove that every
physical held event is a reversal. No Dirac equation or mass unit conversion
is inferred. The telegraph-process analogy is context only.

The old `ProgramWitness.witness` fires both rings and has two reversals, even
though its differing-bit subtotal is one. `quietEqualRing` instead leaves the
equal bit ring empty. It attains one total reversal under the current pillars.
A one-reversal window changes direction, so this is not a proof of full-state
return after 43 ticks or of retained-reference readability.
-/

noncomputable section
namespace PMElementaryParticles.ReversalEvents
open PMElementaryParticles.IsolatedExcitation PMElementaryParticles.RingRates
open PMElementaryParticles.ProgramWitness PMElementaryParticles.HeavyFlipControl
open PMElementaryParticles.RingSurvivors
open PMKAutomaton

/-- Site and stream; true is backward. -/
abbrev Located (n : ℕ) := Fin n × Bool

def arrival {n : ℕ} (s : Located n) : Fin n :=
  if s.2 then (finRotate n).symm s.1 else finRotate n s.1

def step {n : ℕ} (either : Bool) (r : Fin n → IsolatedRequests) (s : Located n) : Located n :=
  (arrival s, if RingReceiver.exchange either (r (arrival s)) then !s.2 else s.2)

def ports {n : ℕ} (s : Located n) : RingReceiver.PortField n :=
  if s.2 then recordPortsN n s.1 else localizedPortsN n s.1 activePacket

/-- The missing reverse-to-forward companion of RingRates.portStep_fire. -/
theorem record_fire {n : ℕ} (either : Bool) (r : Fin n → IsolatedRequests) (y : Fin n)
    (hf : RingReceiver.exchange either (r ((finRotate n).symm y)) = true) :
    RingReceiver.portStep either r (recordPortsN n y) =
      localizedPortsN n ((finRotate n).symm y) activePacket := by
  funext x
  rw [portStep_apply, arrivals_record]
  by_cases hx : x = (finRotate n).symm y
  · subst x
    simp_all [LocalController.applyGuard, localizedPortsN, active_activePacket]
  · simp_all [LocalController.applyGuard, localizedPortsN]

theorem step_ports {n : ℕ} (either : Bool) (r : Fin n → IsolatedRequests) (s : Located n) :
    ports (step either r s) = RingReceiver.portStep either r (ports s) := by
  rcases s with ⟨y, d⟩
  cases d
  · cases h : RingReceiver.exchange either (r (finRotate n y))
    · rw [show ports (y, false) = localizedPortsN n y activePacket from rfl,
        portStep_quiet either r y h]
      simp_all [ports, step, arrival]
    · rw [show ports (y, false) = localizedPortsN n y activePacket from rfl,
        portStep_fire either r y h]
      simp_all [ports, step, arrival]
  · cases h : RingReceiver.exchange either (r ((finRotate n).symm y))
    · rw [show ports (y, true) = recordPortsN n y from rfl,
        portStep_record_quiet either r y h]
      simp_all [ports, step, arrival]
    · rw [show ports (y, true) = recordPortsN n y from rfl, record_fire either r y h]
      simp_all [ports, step, arrival]

def trace {n : ℕ} (either : Bool) (r : Fin n → IsolatedRequests) (x0 : Fin n) (t : ℕ) : Located n :=
  (step either r)^[t] (x0, false)

theorem trace_ports {n : ℕ} (either : Bool) (r : Fin n → IsolatedRequests) (x0 : Fin n) (t : ℕ) :
    ports (trace either r x0 t) =
      (RingReceiver.portStep either r)^[t] (localizedPortsN n x0 activePacket) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [trace, Function.iterate_succ_apply'] at ih ⊢
    rw [step_ports, ih]

def reversal {n : ℕ} (either : Bool) (r : Fin n → IsolatedRequests) (s : Located n) : ℕ :=
  if (step either r s).2 ≠ s.2 then 1 else 0

theorem registration_eq_reversal {n : ℕ} (either : Bool)
    (r : Fin n → IsolatedRequests) (s : Located n) :
    tickCount either r (ports s) = reversal either r s := by
  rcases s with ⟨y, d⟩
  cases d
  · change tickCount either r (localizedPortsN n y activePacket) = _
    rw [tick_localized]
    cases h : RingReceiver.exchange either (r (finRotate n y)) <;>
      simp_all [reversal, step, arrival]
  · change tickCount either r (recordPortsN n y) = _
    rw [tick_record]
    cases h : RingReceiver.exchange either (r ((finRotate n).symm y)) <;>
      simp_all [reversal, step, arrival]

/-- Registration flips the stream in either direction. -/
theorem registration_iff_opposite_direction {n : ℕ} (either : Bool)
    (r : Fin n → IsolatedRequests) (s : Located n) :
    tickCount either r (ports s) = 1 ↔ (step either r s).2 = !s.2 := by
  rw [registration_eq_reversal]
  unfold reversal
  cases hd : s.2 <;> cases hk : (step either r s).2 <;> simp_all

theorem no_registration_iff_same_direction {n : ℕ} (either : Bool)
    (r : Fin n → IsolatedRequests) (s : Located n) :
    tickCount either r (ports s) = 0 ↔ (step either r s).2 = s.2 := by
  rw [registration_eq_reversal]
  simp [reversal]

def count {n : ℕ} (either : Bool) (r : Fin n → IsolatedRequests) (x0 : Fin n) (T : ℕ) : ℕ :=
  ∑ t ∈ Finset.range T, reversal either r (trace either r x0 t)

/-- Equality for arbitrary patterns, not just one-site firing. -/
theorem registrations_eq_reversals {n : ℕ} (either : Bool)
    (r : Fin n → IsolatedRequests) (x0 : Fin n) (T : ℕ) :
    localizedSumN n either r x0 T = count either r x0 T := by
  unfold localizedSumN count
  apply Finset.sum_congr rfl
  intro t _
  rw [sum_flag_eq_tick, ← trace_ports, registration_eq_reversal]

theorem direction_between_registrations {n : ℕ} (either : Bool)
    (r : Fin n → IsolatedRequests) (x0 : Fin n) (start len : ℕ)
    (h : ∀ j < len, tickCount either r (ports (trace either r x0 (start+j))) = 0) :
    (trace either r x0 (start+len)).2 = (trace either r x0 start).2 := by
  induction len with
  | zero => simp
  | succ len ih =>
    have hj := (no_registration_iff_same_direction either r _).mp (h len (by omega))
    change (trace either r x0 (start+(len+1))).2 = _
    rw [show start+(len+1) = (start+len)+1 by omega]
    rw [show trace either r x0 (start+len+1) =
      step either r (trace either r x0 (start+len)) from
      Function.iterate_succ_apply' _ _ _]
    rw [hj]
    exact ih (fun j hj => h j (by omega))

def total (p : EPSpine.Program) : ℕ :=
  count true (p.firing 0) p.x0 43 + count true (p.firing 1) p.x0 43

theorem total_eq_registrations (p : EPSpine.Program) :
    total p = SpacetimeProgram.registrationTotal p := by
  simp only [total, SpacetimeProgram.registrationTotal, registrations,
    EPSpine.Program.toRing, registrations_eq_reversals]

def footprint (p : EPSpine.Program) : PMSubstrate.OccupancyCost.Footprint := { events := total p }

theorem footprint_events (p : EPSpine.Program) :
    (footprint p).events = SpacetimeProgram.registrationTotal p := total_eq_registrations p

theorem footprint_cost (p : EPSpine.Program) :
    PMSubstrate.OccupancyCost.cost (footprint p) = (total p : ℝ) := by
  unfold footprint
  generalize total p = n
  simp [PMSubstrate.OccupancyCost.cost]

theorem footprint_ceiling (p : EPSpine.Program) : (footprint p).events ≤ 2 * PMSubstrate.E8Values.Delta :=
  SpacetimeProgram.footprint_bound p (footprint p) (footprint_events p)

/-- Fire only the differing bit ring; the equal ring stays empty. -/
def quietEqualRing (c : PMConstants.PacketGaugeActions.Channels) : Fin 2 → Fin 43 → IsolatedRequests :=
  fun b => if bitOf (labelRecord c) b ≠ bitOf (refRecord (leastRef c)) b
    then oneFiringN 43 0 else fun _ => (false, false)

theorem quiet_count (c : PMConstants.PacketGaugeActions.Channels) (x0 : Fin 43) (b : Fin 2) :
    localizedSumN 43 true (quietEqualRing c b) x0 43 =
      if bitOf (labelRecord c) b ≠ bitOf (refRecord (leastRef c)) b then 1 else 0 := by
  unfold quietEqualRing
  split_ifs
  · exact one_site_exact true 0 x0
  · exact empty_pattern_zero 43 43 true x0

theorem quiet_total (c : PMConstants.PacketGaugeActions.Channels) (x0 : Fin 43) :
    localizedSumN 43 true (quietEqualRing c 0) x0 43 +
      localizedSumN 43 true (quietEqualRing c 1) x0 43 = 1 := by
  rw [quiet_count, quiet_count]
  simpa [hamming, bitOf] using leastRef_hamming c

theorem quiet_pillars (c : PMConstants.PacketGaugeActions.Channels) (x0 : Fin 43)
    (hc : ProgramClasses.classOf c ≠ 4) :
    ProgramWitness.Pillars ⟨c, leastRef c, quietEqualRing c, x0⟩ := by
  refine ⟨?_, ?_, ?_, hc, ?_, ?_⟩
  · exact (quiet_total c x0).le.trans (by decide)
  · intro b hd
    change localizedSumN 43 true (quietEqualRing c b) x0 43 < 43
    change bitOf (labelRecord c) b ≠ bitOf (refRecord (leastRef c)) b at hd
    rw [quiet_count, ite_eq_left hd]
    decide
  · exact (leastRef_hamming c).symm.le
  · intro b hd
    change 1 ≤ localizedSumN 43 true (quietEqualRing c b) x0 43
    change bitOf (labelRecord c) b ≠ bitOf (refRecord (leastRef c)) b at hd
    rw [quiet_count, ite_eq_left hd]
  · refine ⟨0, 1, ?_⟩
    change RingReceiver.exchange true (quietEqualRing c 0 1) = false
    unfold quietEqualRing
    split_ifs <;> simp [oneFiringN, RingReceiver.exchange]

/-- All physical reversals dominate the differing-bit subtotal. -/
theorem total_floor (p : EPSpine.Program) (h : p.Pillars) : 1 ≤ total p := by
  apply (SpacetimeProgram.relevant_floor p h).trans
  rw [total_eq_registrations]
  unfold SpacetimeProgram.relevant ringTotal SpacetimeProgram.registrationTotal
  rw [← Fin.sum_univ_two]
  apply Finset.sum_le_sum
  intro b _
  split_ifs <;> simp [registrations, EPSpine.Program.toRing]

end PMElementaryParticles.ReversalEvents
