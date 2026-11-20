import PMElementaryParticles.IsolatedReceiverTrace
import PMElementaryParticles.HeavyFlipRecords
import PMElementaryParticles.WireSchedule

/-!
# Reference-background bit rings (candidate model for gap U)

**Candidate for gap U, hypothesis, not certified.**  The vacuum is the
reference record on both streams everywhere; a packet replaces the live bits
at one site by its label bits.  Each record bit, sector and position, runs on
its own ring with its own retained request field.

The colour reference record is `(false,false)` (the up record); the lepton
reference record is `(true,false)` (the neutrino record), in the
`(sector,position)` order of `labelRecord`.
-/

noncomputable section
namespace PMElementaryParticles.IsolatedExcitation

open PMConstants.PacketGaugeActions
open PMElementaryParticles.ProtocolInventory
open PMElementaryParticles.HeavyFlipControl
open PMElementaryParticles.WireSchedule
open PMTransport
open PMTransport.RingReceiver
open PMAction

/-- Hamming distance of two 2-bit records. -/
def hamming (a b : Record) : ℕ :=
  (if a.1 ≠ b.1 then 1 else 0) + (if a.2 ≠ b.2 then 1 else 0)

/-- Candidate reference record: colour = `(false,false)` (up),
lepton = `(true,false)` (neutrino), in `(sector,position)` order. -/
def refRecord (colourReference : Bool) : Record :=
  if colourReference then (false, false) else (true, false)

/-- Task H Step 1: the reference records reproduce both EP rows. -/
theorem bitToll_eq_hamming :
    ∀ (colourReference : Bool) (c : Channels),
      WireSchedule.bitToll colourReference c =
        (hamming (labelRecord c) (refRecord colourReference) : ℝ) := by
  intro colourReference c
  cases colourReference
  · rw [WireSchedule.bitToll, ElectricHeavyRecord.phase_position,
      ElectricHeavyRecord.phase_sector_lepton_reference]
    unfold hamming refRecord
    rcases h : labelRecord c with ⟨s, p⟩
    cases s <;> cases p <;> norm_num
  · rw [WireSchedule.bitToll, ElectricHeavyRecord.phase_position,
      ElectricHeavyRecord.phase_sector]
    unfold hamming refRecord
    rcases h : labelRecord c with ⟨s, p⟩
    cases s <;> cases p <;> norm_num

/-- The colour row is exactly the true-bit count of `labelRecord`. -/
theorem colour_hamming (c : Channels) :
    (hamming (labelRecord c) (refRecord true) : ℝ) = HeavyFlipRecords.orbitRecordToll c := by
  rw [← bitToll_eq_hamming true c]
  simpa [WireSchedule.bitToll] using ElectricHeavyRecord.colour_reference_toll c

def bitOf (p : Record) (b : Fin 2) : Bool :=
  if b = 0 then p.1 else p.2

/-! ## Step 1: complement symmetry -/

def complementPorts {n : ℕ} (ports : Fin n → IsolatedPorts) : Fin n → IsolatedPorts :=
  fun x => (!(ports x).1, !(ports x).2)

def complementPortState {n : ℕ} (s : RingReceiver.State n) : RingReceiver.State n :=
  (s.1, (s.2.1, (s.2.2.1, complementPorts s.2.2.2)))

theorem arrivals_complement {n : ℕ} (ports : Fin n → IsolatedPorts) (x : Fin n) :
    RingReceiver.arrivals (complementPorts ports) x =
      (!(RingReceiver.arrivals ports x).1, !(RingReceiver.arrivals ports x).2) := by
  simp [RingReceiver.arrivals, OpenReferenceFlow.streamShift, complementPorts]

theorem tick_complement (n : ℕ) (either : Bool) (s : RingReceiver.State n) :
    RingReceiver.tick n either (complementPortState s) =
      complementPortState (RingReceiver.tick n either s) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · funext x
        simp only [complementPortState, complementPorts]
        conv_lhs => rw [RingReceiver.tick_ports]
        conv_rhs => rw [RingReceiver.tick_ports]
        rw [arrivals_complement]
        unfold LocalController.applyGuard
        split <;> rfl

theorem receiverFlag_complement (n : ℕ) (either : Bool) (s : RingReceiver.State n)
    (x : Fin n) :
    RingReceiver.receiverFlag either (complementPortState s) x =
      RingReceiver.receiverFlag either s x := by
  simp [RingReceiver.receiver_flag_eq, complementPortState, complementPorts,
    arrivals_complement]

/-! ## Step 2: bit-ring embedding -/

def bitRingEmbed {n : ℕ} (refBit labelBit : Bool) (x0 : Fin n)
    (requests : Fin n → IsolatedRequests) : RingReceiver.State n :=
  (0, (requests, (fun _ => false,
    fun x => if x = x0 then (labelBit, refBit) else (refBit, refBit))))

theorem bitRingEmbed_uniform {n : ℕ} (refBit labelBit : Bool) (x0 : Fin n)
    (requests : Fin n → IsolatedRequests) (h : labelBit = refBit) :
    ∀ x, (bitRingEmbed refBit labelBit x0 requests).2.2.2 x = (refBit, refBit) := by
  intro x
  subst labelBit
  by_cases hx : x = x0 <;> simp [bitRingEmbed, hx]

theorem uniform_ports_tick_N (n : ℕ) (either : Bool) (s : RingReceiver.State n)
    (v : Bool) (h : ∀ x, s.2.2.2 x = (v, v)) (x : Fin n) :
    (RingReceiver.tick n either s).2.2.2 x = (v, v) := by
  rw [RingReceiver.tick_ports]
  have ha : RingReceiver.arrivals s.2.2.2 x = (v, v) := by
    simp [RingReceiver.arrivals, OpenReferenceFlow.streamShift, h]
  rw [ha]
  change LocalController.applyGuard
    (fun _ => RingReceiver.exchange either (s.2.1 x)) (v, v) = (v, v)
  unfold LocalController.applyGuard
  split <;> rfl

theorem uniform_ports_iterate_N (n : ℕ) (either : Bool) (s : RingReceiver.State n)
    (v : Bool) (h : ∀ x, s.2.2.2 x = (v, v)) (k : ℕ) :
    ∀ x, ((RingReceiver.tick n either)^[k] s).2.2.2 x = (v, v) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    intro x
    exact uniform_ports_tick_N n either _ v ih x

theorem receiverFlag_zero_of_uniform_N (n : ℕ) (either : Bool)
    (s : RingReceiver.State n) (v : Bool) (h : ∀ x, s.2.2.2 x = (v, v))
    (x : Fin n) :
    RingReceiver.receiverFlag either s x = 0 := by
  rw [RingReceiver.receiver_flag_eq]
  have ha : RingReceiver.arrivals s.2.2.2 x = (v, v) := by
    simp [RingReceiver.arrivals, OpenReferenceFlow.streamShift, h]
  rw [ha]
  simp

theorem bitRingEmbed_equal_zero {n : ℕ} (refBit labelBit : Bool) (x0 : Fin n)
    (requests : Fin n → IsolatedRequests) (h : labelBit = refBit) (either : Bool)
    (k : ℕ) (x : Fin n) :
    RingReceiver.receiverFlag either
      ((RingReceiver.tick n either)^[k] (bitRingEmbed refBit labelBit x0 requests)) x = 0 := by
  apply receiverFlag_zero_of_uniform_N n either _ refBit
  intro y
  exact uniform_ports_iterate_N n either _ refBit
    (bitRingEmbed_uniform refBit labelBit x0 requests h) k y

theorem bitRingEmbed_background_fixed {n : ℕ} (refBit : Bool) (x0 : Fin n)
    (requests : Fin n → IsolatedRequests) (either : Bool) (k : ℕ) :
    ((RingReceiver.tick n either)^[k]
      (bitRingEmbed refBit refBit x0 requests)).2.2.2 =
      (bitRingEmbed refBit refBit x0 requests).2.2.2 := by
  funext x
  rw [show (bitRingEmbed refBit refBit x0 requests).2.2.2 x = (refBit, refBit)
    from bitRingEmbed_uniform refBit refBit x0 requests rfl x]
  exact uniform_ports_iterate_N n either _ refBit
    (bitRingEmbed_uniform refBit refBit x0 requests rfl) k x

noncomputable def dummyVacuum : VacuumLabel 0 := Classical.choice (by infer_instance)

theorem bitRingEmbed_false_true (vacuum : VacuumLabel 0) (x0 : IsolatedSite)
    (requests : IsolatedSite → IsolatedRequests) :
    (bitRingEmbed false true x0 requests : RingReceiver.State 3) =
      localizedEmbed 0 vacuum activePacket x0 (mkFields requests) := by
  rfl

theorem bitRingEmbed_true_false (vacuum : VacuumLabel 0) (x0 : IsolatedSite)
    (requests : IsolatedSite → IsolatedRequests) :
    (bitRingEmbed true false x0 requests : RingReceiver.State 3) =
      complementPortState (localizedEmbed 0 vacuum activePacket x0 (mkFields requests)) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · funext x
        by_cases hx : x = x0 <;>
          simp [bitRingEmbed, complementPortState, complementPorts, localizedEmbed,
            localizedPorts, mkFields, activePacket, active, hx]

noncomputable def bitRingSum43 (either : Bool) (refBit labelBit : Bool)
    (x0 : IsolatedSite) (requests : IsolatedSite → IsolatedRequests) : ℝ :=
  ∑ t : Fin 43, ∑ x : IsolatedSite,
    RingReceiver.receiverFlag either ((RingReceiver.tick 3 either)^[t.val]
      (bitRingEmbed refBit labelBit x0 requests)) x

theorem bitRingSum43_eq (either : Bool) (refBit labelBit : Bool)
    (x0 : IsolatedSite) (requests : IsolatedSite → IsolatedRequests) :
    bitRingSum43 either refBit labelBit x0 requests =
      if labelBit ≠ refBit then (localizedSum43 either requests x0 : ℝ) else 0 := by
  by_cases h : labelBit = refBit
  · subst labelBit
    rw [if_neg (by simp)]
    unfold bitRingSum43
    apply Finset.sum_eq_zero
    intro t _
    apply Finset.sum_eq_zero
    intro x _
    exact bitRingEmbed_equal_zero refBit refBit x0 requests rfl either t.val x
  · rw [if_pos h]
    cases refBit
    · have hlabel : labelBit = true := by
        cases labelBit <;> simp_all
      subst labelBit
      unfold bitRingSum43
      rw [bitRingEmbed_false_true]
      exact localized_period_registrations_eq either requests dummyVacuum x0
    · have hlabel : labelBit = false := by
        cases labelBit <;> simp_all
      subst labelBit
      unfold bitRingSum43
      rw [bitRingEmbed_true_false]
      calc
        (∑ t : Fin 43, ∑ x : IsolatedSite,
          RingReceiver.receiverFlag either ((RingReceiver.tick 3 either)^[t.val]
            (complementPortState (localizedEmbed 0 dummyVacuum activePacket x0
              (mkFields requests)))) x)
          = ∑ t : Fin 43, ∑ x : IsolatedSite,
              RingReceiver.receiverFlag either ((RingReceiver.tick 3 either)^[t.val]
                (localizedEmbed 0 dummyVacuum activePacket x0 (mkFields requests))) x := by
            apply Finset.sum_congr rfl
            intro t _
            apply Finset.sum_congr rfl
            intro x _
            have hiter : ((RingReceiver.tick 3 either)^[t.val]
                (complementPortState (localizedEmbed 0 dummyVacuum activePacket x0
                  (mkFields requests)))) =
                complementPortState (((RingReceiver.tick 3 either)^[t.val]
                  (localizedEmbed 0 dummyVacuum activePacket x0
                    (mkFields requests)))) := by
              induction t.val with
              | zero => rfl
              | succ k ih =>
                rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
                  tick_complement]
            rw [hiter, receiverFlag_complement]
        _ = (localizedSum43 either requests x0 : ℝ) :=
            localized_period_registrations_eq either requests dummyVacuum x0

/-! ## Step 3: total over the two bit-rings -/

noncomputable def bitRingTotal43 (c : Channels) (colourReference : Bool) (either : Bool)
    (r : Fin 2 → IsolatedSite → IsolatedRequests) (x0 : IsolatedSite) : ℝ :=
  ∑ b : Fin 2,
    bitRingSum43 either (bitOf (refRecord colourReference) b)
      (bitOf (labelRecord c) b) x0 (r b)

theorem bitRingTotal43_eq (c : Channels) (colourReference : Bool) (either : Bool)
    (r : Fin 2 → IsolatedSite → IsolatedRequests) (x0 : IsolatedSite) :
    bitRingTotal43 c colourReference either r x0 =
      ∑ b : Fin 2,
        if bitOf (labelRecord c) b ≠ bitOf (refRecord colourReference) b then
          (localizedSum43 either (r b) x0 : ℝ) else 0 := by
  unfold bitRingTotal43
  apply Finset.sum_congr rfl
  intro b _
  exact bitRingSum43_eq either _ _ x0 (r b)

theorem bitRingTotal43_shared (c : Channels) (colourReference : Bool) (either : Bool)
    (r : IsolatedSite → IsolatedRequests) (x0 : IsolatedSite) :
    bitRingTotal43 c colourReference either (fun _ => r) x0 =
      WireSchedule.bitToll colourReference c *
        (patternSum (firingPattern either r) x0 : ℝ) := by
  rw [bitRingTotal43_eq, Fin.sum_univ_two, bitToll_eq_hamming]
  unfold hamming bitOf refRecord
  rcases h : labelRecord c with ⟨s, p⟩
  cases colourReference <;> cases s <;> cases p <;>
    simp [localizedSum43_eq_pattern, h] <;> ring

/-! ## Step 4: least Toll and zero-Hamming labels -/

theorem hamming_eq_zero_iff (a b : Record) : hamming a b = 0 ↔ a = b := by
  rcases a with ⟨a1, a2⟩
  rcases b with ⟨b1, b2⟩
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;>
    norm_num [hamming]

theorem firingPattern_empty (either : Bool) (x : IsolatedSite) :
    firingPattern either (fun _ => (false, false)) x = false := by
  cases either <;> rfl

theorem localizedSum43_empty_uniform (either : Bool) (x0 : IsolatedSite) :
    localizedSum43 either (fun _ => (false, false)) x0 = 0 := by
  rw [localizedSum43_eq_pattern]
  have hq : firingPattern either (fun _ => (false, false)) = fun _ => false := by
    funext x
    exact firingPattern_empty either x
  rw [hq]
  fin_cases x0 <;> decide +kernel

theorem bitRingSum43_empty_zero (either : Bool) (refBit labelBit : Bool)
    (x0 : IsolatedSite) :
    bitRingSum43 either refBit labelBit x0 (fun _ => (false, false)) = 0 := by
  unfold bitRingSum43
  apply Finset.sum_eq_zero
  intro t _
  apply Finset.sum_eq_zero
  intro x _
  rw [RingReceiver.receiver_flag_eq]
  have hq : ((RingReceiver.tick 3 either)^[t.val]
      (bitRingEmbed refBit labelBit x0 (fun _ => (false, false)))).2.1 x =
      (false, false) := by
    have hqall := RingReceiver.requests_iterate either
      (bitRingEmbed refBit labelBit x0 (fun _ => (false, false))) t.val
    exact congrFun (by simpa [bitRingEmbed] using hqall) x
  rw [hq]
  simp [RingReceiver.exchange]

theorem bitRingTotal43_empty_zero (c : Channels) (colourReference : Bool)
    (either : Bool) (x0 : IsolatedSite) :
    bitRingTotal43 c colourReference either
      (fun _ => fun _ => (false, false)) x0 = 0 := by
  unfold bitRingTotal43
  apply Finset.sum_eq_zero
  intro b _
  exact bitRingSum43_empty_zero either _ _ x0

theorem bitRingTotal43_hamming_zero (c : Channels) (colourReference : Bool)
    (either : Bool) (r : Fin 2 → IsolatedSite → IsolatedRequests)
    (x0 : IsolatedSite)
    (h : hamming (labelRecord c) (refRecord colourReference) = 0) :
    bitRingTotal43 c colourReference either r x0 = 0 := by
  have hrec : labelRecord c = refRecord colourReference :=
    (hamming_eq_zero_iff _ _).1 h
  rw [bitRingTotal43_eq]
  apply Finset.sum_eq_zero
  intro b _
  have hb : bitOf (labelRecord c) b = bitOf (refRecord colourReference) b := by
    rw [hrec]
  rw [if_neg]
  simp [hb]

end PMElementaryParticles.IsolatedExcitation
