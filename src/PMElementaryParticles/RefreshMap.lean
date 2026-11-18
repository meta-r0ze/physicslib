import PMElementaryParticles.ProtocolInventory
import PMConstants.GaugeLedgers
import PMConstants.ReferenceMaintenance
import PMTransport.Machine.RecordSupply
import PMTransport.Machine.CarrierWeyl
import PMTransport.Machine.ClockControlledRoot
import PMTransport.Machine.InBandRootReadout

/-! The least refinement of the protocol inventory that predicts the native weak
refresh. Two successive protocol observations recover the active/static distinction.
The result concerns channel routing over repeated refreshes. -/

namespace PMElementaryParticles.RefreshMap
open PMConstants.PacketGaugeActions PMElementaryParticles.ProtocolInventory

/-- Inventory information retained before the refresh. -/
def retained (c : Channels) := (baseProtocol c, active c)

/-- The protocol observations at the current and next tick. -/
def observations (c : Channels) := (baseProtocol c, baseProtocol (flipWeak c))

theorem retained_iff_observations : ∀ c d : Channels,
    retained c = retained d ↔ observations c = observations d := by decide +kernel

theorem occupied_count : (Finset.univ.image retained).card = 8 := by decide +kernel

theorem refresh_respects : ∀ c d : Channels, retained c = retained d →
    retained (flipWeak c) = retained (flipWeak d) := by decide +kernel

theorem colour_preserves : ∀ a b : Fin 3, ∀ c : Channels,
    retained (permuteColour a b c) = retained c := by decide +kernel

theorem two_ticks : ∀ c : Channels, flipWeak (flipWeak c) = c := by decide +kernel

/-- Any deterministic state description that reads the current protocol and
updates correctly must distinguish every pair distinguished by 'retained'. -/
theorem minimal {S : Type*} (encode : Channels → S) (step : S → S)
    (readout : S → Option BaseProtocol)
    (reads : ∀ c, readout (encode c) = baseProtocol c)
    (updates : ∀ c, step (encode c) = encode (flipWeak c))
    {c d : Channels} (h : encode c = encode d) : retained c = retained d := by
  apply (retained_iff_observations c d).2
  apply Prod.ext
  · exact (reads c).symm.trans ((congrArg readout h).trans (reads d))
  · have hn := (updates c).symm.trans ((congrArg step h).trans (updates d))
    exact (reads _).symm.trans ((congrArg readout hn).trans (reads _))

section Payload
open PMConstants.GaugeLedgers PMAction.ReferenceMaintenance

/-- The inventory channel's address in the existing payload ledger. -/
def payloadRow (c : Channels) : Res := .payload (channelIndex c)

theorem payload_required (c : Channels) : payloadRow c ∈ reqY := by
  simp [payloadRow, reqY]

/-- On a canonical hypercharge visit the old record becomes the live discrepancy
and the old live discrepancy becomes the record, including on occupied input. -/
theorem payload_visit (s : State Res) (c : Channels) :
    run reqY.toList s (payloadRow c) = ((s (payloadRow c)).2, (s (payloadRow c)).1) := by
  simp [run_nodup _ reqY.nodup_toList, payload_required]

/-- Predicting the next live payload bit for every incoming record array
distinguishes precisely the individual channel addresses. -/
theorem same_payload_readout_iff (c d : Channels) :
    (∀ s : State Res, (run reqY.toList s (payloadRow c)).1 =
      (run reqY.toList s (payloadRow d)).1) ↔ c = d := by
  constructor
  · intro h
    by_contra hne
    have hr : payloadRow d ≠ payloadRow c := fun he =>
      hne (channel_index_bijective.injective (payload_inj he)).symm
    have hbit := h (fun r => (false, decide (r = payloadRow c)))
    simp [payload_visit, hr] at hbit
  · rintro rfl
    exact fun _ => rfl

/-- Two bulk channels can have identical routing and different next live bits. -/
theorem routing_misses_payload :
    ∃ c d : Channels, retained c = retained d ∧
      ∃ s : State Res, (run reqY.toList s (payloadRow c)).1 ≠
        (run reqY.toList s (payloadRow d)).1 := by
  classical
  let c : Channels := .inl (0, 0)
  let d : Channels := .inl (1, 0)
  refine ⟨c, d, rfl, ?_⟩
  exact not_forall.mp (fun h => (by decide : c ≠ d) ((same_payload_readout_iff c d).mp h))

/-- A supply carrying a whole ledger array per packet. Initially all records
are clean. The live input marks the payload address of one supplied channel.
Common transport of the array and this preparation are explicit hypotheses
of the application to the wire. -/
def markedSupply {X : Type*} (source : Channels) (_ : X) : (Res → Bool) × (Res → Bool) :=
  (fun r => decide (r = payloadRow source), fun _ => false)

/-- On an orbit of least period N, the first N live outputs have clean payloads.
At visit N+1 the live output identifies the marked address exactly. -/
theorem marked_payload_return {X : Type*} [DecidableEq X] (o : X) (e : Equiv.Perm X)
    (N : ℕ) (hN : 1 ≤ N) (hclose : (e ^ N) o = o)
    (hmin : ∀ m, 1 ≤ m → m < N → (e ^ m) o ≠ o) (source c : Channels) :
    (∀ t, 1 ≤ t → t ≤ N →
      (PMAction.RecordSupply.run o e t (markedSupply source) o).1 (payloadRow c) = false) ∧
    ((PMAction.RecordSupply.run o e (N + 1) (markedSupply source) o).1 (payloadRow c) = true
      ↔ c = source) := by
  constructor
  · intro t ht htN
    rw [PMAction.RecordSupply.clean_supply o e (markedSupply source) (fun _ => false) N
      (fun _ _ _ => rfl) hmin t ht htN]
  · rw [PMAction.RecordSupply.ring_returns o e (markedSupply source) N hN hclose hmin]
    change decide (payloadRow c = payloadRow source) = true ↔ c = source
    rw [decide_eq_true_eq]
    exact ⟨fun h => channel_index_bijective.injective (payload_inj h), congrArg payloadRow⟩

/-- The same live disturbance on a nonreturning orbit never appears in the
live payload readout at the repair site. -/
theorem marked_payload_open {X : Type*} [DecidableEq X] (o : X) (e : Equiv.Perm X)
    (hopen : ∀ m, 1 ≤ m → (e ^ m) o ≠ o) (source c : Channels) (t : ℕ) :
    (PMAction.RecordSupply.run o e (t + 1) (markedSupply source) o).1 (payloadRow c) = false := by
  rw [PMAction.RecordSupply.live_at_site o e _ t (fun j _ => hopen (1 + j) (by omega))]
  rfl

/-- Candidate feedback: consult the bit addressed by the incoming channel and
apply one weak flip when it is set. The array is held fixed during this step. -/
def feedback (bits : Channels → Bool) (c : Channels) : Channels :=
  if bits c then flipWeak c else c

/-- With a fixed array this candidate is reversible on channels exactly when
weak partners read equal bits. Otherwise the two partners collide. -/
theorem feedback_injective_iff (bits : Channels → Bool) :
    Function.Injective (feedback bits) ↔ ∀ c, bits (flipWeak c) = bits c := by
  constructor
  · intro hinj c
    by_contra hne
    have heq : feedback bits (flipWeak c) = feedback bits c := by
      cases h : bits c <;> cases hf : bits (flipWeak c) <;>
        simp_all [feedback, two_ticks]
    exact hne (congrArg bits (hinj heq))
  · intro h
    apply Function.Involutive.injective
    intro c
    cases hb : bits c <;> simp [feedback, hb, h, two_ticks]

/-- Readout test for all channels, including the vacancy. -/
theorem feedback_changes_iff (bits : Channels → Bool) (c : Channels) :
    baseProtocol (feedback bits c) ≠ baseProtocol c ↔ bits c = true ∧ active c = true := by
  have h : ∀ d : Channels, baseProtocol (flipWeak d) ≠ baseProtocol d ↔ active d = true :=
    by decide +kernel
  cases hb : bits c <;> simp [feedback, hb, h]

/-- A record marking one active channel fails the reversibility test. -/
theorem single_active_collision (source : Channels) (ha : active source = true) :
    ¬ Function.Injective (feedback (fun c => decide (c = source))) := by
  intro hinj
  have h := (feedback_injective_iff _).mp hinj source
  have fixed : flipWeak source = source := by simpa using h
  have moves : ∀ c : Channels, active c = true → flipWeak c ≠ c := by decide +kernel
  exact moves source ha fixed

/-- Candidate local coupling. Visit the incoming channel's payload row and
route on its returned live bit, keeping the entire resulting ledger. -/
def visitRoute (c : Channels) (s : State Res) : Channels × State Res :=
  let out := event (payloadRow c) s
  (feedback (fun d => (out (payloadRow d)).1) c, out)

/-- If incoming payload live bits are clear, the output alone recovers the
input channel. Only the partner of the output needs to be probed. -/
theorem recover_visit_channel (c : Channels) (s : State Res)
    (hc : ∀ d, (s (payloadRow d)).1 = false) :
    let (q, out) := visitRoute c s
    (if (out (payloadRow (flipWeak q))).1 then flipWeak q else q) = c := by
  by_cases hb : (s (payloadRow c)).2 = true
  · simp [visitRoute, feedback, event, hb, two_ticks]
  · by_cases he : payloadRow (flipWeak c) = payloadRow c
    · simp [visitRoute, feedback, event, he, hb]
    · simp [visitRoute, feedback, event, he, hb, hc]

/-- The addressed swap is its own inverse once the channel is recovered. -/
theorem visitRoute_clean_injective (c d : Channels) (s t : State Res)
    (hs : ∀ a, (s (payloadRow a)).1 = false)
    (ht : ∀ a, (t (payloadRow a)).1 = false)
    (h : visitRoute c s = visitRoute d t) : c = d ∧ s = t := by
  have hc := recover_visit_channel c s hs
  rw [h] at hc
  have hcd := hc.symm.trans (recover_visit_channel d t ht)
  subst d
  exact ⟨rfl, (event_involutive (payloadRow c)).injective (congrArg Prod.snd h)⟩

/-- With arbitrary occupied live inputs the same local coupling admits a
collision even with the entire outgoing ledger observed. -/
theorem visitRoute_collision (c : Channels) (hm : flipWeak c ≠ c) :
    ∃ s : State Res, visitRoute c s = visitRoute (flipWeak c) s := by
  let bit := fun r : Res => decide (r = payloadRow c)
  let s : State Res := fun r => (bit r, bit r)
  have idle (r : Res) : event r s = s := by
    funext j
    simp [event, s]
  have hr : payloadRow (flipWeak c) ≠ payloadRow c :=
    fun h => hm (channel_index_bijective.injective (payload_inj h))
  exact ⟨s, by simp [visitRoute, idle, feedback, s, bit, hr]⟩

/-- The weak flip moves exactly the active channels; static channels are fixed. -/
theorem moves_iff_active : ∀ a : Channels, flipWeak a ≠ a ↔ active a = true := by decide +kernel

/-- Recovery needs only the partner's live bit to be clear. A fixed channel needs nothing. -/
theorem recover_partner_clean (c : Channels) (s : State Res)
    (hc : flipWeak c ≠ c → (s (payloadRow (flipWeak c))).1 = false) :
    let (q, out) := visitRoute c s
    (if (out (payloadRow (flipWeak q))).1 then flipWeak q else q) = c := by
  by_cases hb : (s (payloadRow c)).2 = true
  · simp [visitRoute, feedback, event, hb, two_ticks]
  · by_cases he : payloadRow (flipWeak c) = payloadRow c
    · simp [visitRoute, feedback, event, he, hb]
    · have hm : flipWeak c ≠ c := fun h => he (congrArg payloadRow h)
      simp [visitRoute, feedback, event, he, hb, hc hm]

/-- **The Map's clean requirement.** The addressed visit with routing is reversible on
every input whose active payload rows have clear live bits. Static rows may be occupied.
With `visitRoute_collision`, one occupied active row already breaks it, so the clear
active rows are exactly what every protocol needs for its route to succeed. -/
theorem visitRoute_active_clean_injective (c d : Channels) (s t : State Res)
    (hs : ∀ a, active a = true → (s (payloadRow a)).1 = false)
    (ht : ∀ a, active a = true → (t (payloadRow a)).1 = false)
    (h : visitRoute c s = visitRoute d t) : c = d ∧ s = t := by
  have side (x : Channels) (u : State Res)
      (hu : ∀ a, active a = true → (u (payloadRow a)).1 = false) :
      flipWeak x ≠ x → (u (payloadRow (flipWeak x))).1 = false := fun hm =>
    hu _ ((moves_iff_active (flipWeak x)).mp (by rwa [two_ticks, ne_comm]))
  have hc := recover_partner_clean c s (side c s hs)
  rw [h] at hc
  have hcd := hc.symm.trans (recover_partner_clean d t (side d t ht))
  subst d
  exact ⟨rfl, (event_involutive (payloadRow c)).injective (congrArg Prod.snd h)⟩

/-- **An unequal gate on a weak pair must write the doublet position.** If a conditional
toggle reads different bits on two weak partners, the partners collide on the channel. Any
reversible extension must then export a record that separates them. -/
theorem asymmetric_gate_records {R : Type*} (bits : Channels → Bool) (r : Channels → R)
    (hinj : Function.Injective (fun c => (feedback bits c, r c))) (c : Channels)
    (hasym : bits (flipWeak c) ≠ bits c) : r (flipWeak c) ≠ r c := by
  have heq : feedback bits (flipWeak c) = feedback bits c := by
    cases h : bits c <;> cases hf : bits (flipWeak c) <;> simp_all [feedback, two_ticks]
  intro hr
  have hfc : flipWeak c = c := hinj (by simp only [Prod.mk.injEq]; exact ⟨heq, hr⟩)
  exact hasym (by rw [hfc])

/-- Coordinates on a moving weak pair, indexed by the two possible positions. -/
abbrev PairState := Bool × (Bool → Bool × Bool)

def pairVisit (x : PairState) : PairState :=
  let (i, rows) := x
  (if (rows i).2 then !i else i,
    fun j => if j = i then ((rows j).2, (rows j).1) else rows j)

def partner (c : Channels) (i : Bool) := if i then flipWeak c else c

/-- Projection of the actual ledger visit onto the two addressed rows. -/
theorem pairVisit_exact (c : Channels) (hm : flipWeak c ≠ c) (i : Bool) (s : State Res) :
    let (q, out) := visitRoute (partner c i) s
    let y := pairVisit (i, fun j => s (payloadRow (partner c j)))
    q = partner c y.1 ∧ (fun j => out (payloadRow (partner c j))) = y.2 := by
  have hn : payloadRow (flipWeak c) ≠ payloadRow c :=
    fun h => hm (channel_index_bijective.injective (payload_inj h))
  cases i <;> constructor
  all_goals first | funext j; cases j | skip
  all_goals simp [feedback, event, partner, pairVisit, hn, Ne.symm hn, two_ticks]
  all_goals split <;> simp_all

def cleanPair (i : Bool) (records : Bool → Bool) : PairState :=
  (i, fun j => (false, records j))

/-- From a clean preparation every pair trajectory repeats after four further
visits once the first visit has taken place. Shorter periods are included. -/
theorem pair_repeat : ∀ i r,
    pairVisit^[5] (cleanPair i r) = pairVisit (cleanPair i r) := by decide +kernel

/-- With a known visit count, the two rows and the current position identify
the clean preparation, for arbitrarily many visits without transport. -/
theorem pair_clean_recover (n : ℕ) (i j : Bool) (r t : Bool → Bool)
    (h : pairVisit^[n] (cleanPair i r) = pairVisit^[n] (cleanPair j t)) :
    i = j ∧ r = t := by
  have small : ∀ m : Fin 5, ∀ a b u v,
      pairVisit^[m.val] (cleanPair a u) = pairVisit^[m.val] (cleanPair b v) →
      a = b ∧ u = v := by decide +kernel
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 5
    · exact small ⟨n, hn⟩ i j r t h
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
      rw [Function.iterate_add_apply, Function.iterate_add_apply, pair_repeat, pair_repeat] at h
      apply ih (k + 1) (by omega)
      simpa only [Function.iterate_add_apply, Function.iterate_one] using h

/-- At a fixed channel only the addressed swap remains, so two visits
restore even an initially occupied ledger. -/
theorem fixed_visit_twice (c : Channels) (hc : flipWeak c = c) (s : State Res) :
    let (q, out) := visitRoute c s
    visitRoute q out = (c, s) := by
  simp [visitRoute, feedback, hc, event_involutive (payloadRow c) s]

/-- Candidate readout after each native supply tick. The stream advances
independently of the channel; feedback samples its new live payload at o. -/
def streamRoute {X : Type*} [DecidableEq X] (o : X) (e : Equiv.Perm X)
    (s : X → (Res → Bool) × (Res → Bool)) : ℕ → Channels → Channels
  | 0, c => c
  | n + 1, c => feedback (fun d => (PMAction.RecordSupply.run o e (n+1) s o).1
      (payloadRow d)) (streamRoute o e s n c)

/-- A clean readout throughout an interval leaves every route unchanged. -/
theorem streamRoute_clean {X : Type*} [DecidableEq X] (o : X) (e : Equiv.Perm X)
    (s : X → (Res → Bool) × (Res → Bool)) (n : ℕ)
    (h : ∀ t, 1 ≤ t → t ≤ n → ∀ d, (PMAction.RecordSupply.run o e t s o).1
      (payloadRow d) = false) (c : Channels) : streamRoute o e s n c = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [streamRoute, ih (fun t ht hn => h t ht (by omega))]
    simp [feedback, h (n+1) (by omega) le_rfl]

/-- At the first return the entire route history reduces to the single
address gate, since none of the preceding visits read a mark. -/
theorem streamRoute_first_return {X : Type*} [DecidableEq X] (o : X) (e : Equiv.Perm X)
    (N : ℕ) (hN : 1 ≤ N) (hclose : (e ^ N) o = o)
    (hmin : ∀ m, 1 ≤ m → m < N → (e ^ m) o ≠ o) (source : Channels) :
    streamRoute o e (markedSupply source) (N+1) =
      feedback (fun d => decide (d = source)) := by
  funext c
  rw [streamRoute, streamRoute_clean o e _ N (fun t ht hn d =>
    (marked_payload_return o e N hN hclose hmin source d).1 t ht hn)]
  rw [PMAction.RecordSupply.ring_returns o e _ N hN hclose hmin]
  have hrow (d : Channels) : payloadRow d = payloadRow source ↔ d = source :=
    ⟨fun h => channel_index_bijective.injective (payload_inj h), congrArg payloadRow⟩
  simp [markedSupply, feedback, hrow]

section NativePorts
open PMAction.NativeReferenceBackground PMAction.NativeCarrierState
variable {X : Type*} [DecidableEq X]

/-- If native configuration values carry inventory channels, the output record
contains the incoming live channel itself. A specified conditional weak route
is realized exactly when the arriving record already carries that target. -/
theorem native_route_iff (o : X) (e : Equiv.Perm X) (s : Config X Channels)
    (i : Fin 2) (bits : Channels → Bool) :
    let input := (readPair s i (e⁻¹ o)).1
    let target := feedback bits input
    readPair (tick o e s) i o = (target, input) ↔ (readPair s i (e o)).2 = target := by
  simp [readPair_step, advance]

/-- Even when two routes have identical outgoing live channels, their distinct
incoming channels are recovered from the departing native record. -/
theorem native_outputs_distinct (o : X) (e : Equiv.Perm X) (s t : Config X Channels)
    (i : Fin 2) (h : (readPair s i (e⁻¹ o)).1 ≠ (readPair t i (e⁻¹ o)).1) :
    readPair (tick o e s) i o ≠ readPair (tick o e t) i o := by
  intro he
  apply h
  simpa [readPair_step, advance] using congrArg Prod.snd he

/-- The native port addresses themselves preserve doublet position under
the exchange. Reading the root permutation as a weak sign flip fails. -/
theorem repair_root_preserves_position : ∀ v : PMAction.ActualRootRepair.C,
    PMConstants.CarrierRepresentation.positive (PMAction.ActualRootRepair.root v) =
      PMConstants.CarrierRepresentation.positive v := by decide +kernel

/-- One fixed reference channel cannot supply the target for the full inventory.
The two static nonbulk slots remain distinct under every choice of bits. -/
theorem no_common_target (bits : Channels → Bool) :
    ¬ ∃ q, ∀ c, feedback bits c = q := by
  rintro ⟨q, h⟩
  let a : Channels := .inr (.inr (.inr 0))
  let b : Channels := .inr (.inr (.inr 1))
  have eq := (h a).trans (h b).symm
  have ha : flipWeak a = a := rfl
  have hb : flipWeak b = b := rfl
  exact (by decide : a ≠ b) (by simpa [feedback, ha, hb] using eq)

/-- Canonical address of a weak orbit, possibly a singleton. -/
def orbitIndex (c : Channels) := min (channelIndex c) (channelIndex (flipWeak c))

theorem orbit_count : (Finset.univ.image orbitIndex).card = 12 := by decide +kernel

theorem feedback_orbit (bits : Channels → Bool) (c : Channels) :
    orbitIndex (feedback bits c) = orbitIndex c := by
  cases h : bits c <;> simp [feedback, h, orbitIndex, two_ticks, min_comm]

/-- Even a selector allowed to inspect the channel must have at least one
stored target per weak orbit if its output is a literal channel value. -/
theorem target_table_bound {I : Type*} [Fintype I] (bits : Channels → Bool)
    (value : I → Channels) (pick : Channels → I)
    (supplies : ∀ c, value (pick c) = feedback bits c) : 12 ≤ Fintype.card I := by
  have sub : Finset.univ.image orbitIndex ⊆
      Finset.univ.image (fun i => orbitIndex (value i)) := by
    intro a ha
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_image.mpr ⟨pick c, Finset.mem_univ _, by rw [supplies, feedback_orbit]⟩
  rw [← orbit_count]
  exact (Finset.card_le_card sub).trans (Finset.card_image_le.trans (by simp))

/-- On a connected stationary native background each port's record value is
constant along the orbit. Picking a site and one of the two ports cannot
supply the conditional weak target for every channel. -/
theorem stationary_source_insufficient [Fintype X] (o : X) (e : Equiv.Perm X)
    (hc : Connected o e) (s : Config X Channels) (hs : tick o e s = s)
    (bits : Channels → Bool) (site : Channels → X) (port : Channels → Fin 2) :
    ¬ ∀ c, (readPair s (port c) (site c)).2 = feedback bits c := by
  intro h
  obtain ⟨r, hr⟩ := (stationary_iff o e hc s).mp hs
  have bound := target_table_bound bits r port (fun c =>
    ((hr (site c) (port c)).2).symm.trans (h c))
  norm_num at bound

/-- Address-order convention for the position within a weak orbit. -/
def orbitPosition (c : Channels) : Bool := decide (channelIndex c ≠ orbitIndex c)

theorem orbit_and_position_identify : Function.Injective
    (fun c => (orbitIndex c, orbitPosition c)) := by
  intro c d
  exact (by decide +kernel : ∀ a b : Channels,
    (orbitIndex a, orbitPosition a) = (orbitIndex b, orbitPosition b) → a = b) c d

/-- When the packet keeps its orbit, the routing update on the remaining
coordinate is one conditional bit toggle. Fixed channels keep their position. -/
theorem feedback_position (bits : Channels → Bool) (c : Channels) :
    orbitPosition (feedback bits c) =
      if bits c && active c then !(orbitPosition c) else orbitPosition c := by
  have step : ∀ a : Channels, orbitPosition (flipWeak a) =
      if active a then !(orbitPosition a) else orbitPosition a := by decide +kernel
  cases h : bits c <;> simp [feedback, h, step]

end NativePorts

section ClockControl
open PMAction PMConstants.CarrierActions

/-- A supplied common bit gates the existing antipodal Weyl word on the
active bank. The other bank passes through. This specifies no pulse duration. -/
theorem gated_word_matches (b : Bool) (c : Channels) :
    channelEquiv (feedback (fun _ => b) c) =
      (if b then Equiv.sumCongr (CarrierWeyl.lookup 0 5) (Equiv.refl _) (channelEquiv c)
       else channelEquiv c) := by
  cases b
  · rfl
  · rw [show feedback (fun _ => true) c = flipWeak c by rfl, weak_label_matches]
    cases h : channelEquiv c with
    | inl v => exact congrArg Sum.inl (CarrierWeyl.lookup_antipode 0 v).symm
    | inr v => rfl

/-- Candidate clock coupling: read the library's mask-change bit at each
phase and use it to gate the complete active-bank word. -/
def clockRoute (mask : Fin Delta → Bool) (t : Fin Delta) : ℕ → Channels → Channels
  | 0, c => c
  | n+1, c => feedback (fun _ => ClockControlledRoot.fire mask ((finRotate Delta)^[n] t))
      (clockRoute mask t n c)

/-- The cumulative toggle depends only on the initial and final mask values. -/
theorem clockRoute_endpoints (mask : Fin Delta → Bool) (t : Fin Delta) (n : ℕ) (c : Channels) :
    clockRoute mask t n c =
      feedback (fun _ => decide (mask ((finRotate Delta)^[n] t) ≠ mask t)) c := by
  induction n with
  | zero => simp [clockRoute, feedback]
  | succ n ih =>
    rw [clockRoute, ih, Function.iterate_succ_apply']
    unfold ClockControlledRoot.fire feedback
    cases mask t <;> cases mask ((finRotate Delta)^[n] t) <;>
      cases mask (finRotate Delta ((finRotate Delta)^[n] t)) <;> simp [two_ticks]

theorem clockRoute_closes (mask : Fin Delta → Bool) (t : Fin Delta) (c : Channels) :
    clockRoute mask t Delta c = c := by
  rw [clockRoute_endpoints, CarrierReferenceCycle.clock_closes t]
  simp [feedback]

open PMSubstrate.Lattices PMAction.SubstrateReflection

/-- In the existing one-phase excursion, let the packet sample the in-band
record once, after the first tick. The remaining ticks advance only the probe
and clock. Sampling the record to gate the packet is the coupling premise. -/
def sampledCycle (z : Lattice) (c : Channels) : ClockControlledRoot.State × Channels :=
  let tick := ClockControlledRoot.update CarrierReferenceCycle.excursionMask
  let atRead := tick (z, 0)
  (tick^[Delta - 1] atRead, feedback (fun _ => InBandRootReadout.record atRead.1) c)

/-- After the cycle the probe and clock return exactly. A clean accumulator
controls the packet by the parity of its substrate root pairing. -/
theorem sampledCycle_result (z : Lattice) (hz : InBandRootReadout.record z = false)
    (c : Channels) :
    sampledCycle z c = ((z, 0), feedback (fun _ => MatchedLatticeProbe.outcome root z) c) := by
  have hc : (ClockControlledRoot.update CarrierReferenceCycle.excursionMask)^[Delta - 1]
      (ClockControlledRoot.update CarrierReferenceCycle.excursionMask (z, 0)) = (z, 0) := by
    rw [← Function.iterate_succ_apply,
      show (Delta - 1).succ = Delta from Nat.sub_add_cancel (show (1 : ℕ) ≤ 43 by norm_num)]
    exact InBandRootReadout.schedule_closes (z, 0)
  show ((ClockControlledRoot.update CarrierReferenceCycle.excursionMask)^[Delta - 1]
      (ClockControlledRoot.update CarrierReferenceCycle.excursionMask (z, 0)),
      feedback (fun _ => InBandRootReadout.record
        (ClockControlledRoot.update CarrierReferenceCycle.excursionMask (z, 0)).1) c) = _
  rw [hc, InBandRootReadout.scheduled_read z hz]

/-- The two outcomes occur already on the same minimal quadratic shell,
with clean accumulators in both cases. -/
theorem clean_shell_both_controls : ∀ b : Bool, ∃ z : Lattice,
    pairing z z = 2 ∧ InBandRootReadout.record z = false ∧
      MatchedLatticeProbe.outcome root z = b := by
  intro b
  cases b
  · exact ⟨Pi.single 7 1, by decide +kernel⟩
  · exact ⟨Pi.single 0 1, by decide +kernel⟩

end ClockControl

end Payload

end PMElementaryParticles.RefreshMap
