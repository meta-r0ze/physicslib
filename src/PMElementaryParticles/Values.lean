import PMElementaryParticles.SharedUnits
import PMElementaryParticles.PhysicalUnits
import PMElementaryParticles.LeptonMasses
import PMElementaryParticles.QuarkMasses
import PMElementaryParticles.MuonLifetimeCorrected
import PMElementaryParticles.MuonLifetimeHigherOrder
import PMElementaryParticles.TauLifetimeCorrected
import PMElementaryParticles.WireReferenceCost
import PMElementaryParticles.IsolatedTrace
import PMElementaryParticles.TierLedger
import PMTransport.Values

/-!
# PMElementaryParticles canonical values

Single import for the units, couplings, masses and lifetimes that later libraries
(`PMHadrons`, `PMAtoms`, `e8p`) use, mirroring `PMSubstrate.E8Values`, `PMConstants.Values` and
`PMFlavor.Values`. Use these names instead of re-proving a bound locally.

* Units (CODATA 2022 inputs): `me` (MeV), `hbarc` (MeV·fm), `electronTime` (s) with
  `electronTime_tight`.
* Couplings: `αe`, `αinv` with `a_b`, `g_b`; `fermiME` (`G_F` in `m_e⁻²`) with `fermiME_pos` and
  `fermiME_tight` (`3.0456453–3.0456507 × 10⁻¹²`); `pi_b`.
* Masses (`m_e` units): `muon`, `tau` with `muon_value`, `tau_value`; quarks `up … top` with
  `up_value … top_value` (in MeV).
* Lifetimes: `muonLifetimeSeconds` (tree level) with `muonLifetimeSeconds_tight`,
  `muonLifetimeCorrected` (derived phase factor, supplied one-loop QED) with `corrected_bounds`,
  `muonLifetimeFull` (the full Fermi-theory QED series of van Ritbergen–Stuart, supplied, at E8
  inputs) with `muonLifetimeFull_bounds` (`2.196974–2.196984 µs`),
  `tauLifetimeSeconds` with `tauLifetimeSeconds_bounds`; `tauLifetimeCorrectedFs` (the measured-`τ_μ`,
  supplied-`B_e` tau lifetime with the corrected partial-width ratio) with
  `tauLifetimeCorrectedFs_bounds` (`291.03–291.06` fs).
-/

namespace PMElementaryParticles.Values

export PMElementaryParticles.SharedUnits
  (me hbarc αe αinv fermiME pi_b a_b g_b fermiME_pos fermiME_tight)
export PMElementaryParticles.PhysicalUnits
  (electronTime electronTime_pos electronTime_tight muonLifetimeSeconds muonLifetimeSeconds_tight
    tauLifetimeSeconds tauLifetimeSeconds_bounds)
export PMElementaryParticles.MuonLifetimeCorrected (muonLifetimeCorrected corrected_bounds)

/-- The muon lifetime with the full Fermi-theory QED series. -/
noncomputable abbrev muonLifetimeFull : ℝ := PMElementaryParticles.MuonLifetimeHigherOrder.lifetime

theorem muonLifetimeFull_bounds :
    (2.196974e-6 : ℝ) < muonLifetimeFull ∧ muonLifetimeFull < (2.196984e-6 : ℝ) :=
  PMElementaryParticles.MuonLifetimeHigherOrder.lifetime_bounds

/-- The conditional tau lifetime (fs) with the corrected partial-width ratio. -/
noncomputable abbrev tauLifetimeCorrectedFs : ℝ := PMElementaryParticles.TauLifetimeCorrected.tauLifeCorrected

theorem tauLifetimeCorrectedFs_bounds :
    (291.03 : ℝ) < tauLifetimeCorrectedFs ∧ tauLifetimeCorrectedFs < 291.06 :=
  PMElementaryParticles.TauLifetimeCorrected.tau_lifetime_corrected
export PMElementaryParticles.LeptonMasses (muon tau muon_value tau_value)
export PMElementaryParticles.QuarkMasses
  (up down strange charm bottom top up_value down_value strange_value charm_value bottom_value
    top_value)

/-! ## Finite Transport witness family

These eight rows index the hold/FIFO, AND/OR and placement witnesses.
They do not enumerate all possible physical EP updates. The first two
projections are the bank motion and the receiver rule. The third is the
choice of excursion example. Physical readout and work remain inputs.
-/

namespace TransportCandidates

open PMConstants.PacketGaugeActions
open ProtocolInventory

abbrev Candidate := Bool × Bool × Bool

def bools : List Bool := [false, true]

def candidates : List Candidate :=
  bools.flatMap fun fifo => bools.flatMap fun either => bools.map fun shifted =>
    (fifo, either, shifted)

theorem candidates_complete : ∀ c : Candidate, c ∈ candidates := by
  decide +kernel

theorem candidates_count : candidates.length = 8 ∧ candidates.Nodup := by
  decide +kernel

def phases (c : Candidate) : Fin PMTransport.Values.Delta × Fin PMTransport.Values.Delta :=
  PMTransport.Values.excursionSlots c.2.2

/-- Unit comparison registrations per tick at site zero if the mixed
basis input is supplied and all visits are booked. This is a receiver
account, not a physical EP writer cost. -/
def allBookedMixedRate (c : Candidate) : ℕ := if c.2.1 then 1 else 0

theorem allBookedMixedRate_eq (c : Candidate) :
    (allBookedMixedRate c : ℝ) =
      PMTransport.Values.mixedReceiverRate c.2.1 (fun _ => true) := by
  rw [PMTransport.Values.mixedReceiverRate_all_booked]
  by_cases h : c.2.1 <;> simp [allBookedMixedRate, h]

/-- The common input measures the writer's booked population. The reset
and other terms are actual paid work per input in this same account.
A negative colour-minus-lepton difference favours colour. -/
noncomputable def referenceDifference (c : Candidate)
    (bookedMass : Candidate → Channels → ℝ)
    (erased remaining : Candidate → Bool → ℝ) : ℝ :=
  2 * (∑ x ∈ Finset.univ.filter (fun x : Channels => ProtocolInventory.colourBulk x = false),
      bookedMass c x) - (∑ x, bookedMass c x) +
    (erased c true - erased c false) + (remaining c true - remaining c false)

theorem referenceDifference_eq (c : Candidate)
    (bookedMass : Candidate → Channels → ℝ)
    (erased remaining : Candidate → Bool → ℝ) :
    referenceDifference c bookedMass erased remaining =
      ((∑ x, bookedMass c x * WireSchedule.bitToll true x) + erased c true + remaining c true) -
      ((∑ x, bookedMass c x * WireSchedule.bitToll false x) + erased c false + remaining c false) := by
  unfold referenceDifference
  rw [← WireReferenceCost.booked_population_difference (bookedMass c)]
  ring

/-- Heavy-label amplitude on a supplied serial trace. The eligibility
proof uses the supplied admission predicate. Physical G, W and U are
needed to identify this trace with the row's realized writer. -/
noncomputable def heavyWeight {ticks : ℕ} (c : Candidate)
    (premises : Candidate → WireSchedule.Premises ticks)
    (trace : Candidate → WireSchedule.Schedule ticks)
    (_admitted : WireSchedule.admissible (premises c) (trace c) = true)
    (companionSetup : Candidate → Bool)
    (unpriced : Candidate → Channels → WireSchedule.Schedule ticks → ℝ) (label : Channels) : ℝ :=
  WireSchedule.amplitude (companionSetup c) (unpriced c) label (trace c)

/-- The common static-vector determinant response. T and U must
identify the offset and the detuning of the admitted trace. -/
theorem lightResponse (c : Candidate) (s : BaseProtocol) (hs : s ≠ .neutrino)
    (label : Channels) (detuning : Candidate → ℂ) (offset : Candidate → BaseProtocol → ℂ)
    (cycle : Candidate → Fin 3 → ℂ)
    (resonance : detuning c ^ 3 = -(cycle c 0 * cycle c 1 * cycle c 2)) :
    (ChargedInsertion.flip s label (detuning c) (offset c s) (cycle c)).det =
      if active label = false ∧ baseProtocol label = some s then detuning c ^ 2 * offset c s
      else 0 :=
  ChargedInsertion.det_flip_at_resonance s hs label _ _ _ resonance

def tier (c : Candidate) (identify : Candidate → TierLedger.WireTierAssignment)
    (protocol : BaseProtocol) (address : Fin 3) : ProtocolDynamics.Tier :=
  TierLedger.wireTier (identify c) protocol address

/-- [Premise] The existing species formulas on their declared tier rows,
in electron-mass units. The neutral sector has no mass ledger here. -/
noncomputable def declaredMass (protocol : BaseProtocol) (t : ProtocolDynamics.Tier) : Option ℝ :=
  match protocol, t.val with
  | .up, 0 => some QuarkMasses.up
  | .up, 2 => some QuarkMasses.charm
  | .up, 3 => some QuarkMasses.top
  | .down, 0 => some QuarkMasses.down
  | .down, 1 => some QuarkMasses.strange
  | .down, 2 => some QuarkMasses.bottom
  | .electron, 0 => some 1
  | .electron, 1 => some LeptonMasses.muon
  | .electron, 2 => some LeptonMasses.tau
  | _, _ => none

/-- Evaluate the declared mass ledger after the caller identifies the
wire tier for this candidate and address. -/
noncomputable def mass (c : Candidate) (identify : Candidate → TierLedger.WireTierAssignment)
    (protocol : BaseProtocol) (address : Fin 3) : Option ℝ :=
  declaredMass protocol (tier c identify protocol address)

/-- A numeric light-offset order is absent from the witness labels.
The operation and scaling law enter through the supplied offset. -/
def certifiedOffsetOrder (_c : Candidate) (_protocol : BaseProtocol) : Option ℕ := none

/-! ### Trace-derived isolated-excitation values

The occupied input and the retained 43-phase receiver trace are in
`IsolatedExcitation`.  These are the eight candidate rows, not supplied
rates.  The electron trace uses the lepton record column because every
electron packet label is colourless.  The heavy writer carries both
certified record columns; the trace does not select one.
-/

/-- Booked electron Toll per 43-tick period, from the candidate trace. -/
noncomputable def traceElectronToll (c : Candidate) : ℝ :=
  IsolatedExcitation.electronToll c.1 c.2.1 c.2.2

/-- Electron amplitude `exp(-T/2)` on the same trace. -/
noncomputable def traceElectronAmplitude (c : Candidate) : ℝ :=
  PMAction.TollAmplitude.wireAmplitude (traceElectronToll c)

theorem traceElectronToll_cases (c : Candidate) :
    traceElectronToll c = if c.2.1 then (if c.1 then 44 else 2) else 1 :=
  IsolatedExcitation.electronToll_cases c.1 c.2.1 c.2.2

/-- Heavy-writer (down-label) booked Toll on the same trace, for either
certified record reference. -/
noncomputable def traceHeavyToll (c : Candidate) (reference : Bool) (a : Fin 3) : ℝ :=
  IsolatedExcitation.heavyToll c.1 c.2.1 c.2.2 reference a

noncomputable def traceHeavyWeight (c : Candidate) (reference : Bool) (a : Fin 3) : ℝ :=
  IsolatedExcitation.heavyWeight c.1 c.2.1 c.2.2 reference a

theorem traceHeavyToll_colour (c : Candidate) (a : Fin 3) :
    IsolatedExcitation.bookedToll c.1 c.2.1 c.2.2 true ProtocolToll.electronStatic =
        IsolatedExcitation.receiverToll c.1 c.2.1 c.2.2 + 2 ∧
      traceHeavyToll c true a = IsolatedExcitation.receiverToll c.1 c.2.1 c.2.2 + 1 := by
  obtain ⟨he, hd, -⟩ := IsolatedExcitation.heavyToll_colour c.1 c.2.1 c.2.2 a
  exact ⟨he, hd⟩

theorem traceHeavyToll_lepton (c : Candidate) (a : Fin 3) :
    IsolatedExcitation.bookedToll c.1 c.2.1 c.2.2 false ProtocolToll.electronStatic =
        IsolatedExcitation.receiverToll c.1 c.2.1 c.2.2 + 1 ∧
      traceHeavyToll c false a = IsolatedExcitation.receiverToll c.1 c.2.1 c.2.2 + 2 := by
  obtain ⟨he, hd, -⟩ := IsolatedExcitation.heavyToll_lepton c.1 c.2.1 c.2.2 a
  exact ⟨he, hd⟩

/-- The trace does not select the heavy record reference.  Both columns are
carried; this is the smallest certified family. -/
def traceReferences : List Bool := [false, true]

theorem traceReferences_complete : ∀ b : Bool, b ∈ traceReferences := by decide +kernel

theorem down_geometric_mean_trace (c : Candidate) (a : Fin 3) :
    (IsolatedExcitation.bookedAmplitude c.1 c.2.1 c.2.2 true (ProtocolToll.downStatic a)) ^ 2 =
      IsolatedExcitation.bookedAmplitude c.1 c.2.1 c.2.2 true ProtocolToll.electronStatic *
        IsolatedExcitation.bookedAmplitude c.1 c.2.1 c.2.2 true (ProtocolToll.upStatic a) :=
  IsolatedExcitation.down_geometric_mean_colour c.1 c.2.1 c.2.2 a

theorem down_geometric_mean_trace_lepton_fails (c : Candidate) (a : Fin 3) :
    (IsolatedExcitation.bookedAmplitude c.1 c.2.1 c.2.2 false (ProtocolToll.downStatic a)) ^ 2 ≠
      IsolatedExcitation.bookedAmplitude c.1 c.2.1 c.2.2 false ProtocolToll.electronStatic *
        IsolatedExcitation.bookedAmplitude c.1 c.2.1 c.2.2 false (ProtocolToll.upStatic a) :=
  IsolatedExcitation.down_geometric_mean_lepton_fails c.1 c.2.1 c.2.2 a

end TransportCandidates

/-! ## Down protocol

The colour reference, common bit price and all remaining paid work
are separate from the declared species ledger.
-/

open ProtocolToll in
theorem down_colour_geometric_mean (price : ℝ) (a : Fin 3) :
    let s c := PMAction.TollAmplitude.wireAmplitude (price * WireSchedule.bitToll true c)
    s (downStatic a) ^ 2 = s electronStatic * s (upStatic a) := by
  simpa only [WireSchedule.bitToll, ElectricHeavyRecord.colour_reference_toll] using
    HeavyFlipRecords.down_geometric_mean price a

/-- [Premise] This is the declared down protocol ledger, with no
identification of an admitted wire address with a tier. -/
theorem down_declared_tiers :
    (TierLedger.tiersFor .down).map Fin.val = [0, 1, 2] := rfl

end PMElementaryParticles.Values
