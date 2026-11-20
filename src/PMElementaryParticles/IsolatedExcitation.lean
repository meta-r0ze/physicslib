import PMTransport.Interface
import PMTransport.Values
import PMElementaryParticles.ProtocolInventory

/-!
# The isolated-excitation sector and its clocked trace

A mass is a property of one isolated excitation on the vacuum.  The import
surface is still `PMTransport.Interface` and `PMTransport.Values`; the
transitive names of the machine are used only to state the existing
acceptance, supply and stationary-background results.

The occupied input is the product of the E8 reference background and one
16-slot packet label.  It is **not** a new choice of `O`: the occupancy is
vacuum plus one packet, which is what the quantity "mass" refers to.  The
background itself is a certified family (`vacuum_stationary` and
`vacuum_nonunique`), not a single preferred vector.

The clocked trace and its booked values live in `IsolatedTrace`.
-/

noncomputable section
namespace PMElementaryParticles.IsolatedExcitation

open PMConstants.PacketGaugeActions
open PMElementaryParticles.ProtocolInventory
open PMAction Matrix

/-! ## Vacuum and occupied input -/

abbrev PacketLabel := Channels

abbrev VacuumLabel (c : Fin 3) := PMAction.RegisterVacuum.Labels c

abbrev OccupiedConfig (c : Fin 3) := PMAction.RegisterVacuum.Config (b := Channels) c

/-- A normalized stationary rest mode of the native vacuum sector.  This is
the carrier factor of the E8 vacuum.  There are twelve such modes (three
carriers, two walls, two rest axes); `vacuum_nonunique` records that no
single one is selected by stationarity. -/
def vacuumMode (c : Fin 3) (wall record : Bool) : VacuumLabel c → ℂ :=
  PMTransport.OddReferenceSource.restMode c wall record

theorem vacuum_stationary (c : Fin 3) (wall record : Bool) (p : ℝ)
    (hp : 0 < p) (hp' : p < 1 / 2) :
    (PMAction.NativeSector.nativeHamiltonian c p 0 0) *ᵥ vacuumMode c wall record = 0 :=
  PMTransport.OddReferenceSource.rest_stationary c wall record p hp hp'

theorem vacuum_population (c : Fin 3) (wall record : Bool) :
    CommonResponse.nsq (vacuumMode c wall record) = 1 :=
  PMTransport.OddReferenceSource.rest_population c wall record

theorem vacuum_nonunique (c : Fin 3) (wall : Bool) :
    vacuumMode c wall false ≠ vacuumMode c wall true :=
  PMTransport.OddReferenceSource.rest_modes_distinct c wall

/-- The stationary two-stream background supplying the reference at every
site.  Its value is the supplied reference `r`; the family is not a
selection of a physical vacuum value. -/
theorem background_stationary {X : Type*} [DecidableEq X] (o : X)
    (e : Equiv.Perm X) (r : Fin 2 → ℂ) :
    PMAction.NativeReferenceBackground.advance o e (fun _ => (r, r)) = fun _ => (r, r) := by
  funext x
  by_cases h : x = o <;> simp [PMAction.NativeReferenceBackground.advance, h]

/-- The occupied input for a mass: one E8 reference label in the carrier
bank and one 16-slot packet label in the payload bank.  `IndependentRegisters`
proves this is exactly one occupied register in each bank. -/
def occupiedInput (c : Fin 3) (vacuum : VacuumLabel c) (packet : PacketLabel) :
    OccupiedConfig c :=
  PMAction.IndependentRegisters.encode (vacuum, packet)

theorem occupiedInput_valid (c : Fin 3) (vacuum : VacuumLabel c) (packet : PacketLabel) :
    PMAction.IndependentRegisters.Valid (occupiedInput c vacuum packet) :=
  (PMAction.IndependentRegisters.valid_iff _).mpr ⟨(vacuum, packet), rfl⟩

theorem occupiedInput_occupied (c : Fin 3) (vacuum : VacuumLabel c) (packet : PacketLabel) :
    PMAction.IndependentRegisters.occupied (occupiedInput c vacuum packet) = 2 :=
  PMAction.IndependentRegisters.occupied_encode _

theorem occupiedInput_carrier (c : Fin 3) (vacuum : VacuumLabel c) (packet : PacketLabel) :
    occupiedInput c vacuum packet (.inl vacuum) = true := by
  simp [occupiedInput, PMAction.IndependentRegisters.encode]

theorem occupiedInput_packet (c : Fin 3) (vacuum : VacuumLabel c) (packet : PacketLabel) :
    occupiedInput c vacuum packet (.inr packet) = true := by
  simp [occupiedInput, PMAction.IndependentRegisters.encode]

theorem occupiedInput_packet_unique (c : Fin 3) (vacuum : VacuumLabel c) {packet other : PacketLabel}
    (h : other ≠ packet) : occupiedInput c vacuum packet (.inr other) = false := by
  simp [occupiedInput, PMAction.IndependentRegisters.encode, h]

theorem occupiedInput_carrier_unique (c : Fin 3) {vacuum other : VacuumLabel c} (packet : PacketLabel)
    (h : other ≠ vacuum) : occupiedInput c vacuum packet (.inl other) = false := by
  simp [occupiedInput, PMAction.IndependentRegisters.encode, h]

/-- Admission uses the existing valid-configuration criterion: one occupied
register in each independent bank. -/
def Admitted {c : Fin 3} (q : OccupiedConfig c) : Prop :=
  PMAction.IndependentRegisters.Valid q

theorem occupiedInput_admitted (c : Fin 3) (vacuum : VacuumLabel c) (packet : PacketLabel) :
    Admitted (occupiedInput c vacuum packet) :=
  occupiedInput_valid c vacuum packet

/-- Reference supply: if the incoming record cells carry the packet label and
the retained orbit is open, every receiver visit reads that label.  This is
`RecordSupply.clean_supply`, exported through the Transport interface. -/
theorem occupiedInput_supply {X : Type*} [DecidableEq X] (o : X)
    (e : Equiv.Perm X) (s : X → Channels × Channels) (packet : PacketLabel) (T : ℕ)
    (hclean : ∀ m, 1 ≤ m → m ≤ T → (s ((e ^ m) o)).2 = packet)
    (hopen : ∀ m, 1 ≤ m → m < T → (e ^ m) o ≠ o)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ T) :
    (PMAction.RecordSupply.run o e t s o).1 = packet :=
  PMAction.RecordSupply.clean_supply o e s packet T hclean hopen t ht1 htT

/-- Any acceptance rule on the retained route factors through the supplied
upstream records.  This is the existing `acceptance_iff_supply`, used here
to certify that the isolated packet is the accepted input of the trace. -/
theorem occupiedInput_acceptance {V : Type*} (s : PMTransport.OpenHandoff.State V)
    (accepts : V → Prop) (N : ℕ) :
    (∀ j : Fin N, accepts (PMTransport.OpenHandoff.run s (j.val + 1) 0).1) ↔
      (∀ j : Fin N, accepts (s (j.val + 1 : ℤ)).2) :=
  PMTransport.OpenHandoff.acceptance_iff_supply s accepts N

end PMElementaryParticles.IsolatedExcitation
