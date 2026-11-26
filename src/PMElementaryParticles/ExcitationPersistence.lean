import PMElementaryParticles.IsolatedReceiverTrace
import PMElementaryParticles.ProgramWitness
import PMKAutomaton.BoundaryErasure

/-!
# Isolated excitation persistence: stop at the missing occupied-background rule

This module records the item-1 blocker. It does not define Persists by supplying
an arbitrary joint update or an assumed renewal budget. That would insert the
missing physical rule as a hypothesis. No minimum, coset contact count, or mass
reading is selected here.

An eventual Persists predicate needs one identified admitted execution of
vacuum tensor one packet program. After Delta ticks its class, generation and
label must return, and its vacuum must be back in the certified stationary
family. ProgramWitness.Pillars supplies only the ring conditions. Its Capacity
bounds registrations by 2*43; it does not balance a reference resource.

Resource Capacity also needs the actual record writes and booked boundary
resets of THAT execution. Each used record must have an identified restoring
input and readiness deadline within the period. The account must show that
supply covers consumption without an intermediate deficit and that the
vacuum/reference inventory is renewed at the end. An equality of net bit
occupancy, or zero boundary erasures, does not prove those facts. Restoring an
unknown bit and preparing a clean reference slot are distinct operations;
BoundaryErasure.erasure_not_injective forbids recovering the former from a
reset output alone.

## What exists and what it leaves open

| Existing result | Certified | Missing connection |
| --- | --- | --- |
| IsolatedExcitation.vacuum_stationary | Each exhibited rest mode is stationary for the vacuum Hamiltonian. | The occupied interaction and return after its writes. |
| IsolatedExcitation.occupiedInput | One carrier basis label and one payload label occupy independent banks. | Its relation to a coherent vacuum mode and the spatial program execution. |
| IsolatedReceiverTrace.localizedEmbedN | A localized Boolean port field with supplied controller fields. | The vacuum label is ignored; requests and readiness are not derived from it. |
| Components.jointTick | Reversible packet-bank lifts over the retained core. | The bank permutation is supplied, not the occupied-background rule. |
| RecordSupply.clean_supply | The backward stream restores the reference on clean, open incoming records. | Their occupied source, renewal, and closure of the background in the same period. |
| OddReferenceSource.odd_seed_train_restores | A loaded train of rest seeds supplies a reference. | The hypothesis loads a seed before every visit; it is not derived from one isolated excitation. |
| BoundaryErasure.cycleErased | Counts actual resets once exports and dispositions are supplied. | Which execution writes/exports a bit, who restores the slot, and where its input comes from. |
| ProgramWitness.witness_total | One differing-ring registration attains the ring subtotal lower bound. | Registrations are not identified with OccupancyCost.Footprint.events. |

The candidate restoring input already named in the machine is the upstream
backward record stream, s(j+1).2. It is CONDITIONAL supply. Open fresh supply
moves disturbances into outgoing records; it does not certify renewal of a
closed vacuum tensor packet system. On a finite ring a disturbance returns.
Stationary seeds are also nonunique, and the existing receiver embedding
cannot distinguish them. The lemmas below expose these API limits; they do
not prove that no physical closed renewal rule can exist.

Blocker for PMKAutomaton: construct the reachable occupied background and an
admitted local successor tying its vacuum/reference, packet, requests and
record operations together. Identify each write/export/reset and its restoring
mode or port; prove within-period resource balance and return of the background
to the certified stationary family. Only then can EP state the requested
Persists on that execution and minimize its held-event footprint.

Items 2--4 stop here. In particular no equal-generation mass prediction, no
k-to-zero-to-k requirement, no one-event minimum, and no uniqueness claim follows.
SelectionSymmetry.unique_minimizer_fixed presupposes a cost and a minimizer;
it cannot supply this missing execution. The triality-orientation question is
parked until a persistence-derived minimum actually exhibits a tie.
-/

noncomputable section
namespace PMElementaryParticles.ExcitationPersistence
open PMElementaryParticles.IsolatedExcitation
open PMKAutomaton
open Matrix

/-- The receiver embedding supplies no dependence on the vacuum label. -/
theorem localized_embedding_ignores_vacuum (n : ℕ) (c : Fin 3)
    (v w : VacuumLabel c) (label : PacketLabel) (x0 : Fin n)
    (fields : ReceiverFieldsN n) :
    localizedEmbedN n c v label x0 fields = localizedEmbedN n c w label x0 fields := rfl

/-- The exhibited stationary vacuum family does not select one record mode. -/
theorem distinct_stationary_modes (c : Fin 3) (wall : Bool) (p : ℝ)
    (hp : 0 < p) (hp' : p < 1/2) :
    ∃ v w : VacuumLabel c → ℂ,
      PMAction.NativeSector.nativeHamiltonian c p 0 0 *ᵥ v = 0 ∧
      PMAction.NativeSector.nativeHamiltonian c p 0 0 *ᵥ w = 0 ∧ v ≠ w :=
  ⟨vacuumMode c wall false, vacuumMode c wall true,
    vacuum_stationary c wall false p hp hp', vacuum_stationary c wall true p hp hp',
    vacuum_nonunique c wall⟩

/-- The same reversible core permits distinct packet-bank operations. This is
an underdetermination result, not an admission of either operation for EP. -/
theorem core_projection_does_not_select_packet_lift {I : Type*} (core : I → I)
    (x : I) (label : PacketLabel) :
    ∃ bank : Components.PacketBank 1,
      (Components.jointTick core (fun _ => Components.fifoEquiv 1) (x, bank)).1 =
        (Components.jointTick core (fun _ => Equiv.refl _) (x, bank)).1 ∧
      (Components.jointTick core (fun _ => Components.fifoEquiv 1) (x, bank)).2 (0,label) ≠
        (Components.jointTick core (fun _ => Equiv.refl _) (x, bank)).2 (0,label) := by
  obtain ⟨bank, hb⟩ := Components.joint_two_fifo_placements_differ core x label
  exact ⟨bank, rfl, hb⟩

/-- Disposal changes the supplied account while leaving the protected update
unchanged. There is no assertion that both bookings describe one ring execution. -/
theorem protected_step_does_not_select_boundary_account {I : Type*}
    (update : Equiv.Perm I) (i : I) (bit : Bool) :
    (BoundaryErasure.step update i (some bit) .keep).1 =
      (BoundaryErasure.step update i (some bit) .erase).1 ∧
    BoundaryErasure.erasedBits .keep (some bit) = 0 ∧
    BoundaryErasure.erasedBits .erase (some bit) = 1 := by
  exact ⟨rfl, BoundaryErasure.keep_no_erasure _, BoundaryErasure.erasing_pays_one bit⟩

/-- Retaining a finite stream returns its disturbance; this alone does not
renew the stream into an unlimited source of clean reference records. -/
theorem finite_supply_returns_disturbance {X A : Type*} [DecidableEq X]
    (o : X) (e : Equiv.Perm X) (s : X → A × A) (reference : A)
    (N : ℕ) (hN : 1 ≤ N) (hclose : (e ^ N) o = o)
    (hmin : ∀ m, 1 ≤ m → m < N → (e ^ m) o ≠ o)
    (hdirty : (s (e⁻¹ o)).1 ≠ reference) :
    (PMAction.RecordSupply.run o e (N+1) s o).1 ≠ reference := by
  rw [PMAction.RecordSupply.ring_returns o e s N hN hclose hmin]
  exact hdirty

end PMElementaryParticles.ExcitationPersistence
