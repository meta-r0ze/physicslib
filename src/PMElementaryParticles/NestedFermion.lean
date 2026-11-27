import PersistenceMechanics.CapacityPartitioning
import PersistenceMechanics.ReversibleEncoding
import PersistenceMechanics.ImpedanceMatching
import PMElementaryParticles.RetainedMap
import PMElementaryParticles.CapacityLedger
import PMElementaryParticles.RecordEncoding
import PMElementaryParticles.ImpedanceLedger

/-!
# Fermions as proposed nested persistence systems

This is a roles-and-structure step. A proposed tier n has levels 0 through n:
n nesting steps above the primitive ring. No workload, interface phase, level
period, tier assignment or higher-level cost is chosen. No flat-program
minimization is performed. OccupancyCost.cost_tower is the additive account;
PMAtoms.SystemTower is a downstream example, not an import or an EP derivation.

Sources: Paper III, PM-3-Nested/paper/2_nested_persistence.tex, Rules 1, 2, 3;
PersistenceMechanics.{CapacityPartitioning,ReversibleEncoding,ImpedanceMatching};
PMSubstrate.Pillars and PersistenceMechanics.Requirements.Pillar. Each system
has all six roles. A term named after a pillar does not prove that the
corresponding operation exists. This is the same distinction used by the
PMHadrons pillar-role audit and NucleonBase: a cone count and a residual
identity do not supply a whole physical configuration or its execution.

| Level | Capacity | Map | Protocol | Governor | Toll | Margin |
| --- | --- | --- | --- | --- | --- | --- |
| 0: primitive ring | Registration work fits the period: ProgramWitness.Capacity; CapacityLedger.ring_budget. | Keep the supplied channel/reference distinction: MapRecord and MapClass. Generation is missing from the quiet ring history. Rule 2 requires recoverable metadata for it. | RingReceiver.tick_bijective. | ProgramWitness.Governor leaves a non-firing site. | One reversal in the quiet-equal-ring account: ReversalEvents and RetainedMap.quiet_program_cost. No electron identification. | Each differing bit ring has at most 42 registrations: one_ring_margin_ceiling. |
| 1: maintain level 0 | Rule 1 must service the actual level-0 reference, metadata and coordination work; workload is open. | Retain a reference for distinctions erased by the level-0 description, including generation (Rule 2), and supply correction toward it (PMSubstrate.Pillars.map_maintains); both implementation and rate are open. | Supply a reversible cross-level encoding and a coordinated service schedule; Rule 2 and Rule 1, both conditional. | Restrict admitted child operations and resource contention; Requirements.Pillar.governor, with the execution open. | Count actual interface comparisons, writes or reversals; the encounter and its price are open, not inferred from metadata states. | Keep positive robustness to perturbations (PMSubstrate.Pillars.margin_iff), service reserve and a Rule-3 reflected-load budget. Their state spaces and units remain to be related. |
| 2: maintain level 1 | Rule 1 now services level-1 control and its child interfaces; tasks and demand are open. | Identify the level-1 coarse description, retain its lost distinctions (Rule 2) and correct toward that reference (map_maintains); the encoder/update are open. | Coordinate level-1 subsystems and preserve the inter-level records; actual update and timing are open. | Restrict the allowed level-1 compositions; no topology or nesting split is selected. | Account for level-1 interface work without counting a shared event twice; work and allocation are open. | Prove positive distance to nonviability (margin_iff), loop reserve and mismatch budget; no tolerance is selected. |
| 3: maintain level 2 | Rule 1 must service level-2 maintenance and coordination; no volume workload is assumed. | Retain level-2 reference/metadata (Rule 2) and supply correction (map_maintains); generation-to-depth is not derived. | Supply reversible level-2 composition and its schedule; neither follows from a ledger identity. | Restrict the admitted level-2 architecture and its execution. | Price its executed boundary work, not a guessed Delta power. | Prove robustness (margin_iff), reserve and interface budgets for that implementation. |

Level 0 here names the primitive unit account. The supplied quark point
entries have not been derived from it. The proved one-reversal account in a
43-tick window is not a theorem
of full joint-state return in 43 ticks. Above level 0 all six roles are
obligations of the proposed architecture, not new physics theorems.
If each higher-level controller is realized by a copy of the ring, its
Margin bound needs an identified differing ring and the same service interval.
The 42 bound does not automatically apply to an arbitrary metadata store.

## Existing three-rule adapters

| Module | Actual objects and hypotheses | Per-level structure? | Reuse |
| --- | --- | --- | --- |
| CapacityLedger | Tasks are protocols sharing one ring; r_i are registrations per period; h_i are supplied comparison overheads; capacity is 43, or 43 minus a supplied reserve. | No level index, workload generator or child schedule. | Reusable conditional budget adapter; use a proved Margin reserve before assigning 42. |
| RecordEncoding | States are Channels, coarse data are labelRecord, metadata are channelCode. Fibres have six or two channels and need at least six metadata states. | No generation coordinate or per-level record. | Reusable channel-encoding adapter. Its colour-reference construction is not a nested-generation model. |
| ImpedanceLedger | Tasks are supplied converter encounters/phases xs; reflected/transmitted loads are sums of expected flag weights; a reserve bounds the reflected part. Source/load 1 minus/plus abs(sin(x/2)) realize that law. | No level indices, derived phases, workloads or per-level reserves. | Reusable conditional interface algebra. Treating it as an already derived level model is legacy; expected load is not the integer 42-slot budget. |

The new Rule-2 instance below uses a fixed channel and generations as states.
Its coarse description is the complete quiet-program ring history for one
period. The histories coincide across generations. Adding the generation as
metadata is injective; any sufficient metadata needs at least three states.
This prices neither storage nor service. It is not a three-reversal workload.

Paper V (PM-5-InfoTransfer/paper/2_ie_dynamics.tex) proposes linear/areal/volume
quark generations. That wording differs from the retained EP ledger powers
(up 0,2,3; down 0,1,2). No equality or generation-to-tier map is inferred.
Paper V 4_pmns_matrix.tex's lepton-axis 1+2 statement concerns a reference
symmetry and states three premises. ClockSymmetry's raw key stabilizer also
has a singleton and a pair, but the full oriented channel placement can reject
the swap. None of these statements proves a nesting depth or a workload.

## Exact promotion question

For species s and level n, specify the tasks, required work w(s,n,i) per fixed
period, nonnegative interface overhead, and a complete feasible service
allocation. Identify each worker with a differing ring so Margin supplies 42
service units in that interval. If total required work plus overhead exceeds
42, Rule 1 forces at least two such loops. If workload or deadline can change,
that conclusion need not apply. Dividing the same insufficient budget does
not help. To call the additional loops level n+1, also establish the nested
architecture that coordinates them; Rule 1 alone only forces more capacity.
No species ledger supplies w(s,n,i), an event-to-service map or a deadline.
No species-specific overload is proved here. Rule 2's metadata state counts,
held occupancy counts and Rule 1's work per period are distinct quantities.
-/

noncomputable section
namespace PMElementaryParticles.NestedFermion
open PMElementaryParticles.EPSpine PMElementaryParticles.RetainedMap
open PMElementaryParticles.ProgramWitness
open PMConstants.PacketGaugeActions
open PersistenceMechanics

/-- The base coarse description is a one-period native ring history, including both endpoints. -/
def baseHistory (c : Channels) (g : Generation) : Fin 44 → RingObservation :=
  fun t => observe (quietProgram g c) t.val

theorem base_history_merges_generations (c : Channels) (g h : Generation) :
    baseHistory c g = baseHistory c h := by
  funext t
  exact quiet_observations_equal g h c t.val

/-- Rule 2, for the generation distinctions omitted by this particular coarse description. -/
theorem generation_metadata_reversible (c : Channels) :
    Function.Injective (ReversibleEncoding.encode (baseHistory c) (id : Generation → Generation)) := by
  intro g h he
  exact congrArg Prod.snd he

theorem generation_metadata_cardinality (c : Channels) {M : Type*} [Fintype M]
    (m : Generation → M)
    (h : Function.Injective (ReversibleEncoding.encode (baseHistory c) m)) :
    3 ≤ Fintype.card M := by
  have hm : Function.Injective m := by
    intro g k he
    exact (ReversibleEncoding.encode_injective_iff _ _).mp h g k
      (base_history_merges_generations c g k) he
  simpa only [EPSpine.generation_card] using Fintype.card_le_of_injective m hm

/-- This service ceiling is for a differing bit ring, not for arbitrary higher-level storage. -/
theorem one_ring_margin_ceiling (p : Program) (h : p.Pillars) (b : Fin 2)
    (hd : differs p.toRing b) : registrations p.toRing b ≤ 42 := by
  have hm := h.2.1 b hd
  omega

/-- Rule 1: with fixed complete work, overload of one such loop forces additional capacity.
The theorem does not identify the workers with a new tier. -/
theorem overload_needs_multiple_loops {I J : Type*} [Fintype I] [Fintype J]
    (w : I → ℝ) (overhead : J → ℝ) (service : I → J → ℝ)
    (h : CapacityPartitioning.Feasible w (fun _ => 42) overhead service)
    (hover : 42 < (∑ i, w i)+(∑ j, overhead j)) : 2 ≤ Fintype.card J := by
  have hb := CapacityPartitioning.global_budget h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hb
  by_contra hc
  have hn : Fintype.card J ≤ 1 := by omega
  have hn' : (Fintype.card J : ℝ) ≤ 1 := by exact_mod_cast hn
  linarith

end PMElementaryParticles.NestedFermion
