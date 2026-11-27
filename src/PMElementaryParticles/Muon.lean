import PMElementaryParticles.NestedFermion
import PMSubstrate.DerivedParameters
import PMElementaryParticles.LedgerLevels

/-!
# Muon: level-1 roles before a cost assignment

Named premise B: a level-1 charged-lepton system persists.
This is the SCOPE named premise, not a new Lean axiom. The native level-1
execution, admission predicate and promotion workload remain open. In
particular, this sentence is not replaced by a freely chosen permutation or
by a proof that a list of accounts exists. The conditional accounting below
must not be read as constructing that execution.

## Roles, independent of the declared species ledger

The method is the pillar-role separation used by PMHadrons and the downstream
PMAtoms.ShellSystem. Neither library is imported. A role needs an operation,
its state space and a resource account before it supplies a numerical charge.

| Pillar | Level-1 charged-lepton role | Source | Open implementation |
| --- | --- | --- | --- |
| Capacity | Hold the child ring programs and service the parent's reference/coordination tasks in its period. | Paper III Rule 1; CapacityPartitioning.global_budget; OccupancyCost.cost_tower. | The set of held children, their ownership and parent period. No sweep or multiplicity follows from feasibility. |
| Map | Keep the charged channel and retained generation readable; correct toward that reference. | Paper III Rule 2; NestedFermion.generation_metadata_cardinality; PMSubstrate.Pillars.map_maintains. | Parent coarse description, encoder, correction and update schedule. Alphabet size does not fix their rate or give an anchor credit. |
| Protocol | Coordinate child transitions and preserve the cross-level distinctions. | ReversibleEncoding.encode_injective_iff_decoder; RingReceiver.tick_bijective for a child. | Reversible parent operation and its clock. A child tick does not specify the parent period. |
| Governor | Restrict admitted child combinations and resource contention. | Requirements.Pillar.governor; PMSubstrate.PersistencePremises.restriction_lowers. | The allowed subset and proof of what it removes. No phase or numerical saving is selected. |
| Toll | Account for executed registrations/reversals at the child and parent interfaces. | ReversalEvents.registrations_eq_reversals, footprint_cost; RetainedMap.quiet_program_cost. | Actual interface operations and multiplicity. Coherent phase is not yet an event charge. |
| Margin | Preserve robustness, spare loop service and a budget for reflected load. | NestedFermion.one_ring_margin_ceiling; PMSubstrate.Pillars.margin_iff; ImpedanceMatching.admissible_iff_transmission. | Viable parent states, reserve allocation, encounter phases and recovery law. Rule 3 does not select a feedback loop. |

The certified child is the quiet-equal-ring program, with one reversal and
cost one in its base-period account. Its full joint-state return is not proved.
A parent holding a child across several ticks does not thereby hold a different
child at every tick. A parent period need not equal one child clock period.

## What the rules determine

For an independently identified collection of disjoint unit child accounts
in a common accounting period, their cost is the cardinality of that collection.
Relating the parent period to this base-period account is still required. All other contributions
remain an explicit OPEN residual. Neither its value nor the child count is
set here; zero is not the derived value of an unresolved contribution.
A conditional price identity is not a numerical muon prediction.
-/

noncomputable section
namespace PMElementaryParticles.Muon
open PMSubstrate.E8Values PMSubstrate.OccupancyCost
open PMConstants.PacketGaugeActions
open PMElementaryParticles.EPSpine PMElementaryParticles.RetainedMap

/-- Only the identified child accounts are counted. No parent architecture is selected. -/
def heldChildren (n : ℕ) (g : Generation) (c : Channels) : Footprint :=
  (ReversalEvents.footprint (quietProgram g c)).scale n

theorem held_children_events (n : ℕ) (g : Generation) (c : Channels) :
    (heldChildren n g c).events = n := by
  simp [heldChildren, quiet_footprint_one, Footprint.scale]

/-- A count of disjoint unit accounts times the proved unit price. -/
theorem held_children_cost (n : ℕ) (g : Generation) (c : Channels) :
    cost (heldChildren n g c) = (n : ℝ) := by
  simp [heldChildren, quiet_program_cost]

/-- The child pillars alone admit any finite copy count. This says nothing
about admission or persistence of a level-1 parent of those children. -/
theorem child_pillars_for_any_count (n : ℕ) (g : Generation) (c : Channels)
    (hc : ProgramClasses.classOf c ≠ 4) :
    ∀ _ : Fin n, (quietProgram g c).Pillars :=
  fun _ => quiet_program_pillars g c hc

/-- An OPEN account: n must come from the held-unit set, and unresolved must
come from priced parent operations. Neither is supplied by premise B. A zero
extra pillar field omits that operation; it does not prove its charge is zero. -/
def conditionalFootprint (n : ℕ) (unresolved : ℝ) (g : Generation) (c : Channels) : Footprint :=
  tower [heldChildren n g c, { residual := unresolved }]

theorem conditional_cost (n : ℕ) (unresolved : ℝ) (g : Generation) (c : Channels) :
    cost (conditionalFootprint n unresolved g c) = (n : ℝ)+unresolved := by
  rw [conditionalFootprint, cost_tower]
  have hr : cost { residual := unresolved } = unresolved := by simp [cost]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    held_children_cost, hr, add_zero]

/-! ## Counts from the substrate, without identifying them with held children

D is half the forced E8 rank (Derived.rank_eight, parameters_forced); the
signature supplies one clock direction (Derived.one_time).
Sigma is the dimension of the configuration chart: D-1 spatial coordinate
directions plus two surface-coordinate directions (Derived.configDim and its
signature/boundary postulates). The latter two are NOT two points of a sphere
or two ring copies. Chi is the Euler characteristic of that boundary (Derived.boundary_sphere),
not a theorem counting two child anchor accounts.
Pi in the pillar price is a real geometric measure, not a finite cardinality.
The full product below counts chart-direction/tick labels. It is not proved
bijective to the units actually held by the parent. In particular, executing
Delta ticks is not a proof of holding Delta separate base-period accounts.
-/

abbrev ConfigurationDirections := Fin (D-1) ⊕ Fin 2
abbrev FullSweepLabels := ConfigurationDirections × Fin Delta

theorem configuration_direction_count :
    Fintype.card ConfigurationDirections = sigma ∧ sigma = PMSubstrate.Derived.configDim D 1 := by
  norm_num [ConfigurationDirections, PMSubstrate.Derived.configDim]

theorem full_sweep_label_count : Fintype.card FullSweepLabels = sigma*Delta := by
  simp only [FullSweepLabels, Fintype.card_prod, configuration_direction_count.1, Fintype.card_fin]

theorem boundary_euler :
    PMSubstrate.ImpedanceTerms.ClosedSurface.euler (.orientable 0) = (chi : ℤ) := by
  norm_num [PMSubstrate.ImpedanceTerms.ClosedSurface.euler]

/-- This is a price identity. No released anchor, or sign of a parent charge, is derived. -/
theorem negative_map_price : cost { map := -1 } = -(chi : ℝ) := by
  norm_num [cost, PMSubstrate.mapTerm, PMSubstrate.baseline]

/-- Even the magnitude of the proposed phase charge is not a whole event count. -/
theorem phase_measure_not_event_count : ¬ ∃ n : ℕ, (n : ℝ) = 2*Real.pi := by
  rintro ⟨n,hn⟩
  have hlo : (6 : ℝ) < 2*Real.pi := by linarith [Real.pi_gt_three]
  have hhi : 2*Real.pi < (7 : ℝ) := by linarith [Real.pi_lt_d2]
  by_cases h : n ≤ 6
  · have hc : (n : ℝ) ≤ 6 := by exact_mod_cast h
    linarith
  · have hc : (7 : ℝ) ≤ n := by exact_mod_cast (show 7 ≤ n by omega)
    linarith

/-! ## Comparison with the declared ledger, after the role and count audit

| Ledger term | Obtained from the roles | Mathematical certificate | Match? |
| --- | --- | --- | --- |
| Sweep sigma*Delta | n held unit accounts, count not determined. | held_children_cost; full_sweep_label_count | Conditional arithmetic match only if actual held units are the full direction/tick product. No such identification is proved. |
| Anchor -chi | No released-anchor operation or negative count is derived. | boundary_euler; negative_map_price | Price identity only. No release, sharing or prior-accounting theorem supplies this negative charge. |
| Spin phase lag -2*pi | No phase-to-held-event charge is derived. | phase_measure_not_event_count | Open residual; phase and event count have different meanings. |
| Feedback (chi+sigma)*alpha/(1-alpha) | No source load, return coefficient or recurrence is derived. | declared_feedback_unique, for the SUPPLIED recurrence | Algebra matches the declared loop, but neither Rule 3 nor premise B chooses that loop. |

The cost derivation is n plus an open residual, not a new scalar prediction.
The exact difference below compares that uninstantiated account with the
ledger; it does not set the residual to make them equal. The two known child
facts (one reversal, unit price) do not determine any of the four muon terms.
No measured input enters this module. No closeness ranking exists for an
uninstantiated n and residual; comparing the child unit to a muon measurement
would compare different systems. The reporter's existing ledger comparison
remains read-only.

The reusable part for a tau or a strange-quark system is the method: identify
children, their shared accounting period, retained metadata, admitted operations
and resource ownership, then apply the same three rules and tower addition.
No proved recursion maps this level-1 lepton's open operations to level 2 or
to the coloured sector. Thus this audit derives neither their multiplicities
nor their residuals; the declared inheritance identities do not supply that map.
-/

open PMSubstrate.SpeciesFootprints

/-- Equality of a hypothetical full-sweep unit account with the declared leading term.
The hypothesis is an OPEN identification, not an additional adopted premise. -/
theorem sweep_agrees_if_identified (n : ℕ) (g : Generation) (c : Channels)
    (h : n = Fintype.card FullSweepLabels) :
    cost (heldChildren n g c) = Lepton.muonSweep := by
  rw [held_children_cost,h,full_sweep_label_count]
  unfold Lepton.muonSweep
  push_cast
  ring

/-- The supplied feedback recurrence has a unique solution. This does not
identify its source load or coefficient with a physical parent operation. -/
theorem declared_feedback_unique (x : ℝ)
    (h : x = ((chi+sigma : ℕ) : ℝ)*PMSubstrate.causalCoupling+
      PMSubstrate.causalCoupling*x) : x = Lepton.muonFeedback := by
  have ha : 1-PMSubstrate.causalCoupling ≠ 0 := ne_of_gt (sub_pos.mpr PMSubstrate.causalCoupling_bounds.2)
  have hf := Lepton.muonFeedback_fixpoint (ne_of_lt PMSubstrate.causalCoupling_bounds.2)
  have hz : (1-PMSubstrate.causalCoupling)*(x-Lepton.muonFeedback) = 0 := by
    nlinarith [h,hf]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left ha)

/-- All missing terms stay in the difference; no ledger correction is copied into the account. -/
theorem declared_minus_conditional (n : ℕ) (unresolved : ℝ) (g : Generation) (c : Channels) :
    Lepton.muon-cost (conditionalFootprint n unresolved g c) =
      (Lepton.muonSweep-(n : ℝ))-Lepton.muonAnchor-Lepton.muonSpinLag+
        Lepton.muonFeedback-unresolved := by
  rw [conditional_cost,Lepton.muon_ledger]
  unfold Lepton.muonSweep Lepton.muonAnchor Lepton.muonSpinLag Lepton.muonFeedback
  ring

end PMElementaryParticles.Muon
