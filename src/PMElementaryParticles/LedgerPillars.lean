import PMElementaryParticles.LevelZeroFermions

/-!
# Ledger pillar classification: arithmetic, roles, and missing identifications

This is an audit, not a cost derivation. The EP OVERVIEW gives the table with
read-only e8p pulls. No hadron module is imported into EP.

We distinguish three questions:
1. Which whole baseline-price coefficients occur in an existing Footprint?
2. Which additional ledger expressions have a direct price identity or an
   explicit role label in their OWN library?
3. Which physical operations and coefficients have actually been derived?
An answer to the first two does not answer the third. Events at price one and
an unpriced residual do not automatically constitute a baseline pillar charge.

For classification, an already written pi*L term has the Capacity-price form
(L/Delta)*capacityTerm. A written chi*X term has the Map-price form X*mapTerm.
These identities are arithmetic, not new whole counts when their coefficients
are fractional. We do not divide arbitrary residuals by a selected price.
Nor do we relabel D as 2*chi merely because those integers happen to agree.
A capacity-leak label is a documented role, not a count theorem.

## Sources for the table

| Source | Classification it actually supports |
| --- | --- |
| SpeciesFootprints; Muon | Muon has the explicit negative Map charge. Its spin pi term has a fractional Capacity-price identity; its sweep is a declared event account, and the feedback loop has no derived pillar assignment. Tau's explicit chi boundary terms have Map-price identities; the negative line and D anchor are unassigned operations. |
| Quark named terms | D-based anchors and eta normalization have no certified pillar operation. Strange chi*sigma and bottom Delta^2*chi/sigma have Map-price factors, with the overhead still supplied. Top capLeakTerm is named a capacity leak. Charm's colour dilution is supplied. |
| NucleonBase.causalCone_eq_sq | Delta^2 is explicitly Margin's causal cone. It is an event count, not a whole marginTerm charge. This does not assign the other terms. |
| CompositeMasses; MesonMasses | zTol and zMar are exactly baseline Toll and Margin prices. Sigma*zTol and -zMar/chi retain their own coefficients; the latter is fractional. The pi*D term has a fractional Capacity-price identity. No source assigns inverse D, charge feedback, or sigma/2 uniquely to the remaining pillars. |
| MesonMasses.cellBudget_pillars; *_cells | Each full cell expands into six baseline prices. Pion -chi*sigma is an extra whole Map charge. Other residual terms stay labelled or unassigned individually; a six-price cell does not derive its residual. |

The older PMHadrons overview's "all six" nucleon claim was based on its list
of terms; it did not supply a one-to-one pillar map. Direct Toll/Margin prices
and a causal-cone role do not certify six distinct slots. The neutral and
charged mesons really have an explicit six-price expansion by definition of
their cell budget. Counts of written summands are not counts of pillars.

## The six-slot hypothesis

A role can constrain an already-priced event. Six roles do not license charging
that event six times. Resource ownership and any independent extra costs need proofs.
A six-entry grouping can always contain zeros or aggregate several operations.
It is not a theorem that all six roles must add distinct nonzero scalar terms.
The CURRENT ring pillars all hold for the labelled one-reversal witnesses,
whose baseline extra-price support is empty. This is a finding about that
contract/account; it is not a counterexample to full physical persistence,
which that contract does not prove. Even support is representation-dependent:
chi events and one Map charge have the same scalar value but different supports.

The four-term muon ledger therefore does not identify exactly two missing
physical slots. Its named Toll and Margin baseline prices are absent, but
there is also no proved Protocol/Governor assignment of its phase and feedback.
Calling those the two missing corrections would assume the proposed map.
The parent Toll/Margin roles are open; a child reversal has already been priced
inside any actual child bank. The level and ownership of a charge matter.

## Withdrawn baseline-Toll lead (2026-11-23)

The EP TODO no longer contains that working history. It is retained in the
read-only e8p LeptonMassPulls docstring: the apparent baseline-Toll agreement
with the muon residual (+0.18 sigma) was withdrawn. One common sign rule gave
wrong signs for Capacity, Map and the regulator; reversing all signs did not
repair Toll/Margin, and Protocol+Governor differed from the proposed muon
feedback by +226 sigma. This is a do-not-retry result for that flat reading.
Do not use a measured residual to fill a slot. A level-specific operation,
coefficient and resource account must be supplied first.
-/

noncomputable section
namespace PMElementaryParticles.LedgerPillars
open PersistenceMechanics.Requirements
open PMSubstrate.OccupancyCost PMSubstrate.E8Values
open PMSubstrate.SpeciesFootprints

/-- Metadata about the existing six fields, not a new cost reading. -/
def extraCount (f : Footprint) : Pillar → ℤ
  | .capacity => f.capacity
  | .map => f.map
  | .protocol => f.protocol
  | .governor => f.governor
  | .toll => f.toll
  | .margin => f.margin

/-- Expand full cells into their six prices; do not assign events or residuals by fiat. -/
def explicitSlots (f : Footprint) : Finset Pillar :=
  Finset.univ.filter fun p => (f.cells : ℤ)+extraCount f p ≠ 0

theorem one_cell_has_six_prices : explicitSlots oneCell = Finset.univ := by decide +kernel

theorem muon_tau_explicit_slots :
    explicitSlots Lepton.muonFootprint = {.map} ∧
      explicitSlots Lepton.tauFootprint = {.map} := by decide +kernel

theorem quark_explicit_slots :
    explicitSlots Quark.upFootprint = ∅ ∧ explicitSlots Quark.downFootprint = ∅ ∧
    explicitSlots Quark.strangeFootprint = ∅ ∧ explicitSlots Quark.charmFootprint = ∅ ∧
    explicitSlots Quark.bottomFootprint = ∅ ∧ explicitSlots Quark.topFootprint = ∅ := by decide +kernel

/-- Current ring pillars do not imply six separately charged baseline prices. -/
theorem ring_pillars_do_not_force_six_prices (g : EPSpine.Generation)
    (c : PMConstants.PacketGaugeActions.Channels) (hc : ProgramClasses.classOf c ≠ 4) :
    (RetainedMap.quietProgram g c).Pillars ∧
      explicitSlots (ReversalEvents.footprint (RetainedMap.quietProgram g c)) = ∅ := by
  refine ⟨RetainedMap.quiet_program_pillars g c hc,?_⟩
  rw [RetainedMap.quiet_footprint_one]
  decide +kernel

/-- A geometric pi-length factor, not a new whole Capacity count or a physical identification. -/
theorem pi_length_price (length : ℝ) :
    Real.pi*length = (length/(Delta : ℝ))*PMSubstrate.capacityTerm PMSubstrate.baseline := by
  norm_num [PMSubstrate.capacityTerm,PMSubstrate.baseline]
  ring

/-- Direct chi factors can be identified arithmetically without deriving the operation. -/
theorem boundary_factor_price (coefficient : ℝ) :
    (chi : ℝ)*coefficient = coefficient*PMSubstrate.mapTerm PMSubstrate.baseline := by
  norm_num [PMSubstrate.mapTerm,PMSubstrate.baseline]
  ring

/-- Numerical equality does not identify a physical pillar or resource ownership. -/
theorem price_support_not_determined_by_value :
    cost { events := chi } = cost { map := 1 } ∧
      explicitSlots { events := chi } ≠ explicitSlots { map := 1 } := by
  constructor
  · norm_num [cost,PMSubstrate.mapTerm,PMSubstrate.baseline]
  · decide +kernel

end PMElementaryParticles.LedgerPillars
