import PMSubstrate.SpeciesFootprints
import PMElementaryParticles.SpacetimeProgram

/-!
# Declared species ledgers as level towers

Every result here is about the supplied SpeciesFootprints ledgers [Premise].
It is not a derivation of a persistent nested system, a workload, a tier or a
physical level cost. The only cost is OccupancyCost.cost. cost_tower supplies
the same additive form used by the downstream PMAtoms.SystemTower.

We use telescoping increments of the existing whole-count footprints. Counts
stay natural. Signed pillar charges and residual differences remain signed.
In particular, a negative inherited event term cannot be put in events.
Tau's minus sigma*Delta is minus the muon LEADING term, not the whole muon.
The increment from muon to tau cancels the old spin/feedback residual and
adds the tau residual. These cancellations are ledger identities, not jobs.
A zero incremental pillar field does not mean that a level has no such role.

Leptons use the declared unit entry, then muon, then tau. Down-type ledgers
use down, strange, bottom. Up-type has entries at 0,2,3 and no declared entry
at 1. Its missing cumulative footprint through level 1 is an explicit parameter
between the known event counts, not an invented zero-cost level. All other fields of that parameter
are unconstrained by these identities. The tower telescopes for every such
parameter; it therefore does not determine its physical value or role.
No disjoint physical resource ownership is proved by these identities.
The relation of the supplied quark point entries to the primitive unit is open.

| Family | Declared leading pattern | What breaks a common series |
| --- | --- | --- |
| Charged lepton | unit; sigma*Delta; chi*Delta^2-sigma*Delta | Multipliers change. Tau subtracts muon's leading term but does not retain muon's spin/feedback terms. |
| Down | D*Delta^n/eta for n=0,1,2 | The leading series is geometric. Full costs have distinct sigma, chi*sigma and Delta^2*chi/sigma residual terms. |
| Up | D/eta; D*Delta^2/(eta*(sigma-chi)); Delta^3*(D+1/D) | No level-1 species entry; charm has colour dilution, top drops eta and adds the reciprocal-capacity term. |

The named inheritance theorems below record these facts exactly. The floors
in quark events are kept unchanged. No value theorem or reporter row changes.
-/

noncomputable section
namespace PMElementaryParticles.LedgerLevels
open PMSubstrate.OccupancyCost PMSubstrate.E8Values
open PMSubstrate.SpeciesFootprints

/-- The declared point/unit account; no physical species identification is proved here. -/
def unitLevel : Footprint := { events := 1 }

/-- A bookkeeping increment, only used with monotone whole event/cell counts. -/
def increment (a b : Footprint) : Footprint :=
  ⟨b.events-a.events, b.cells-a.cells, b.capacity-a.capacity, b.map-a.map,
    b.protocol-a.protocol, b.governor-a.governor, b.toll-a.toll,
    b.margin-a.margin, b.residual-a.residual⟩

private theorem add_zero (f : Footprint) : f.add {} = f := by
  cases f
  simp [Footprint.add]

private theorem add_assoc (a b c : Footprint) : (a.add b).add c = a.add (b.add c) := by
  cases a; cases b; cases c
  simp [Footprint.add, _root_.add_assoc]

/-- Legal natural counts telescope; all signed charges and residuals telescope too. -/
theorem add_increment (a b : Footprint) (he : a.events ≤ b.events) (hc : a.cells ≤ b.cells) :
    a.add (increment a b) = b := by
  cases a; cases b
  dsimp [increment, Footprint.add] at *
  congr 1 <;> first | omega | ring

private theorem two_levels (a b : Footprint) (he : a.events ≤ b.events) (hc : a.cells ≤ b.cells) :
    tower [a, increment a b] = b := by
  dsimp [tower]
  rw [add_zero, add_increment a b he hc]

private theorem three_levels (a b c : Footprint)
    (he : a.events ≤ b.events) (hf : b.events ≤ c.events)
    (hc : a.cells ≤ b.cells) (hd : b.cells ≤ c.cells) :
    tower [a, increment a b, increment b c] = c := by
  dsimp [tower]
  rw [add_zero, ← add_assoc, add_increment a b he hc, add_increment b c hf hd]

private theorem four_levels (a b c d : Footprint)
    (he : a.events ≤ b.events) (hf : b.events ≤ c.events) (hg : c.events ≤ d.events)
    (hc : a.cells ≤ b.cells) (hd : b.cells ≤ c.cells) (hi : c.cells ≤ d.cells) :
    tower [a, increment a b, increment b c, increment c d] = d := by
  dsimp [tower]
  rw [add_zero, ← add_assoc, ← add_assoc, add_increment a b he hc,
    add_increment b c hf hd, add_increment c d hg hi]

/-- These order facts reuse the existing declared event-field certificate. -/
theorem declared_event_order :
    unitLevel.events ≤ Lepton.muonFootprint.events ∧
    Lepton.muonFootprint.events ≤ Lepton.tauFootprint.events ∧
    Quark.downFootprint.events ≤ Quark.strangeFootprint.events ∧
    Quark.strangeFootprint.events ≤ Quark.bottomFootprint.events ∧
    Quark.upFootprint.events ≤ Quark.charmFootprint.events ∧
    Quark.charmFootprint.events ≤ Quark.topFootprint.events := by
  obtain ⟨hm, ht, hu, hd, hs, hc, hb, hp⟩ := SpacetimeProgram.declared_event_counts
  change 1 ≤ Lepton.muonFootprint.events ∧ _
  omega

def electronLevels : List Footprint := [unitLevel]
def muonLevels : List Footprint := [unitLevel, increment unitLevel Lepton.muonFootprint]
def tauLevels : List Footprint :=
  [unitLevel, increment unitLevel Lepton.muonFootprint, increment Lepton.muonFootprint Lepton.tauFootprint]
def downLevels : List Footprint := [Quark.downFootprint]
def strangeLevels : List Footprint := [Quark.downFootprint, increment Quark.downFootprint Quark.strangeFootprint]
def bottomLevels : List Footprint :=
  [Quark.downFootprint, increment Quark.downFootprint Quark.strangeFootprint,
    increment Quark.strangeFootprint Quark.bottomFootprint]
def upLevels : List Footprint := [Quark.upFootprint]

/-- No level-1 up-type entry is supplied by SpeciesFootprints. Keep it unknown. -/
def charmLevels (level1 : Footprint) : List Footprint :=
  [Quark.upFootprint, increment Quark.upFootprint level1, increment level1 Quark.charmFootprint]
def topLevels (level1 : Footprint) : List Footprint :=
  [Quark.upFootprint, increment Quark.upFootprint level1, increment level1 Quark.charmFootprint,
    increment Quark.charmFootprint Quark.topFootprint]

theorem declared_electron_tower : tower electronLevels = unitLevel := by
  exact add_zero unitLevel

theorem declared_muon_tower : tower muonLevels = Lepton.muonFootprint :=
  two_levels _ _ declared_event_order.1 (by change 0 ≤ 0; omega)

theorem declared_tau_tower : tower tauLevels = Lepton.tauFootprint :=
  three_levels _ _ _ declared_event_order.1 declared_event_order.2.1
    (by change 0 ≤ 0; omega) (by change 0 ≤ 0; omega)

theorem declared_down_tower : tower downLevels = Quark.downFootprint := add_zero _
theorem declared_strange_tower : tower strangeLevels = Quark.strangeFootprint :=
  two_levels _ _ declared_event_order.2.2.1 (by change 0 ≤ 0; omega)
theorem declared_bottom_tower : tower bottomLevels = Quark.bottomFootprint :=
  three_levels _ _ _ declared_event_order.2.2.1 declared_event_order.2.2.2.1
    (by change 0 ≤ 0; omega) (by change 0 ≤ 0; omega)
theorem declared_up_tower : tower upLevels = Quark.upFootprint := add_zero _

theorem declared_charm_tower (level1 : Footprint)
    (h0 : Quark.upFootprint.events ≤ level1.events) (h2 : level1.events ≤ Quark.charmFootprint.events)
    (hcell : level1.cells = 0) : tower (charmLevels level1) = Quark.charmFootprint :=
  three_levels _ _ _ h0 h2 (by change 0 ≤ level1.cells; omega)
    (by change level1.cells ≤ 0; omega)

theorem declared_top_tower (level1 : Footprint)
    (h0 : Quark.upFootprint.events ≤ level1.events) (h2 : level1.events ≤ Quark.charmFootprint.events)
    (hcell : level1.cells = 0) : tower (topLevels level1) = Quark.topFootprint :=
  four_levels _ _ _ _ h0 h2 declared_event_order.2.2.2.2.2
    (by change 0 ≤ level1.cells; omega) (by change level1.cells ≤ 0; omega)
    (by change 0 ≤ 0; omega)

/-- Additive tower prices are exactly the old declared costs. -/
theorem declared_lepton_costs :
    (electronLevels.map cost).sum = 1 ∧
    (muonLevels.map cost).sum = Lepton.muon ∧ (tauLevels.map cost).sum = Lepton.tau := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← cost_tower, declared_electron_tower]
    exact cost_oneEvent
  · rw [← cost_tower, declared_muon_tower]
  · rw [← cost_tower, declared_tau_tower]; rfl

theorem declared_down_costs :
    (downLevels.map cost).sum = Quark.down ∧ (strangeLevels.map cost).sum = Quark.strange ∧
      (bottomLevels.map cost).sum = Quark.bottom := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← cost_tower, declared_down_tower]
  · rw [← cost_tower, declared_strange_tower]
  · rw [← cost_tower, declared_bottom_tower]

theorem declared_up_costs (level1 : Footprint)
    (h0 : Quark.upFootprint.events ≤ level1.events) (h2 : level1.events ≤ Quark.charmFootprint.events)
    (hcell : level1.cells = 0) :
    (upLevels.map cost).sum = Quark.up ∧ (charmLevels level1 |>.map cost).sum = Quark.charm ∧
      (topLevels level1 |>.map cost).sum = Quark.top := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← cost_tower, declared_up_tower]
  · rw [← cost_tower, declared_charm_tower level1 h0 h2 hcell]
  · rw [← cost_tower, declared_top_tower level1 h0 h2 hcell]

theorem declared_muon_leading_from_unit :
    Lepton.muonSweep = (sigma : ℝ)*(Delta : ℝ)*cost unitLevel := by
  rw [show cost unitLevel = 1 from cost_oneEvent]
  unfold Lepton.muonSweep
  ring

theorem declared_lepton_event_levels :
    (increment unitLevel Lepton.muonFootprint).events = sigma*Delta-1 ∧
    (increment Lepton.muonFootprint Lepton.tauFootprint).events =
      chi*Delta^2-2*(sigma*Delta) := by
  constructor
  · rfl
  · change (chi*Delta^2-sigma*Delta)-sigma*Delta = chi*Delta^2-2*(sigma*Delta)
    rw [Nat.sub_sub, two_mul]

theorem declared_tau_increment_residual :
    (increment Lepton.muonFootprint Lepton.tauFootprint).residual =
      -(D : ℝ)+Lepton.muonSpinLag-Lepton.muonFeedback := by
  change -(D : ℝ)-(-Lepton.muonSpinLag+Lepton.muonFeedback) = _
  ring

/-- The inherited subtraction is the muon's leading term, with its sign kept. -/
theorem declared_tau_inherits_muon_leading :
    Lepton.tauCoreLatency = Lepton.muonSweep ∧ -Lepton.tauCoreLatency = -Lepton.muonSweep := by
  unfold Lepton.tauCoreLatency Lepton.muonSweep
  constructor <;> ring

theorem declared_tau_signed_inheritance : Lepton.tau + Lepton.muonSweep = Lepton.tauBoundary-Lepton.tauAnchors := by
  rw [Lepton.tau_ledger]
  unfold Lepton.muonSweep Lepton.tauBoundary Lepton.tauAnchors
  ring

theorem declared_down_leading_powers :
    Quark.anchorPoint/Quark.η = (D : ℝ)*(Delta : ℝ)^0/Quark.η ∧
    Quark.anchorLine/Quark.η = (D : ℝ)*(Delta : ℝ)^1/Quark.η ∧
    Quark.anchorArea/Quark.η = (D : ℝ)*(Delta : ℝ)^2/Quark.η := by
  simp [Quark.anchorPoint, Quark.anchorLine, Quark.anchorArea]

theorem declared_down_leading_inheritance :
    Quark.anchorLine/Quark.η = (Delta : ℝ)*(Quark.anchorPoint/Quark.η) ∧
    Quark.anchorArea/Quark.η = (Delta : ℝ)*(Quark.anchorLine/Quark.η) := by
  unfold Quark.anchorLine Quark.anchorPoint Quark.anchorArea
  constructor <;> ring

theorem declared_down_corrections : Quark.dragSym = (chi : ℝ)*Quark.symWeight ∧
    Quark.latencyTerm = (Delta : ℝ)^2*((chi : ℝ)/(sigma : ℝ)) := ⟨rfl,rfl⟩

theorem declared_down_full_inheritance :
    Quark.strange = (Delta : ℝ)*Quark.down+
      (Quark.dragSym-(Delta : ℝ)*Quark.symWeight)/Quark.η ∧
    Quark.bottom = (Delta : ℝ)*Quark.strange+
      (Quark.latencyTerm-(Delta : ℝ)*Quark.dragSym)/Quark.η := by
  constructor
  · rw [Quark.strange_ledger, Quark.down_ledger]
    unfold Quark.anchorLine Quark.anchorPoint
    ring
  · rw [Quark.bottom_ledger, Quark.strange_ledger]
    unfold Quark.anchorArea Quark.anchorLine
    ring

theorem declared_charm_inheritance :
    Quark.anchorArea/(Quark.η*Quark.colourDim) =
      (Delta : ℝ)^2*(Quark.anchorPoint/Quark.η)/Quark.colourDim := by
  unfold Quark.anchorArea Quark.anchorPoint
  ring

theorem declared_top_anchor_inheritance : Quark.anchorVolume = (Delta : ℝ)*Quark.anchorArea := by
  unfold Quark.anchorVolume Quark.anchorArea
  ring

/-- Top is not one more unchanged factor Delta of the diluted charm leading term. -/
theorem declared_top_breaks_charm_scaling :
    Quark.anchorVolume+Quark.capLeakTerm ≠
      (Delta : ℝ)*(Quark.anchorArea/(Quark.η*Quark.colourDim)) := by
  norm_num [Quark.anchorVolume, Quark.capLeakTerm, Quark.capLeak, Quark.anchorArea,
    Quark.η, Quark.colourDim, overhead, D_eq, Delta_eq, chi_eq, sigma_eq, RM_eq]

end PMElementaryParticles.LedgerLevels
