import PersistenceMechanics.DecayChannel
import PMElementaryParticles.BetaLattice
import PMAtoms.AlphaFinite
import PMAtoms.FissionYield
import Mathlib.Tactic

/-! **Experimental/candidate module.**

# Six-pillar instantiations

Beta, alpha, and fission rates are recovered from the shared `DecayChannel`
template.  These are consistency proofs: no numerical value is changed.

Each factor found for the chains sits in its own pillar slot:

| factor | slot |
| --- | --- |
| open-mode fraction (beta) | capacity |
| alpha workload `K` (capacity of the attempt) | capacity |
| flux `1/Δ`, or the toll `c0` | toll |
| daughter-closure hindrance (overlap of parent and daughter identity) | map |
| alpha preformation | protocol |
| superheavy gate `exp(−χ·max(Z−100,0))` | governor |
| fission yield weight | margin |
| Geiger / fissility barrier | action |

`alphaDecayChannel` and `fissionDecayChannel` keep the earlier one-slot packing; the
`*PillarChannel` versions split it and have the same rate.
-/

noncomputable section
namespace PMAtoms
open PMElementaryParticles PMHadrons

open PersistenceMechanics.Decay

/-- Beta lattice channel as a six-pillar channel. -/
def betaDecayChannel (c0 : ℝ) (c : BetaLatticeChannel) : DecayChannel :=
  { capacity := 1
    map := 1
    protocol := (c.active : ℝ) / (c.size : ℝ)
    governor := 1
    toll := c0
    margin := 1
    action := 0 }

theorem betaDecayChannel_rate_eq (β c0 : ℝ) (c : BetaLatticeChannel) :
    rate β (betaDecayChannel c0 c) = betaLatticeRate β c0 c := by
  rw [betaLatticeRate_eq]
  unfold betaDecayChannel rate
  norm_num
  ring

/-- Alpha finite channel as a six-pillar channel. -/
def alphaDecayChannel (attempt : ℝ) (p : Nuclide) : DecayChannel :=
  { capacity := 1
    map := 1
    protocol := alphaWidthE8 1 p
    governor := 1
    toll := attempt
    margin := 1
    action := 0 }

theorem alphaDecayChannel_rate_eq (attempt : ℝ) (p : Nuclide) :
    rate 1 (alphaDecayChannel attempt p) = alphaFiniteRate attempt p := by
  unfold alphaDecayChannel rate alphaFiniteRate
  norm_num

/-- One fission split as a six-pillar channel. -/
def fissionDecayChannel (p : Nuclide) (s : FissionSplit) : DecayChannel :=
  { capacity := 1
    map := 1
    protocol := 1
    governor := 1
    toll := alphaAttempt p
    margin := 1
    action := s.costWithGovernor p }

/-- Fission surface channels. -/
def fissionDecayChannels (p : Nuclide) : List DecayChannel :=
  (fissionSplits p).map (fissionDecayChannel p)

theorem fissionDecayChannel_rate_eq (p : Nuclide) (s : FissionSplit) :
    rate 1 (fissionDecayChannel p s) =
      alphaAttempt p * Real.exp (-(s.costWithGovernor p)) := by
  unfold fissionDecayChannel rate
  norm_num

/-- One weighted yield as a six-pillar channel. -/
def fissionYieldDecayChannel (p : Nuclide) (y : FissionYield) : DecayChannel :=
  { capacity := 1
    map := 1
    protocol := 1
    governor := 1
    toll := alphaAttempt p
    margin := y.weight
    action := y.split.costWithSubshell p }

/-- Full weighted yield channels. -/
def fissionYieldDecayChannels (p : Nuclide) : List DecayChannel :=
  (fissionYields p).map (fissionYieldDecayChannel p)

/-! ## Pillar-resolved channels -/

/-- Beta: the open-mode fraction is the channel's capacity. -/
def betaPillarChannel (c0 : ℝ) (c : BetaLatticeChannel) : DecayChannel :=
  { capacity := (c.active : ℝ) / (c.size : ℝ)
    map := 1
    protocol := 1
    governor := 1
    toll := c0
    margin := 1
    action := 0 }

theorem betaPillarChannel_rate_eq (β c0 : ℝ) (c : BetaLatticeChannel) :
    rate β (betaPillarChannel c0 c) = betaLatticeRate β c0 c := by
  rw [← betaDecayChannel_rate_eq]
  unfold betaPillarChannel betaDecayChannel rate
  ring

/-- Alpha: workload × flux is capacity × toll; closure hindrance is map; preformation is
protocol; the Geiger barrier is the action. -/
def alphaPillarChannel (p : Nuclide) : DecayChannel :=
  { capacity := alphaWorkload p
    map := alphaPhaseSpace p
    protocol := alphaPreformationShell p
    governor := 1
    toll := alphaFlux
    margin := 1
    action := alphaBarrierGeiger p.Z (alphaQ p) }

theorem alphaPillarChannel_rate_eq (p : Nuclide) :
    rate 1 (alphaPillarChannel p) = alphaFiniteRate (alphaAttempt p) p := by
  unfold alphaPillarChannel rate alphaFiniteRate alphaWidthE8 alphaAttempt
  ring

/-- Fission: the superheavy term is the governor, the fragment-resolved cost the action. -/
def fissionPillarChannel (p : Nuclide) (s : FissionSplit) : DecayChannel :=
  { capacity := alphaWorkload p
    map := 1
    protocol := 1
    governor := Real.exp (-(fissionSuperheavyCost p))
    toll := alphaFlux
    margin := 1
    action := s.cost p }

theorem fissionPillarChannel_rate_eq (p : Nuclide) (s : FissionSplit) :
    rate 1 (fissionPillarChannel p s) = rate 1 (fissionDecayChannel p s) := by
  unfold fissionPillarChannel fissionDecayChannel rate FissionSplit.costWithGovernor alphaAttempt
  rw [neg_add, Real.exp_add]
  ring

/-- Fission yield: the subshell cost stays in the action, the yield weight is the margin. -/
def fissionYieldPillarChannel (p : Nuclide) (y : FissionYield) : DecayChannel :=
  { capacity := alphaWorkload p
    map := 1
    protocol := 1
    governor := Real.exp (-(fissionSuperheavyCost p))
    toll := alphaFlux
    margin := y.weight
    action := y.split.cost p + fissionSubshellCost p }

theorem fissionYieldPillarChannel_rate_eq (p : Nuclide) (y : FissionYield) :
    rate 1 (fissionYieldPillarChannel p y) = rate 1 (fissionYieldDecayChannel p y) := by
  unfold fissionYieldPillarChannel fissionYieldDecayChannel rate FissionSplit.costWithSubshell
    FissionSplit.costWithGovernor alphaAttempt
  rw [show -(y.split.cost p + fissionSuperheavyCost p + fissionSubshellCost p) =
    -(fissionSuperheavyCost p) + -(y.split.cost p + fissionSubshellCost p) by ring, Real.exp_add]
  ring

end PMAtoms
