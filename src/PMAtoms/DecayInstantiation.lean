import PersistenceMechanics.DecayChannel
import PMAtoms.BetaLattice
import PMAtoms.AlphaFinite
import PMAtoms.FissionYield
import Mathlib.Tactic

/-! **Experimental/candidate module.**

# Six-pillar instantiations

Beta, alpha, and fission rates are recovered from the shared `DecayChannel`
template.  These are consistency proofs: no numerical value is changed.
-/

noncomputable section
namespace PMAtoms

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


end PMAtoms
