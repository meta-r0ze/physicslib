import PMAtoms.E8Tick
import PMHadrons.CompositeMasses
import PMElementaryParticles.MuonLifetime
import PMHadrons.PionWidth
import PMHadrons.KaonWidth
import PMElementaryParticles.TauE8
import PMElementaryParticles.PhysicalUnits
import PMAtoms.FissionYield
import PMAtoms.AlphaFinite
import PMSubstrate.E8Margin
import PMHadrons.NeutralPionWidth
import Mathlib.Tactic

/-! **Comparison / unit conversion.** Not an E8 prediction.

The E8 period is `Δ = 43 m_e` (`E8Tick`).  Converting that to seconds uses the
measured electron mass, `ħc`, and the speed of light.  These constants are
comparison inputs, not E8-derived numbers.
-/

noncomputable section
namespace E8PConstants.E8TickUnit
open PMAtoms PMElementaryParticles PMConstants

/-- Electron time unit `ħ/(m_e c²)` from the canonical conversion module. -/
def electronSecond : ℝ := PMElementaryParticles.PhysicalUnits.electronTime

theorem electronSecond_eq :
    electronSecond = PMElementaryParticles.PhysicalUnits.electronTime := rfl

theorem electronSecond_pos : 0 < electronSecond :=
  PMElementaryParticles.PhysicalUnits.electronTime_pos

/-- Physical E8 tick in seconds. -/
def e8TickSeconds : ℝ := e8Tick * electronSecond

theorem e8TickSeconds_eq : e8TickSeconds = 43 * electronSecond := by
  rw [e8TickSeconds, e8Tick_eq]

theorem e8TickSeconds_pos : 0 < e8TickSeconds := by
  unfold e8TickSeconds
  exact mul_pos (by rw [e8Tick_eq]; norm_num) electronSecond_pos

/-- Muon lifetime in E8 ticks. -/
noncomputable def muonLifetimeTicks : ℝ :=
  lifetimeTicks PMElementaryParticles.MuonLifetime.muonLifetime

/-- Pion lifetime in E8 ticks. -/
noncomputable def pionLifetimeTicks : ℝ :=
  lifetimeTicks PMHadrons.PionWidth.pionLifetimeE8

/-- Kaon lifetime in E8 ticks. -/
noncomputable def kaonLifetimeTicks : ℝ :=
  lifetimeTicks PMHadrons.KaonWidth.kaonLifetimeE8

/-- Tau lifetime in E8 ticks. -/
noncomputable def tauLifetimeTicks : ℝ :=
  lifetimeTicks PMElementaryParticles.TauE8.tauLifetimeE8

/-- Neutral-pion lifetime in E8 ticks. -/
noncomputable def neutralPionLifetimeTicks : ℝ :=
  lifetimeTicks PMHadrons.NeutralPionWidth.neutralPionLifetimeE8

/-- Pion lifetime after the pion-channel margin, in ticks. -/
noncomputable def pionLifetimeCorrectedTicks : ℝ :=
  lifetimeTicks (PMSubstrate.E8Margin.pionCorrectedLifetime
    PMHadrons.PionWidth.pionLifetimeE8)

/-- Fission tick scales for the test nuclei. -/
noncomputable def u238FissionTicks : ℝ := lifetimeTicks (fissionFullLifetime u238)
noncomputable def cf252FissionTicks : ℝ := lifetimeTicks (fissionFullLifetime cf252)

end E8TickUnit
