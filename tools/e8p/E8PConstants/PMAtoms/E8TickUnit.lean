import PMAtoms.Values
import PMElementaryParticles.Values
import PMHadrons.Values
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
def electronSecond : ℝ := PMElementaryParticles.Values.electronTime

theorem electronSecond_eq :
    electronSecond = PMElementaryParticles.Values.electronTime := rfl

theorem electronSecond_pos : 0 < electronSecond :=
  PMElementaryParticles.Values.electronTime_pos

/-- Physical E8 tick in seconds. -/
def e8TickSeconds : ℝ := PMAtoms.Values.e8Tick * electronSecond

theorem e8TickSeconds_eq : e8TickSeconds = 43 * electronSecond := by
  rw [e8TickSeconds, PMAtoms.Values.e8Tick_eq]

theorem e8TickSeconds_pos : 0 < e8TickSeconds := by
  unfold e8TickSeconds
  exact mul_pos (by rw [PMAtoms.Values.e8Tick_eq]; norm_num) electronSecond_pos

/-- Muon lifetime in E8 ticks. -/
noncomputable def muonLifetimeTicks : ℝ :=
  PMAtoms.Values.lifetimeTicks PMElementaryParticles.Values.muonLifetime

/-- Pion lifetime in E8 ticks. -/
noncomputable def pionLifetimeTicks : ℝ :=
  PMAtoms.Values.lifetimeTicks PMHadrons.Values.pionLifetimeE8

/-- Kaon lifetime in E8 ticks. -/
noncomputable def kaonLifetimeTicks : ℝ :=
  PMAtoms.Values.lifetimeTicks PMHadrons.Values.kaonLifetimeE8

/-- Tau lifetime in E8 ticks. -/
noncomputable def tauLifetimeTicks : ℝ :=
  PMAtoms.Values.lifetimeTicks PMElementaryParticles.Values.tauLifetimeE8

/-- Neutral-pion lifetime in E8 ticks. -/
noncomputable def neutralPionLifetimeTicks : ℝ :=
  PMAtoms.Values.lifetimeTicks PMHadrons.Values.neutralPionLifetimeE8

/-- Pion lifetime after the pion-channel margin, in ticks. -/
noncomputable def pionLifetimeCorrectedTicks : ℝ :=
  PMAtoms.Values.lifetimeTicks (PMHadrons.Values.pionCorrectedLifetime
    PMHadrons.Values.pionLifetimeE8)

/-- Fission tick scales for the test nuclei. -/
noncomputable def u238FissionTicks : ℝ := PMAtoms.Values.lifetimeTicks (PMAtoms.Values.fissionFullLifetime PMAtoms.Values.u238)
noncomputable def cf252FissionTicks : ℝ := PMAtoms.Values.lifetimeTicks (PMAtoms.Values.fissionFullLifetime PMAtoms.Values.cf252)

end E8TickUnit
