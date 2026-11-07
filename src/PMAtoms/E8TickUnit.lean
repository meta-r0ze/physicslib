import PMAtoms.E8Tick
import PMElementaryParticles.CompositeMasses
import PMElementaryParticles.MuonLifetime
import PMElementaryParticles.PionWidth
import PMElementaryParticles.KaonWidth
import Mathlib.Tactic

/-! **Comparison / unit conversion.** Not an E8 prediction.

The E8 period is `Δ = 43 m_e` (`E8Tick`).  Converting that to seconds uses the
measured electron mass, `ħc`, and the speed of light.  These constants are
comparison inputs, not E8-derived numbers.
-/

noncomputable section
namespace PMAtoms

/-- Speed of light in fm/s (unit conversion). -/
def cFmPerSecond : ℝ := 2.99792458e23

/-- Electron time unit `ħ/(m_e c²)` from the existing mass/`ħc` inputs. -/
def electronSecond : ℝ :=
  PMElementaryParticles.CompositeMasses.hbarc /
    (PMElementaryParticles.CompositeMasses.me * cFmPerSecond)

theorem electronSecond_pos : 0 < electronSecond := by
  unfold electronSecond cFmPerSecond PMElementaryParticles.CompositeMasses.hbarc
    PMElementaryParticles.CompositeMasses.me
  norm_num

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
  lifetimeTicks PMElementaryParticles.PionWidth.pionLifetimeE8

/-- Kaon lifetime in E8 ticks. -/
noncomputable def kaonLifetimeTicks : ℝ :=
  lifetimeTicks PMElementaryParticles.KaonWidth.kaonLifetimeE8

end PMAtoms
