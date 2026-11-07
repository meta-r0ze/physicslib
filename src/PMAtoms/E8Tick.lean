import PMSubstrate.E8Values
import PMElementaryParticles.CompositeMasses
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.

# E8 tick

The substrate clock period is `Δ = 43` in `m_e` units.  The SI conversion uses
the electron time unit as a supplied unit input.
-/

noncomputable section
namespace PMAtoms

/-- E8 clock period in `m_e` units. -/
def e8Tick : ℝ := (PMSubstrate.E8Values.Delta : ℝ)

theorem e8Tick_eq : e8Tick = 43 := by
  unfold e8Tick
  norm_num [PMSubstrate.E8Values.Delta, PMSubstrate.baseline]

/-- Speed of light in fm/s (unit conversion). -/
def cFmPerSecond : ℝ := 2.99792458e23

/-- Electron time unit `ħ/(m_e c²)` derived from the existing mass/`ħc` inputs. -/
def electronSecond : ℝ :=
  PMElementaryParticles.CompositeMasses.hbarc /
    (PMElementaryParticles.CompositeMasses.me * cFmPerSecond)

theorem electronSecond_eq :
    electronSecond =
      PMElementaryParticles.CompositeMasses.hbarc /
        (PMElementaryParticles.CompositeMasses.me * cFmPerSecond) := rfl

/-- Physical E8 tick in seconds. -/
def e8TickSeconds : ℝ := e8Tick * electronSecond

theorem e8TickSeconds_eq : e8TickSeconds = 43 * electronSecond := by
  rw [e8TickSeconds, e8Tick_eq]

theorem electronSecond_pos : 0 < electronSecond := by
  unfold electronSecond cFmPerSecond PMElementaryParticles.CompositeMasses.hbarc
    PMElementaryParticles.CompositeMasses.me
  norm_num

theorem e8TickSeconds_pos : 0 < e8TickSeconds := by
  unfold e8TickSeconds
  exact mul_pos (by rw [e8Tick_eq]; norm_num) electronSecond_pos

end PMAtoms
