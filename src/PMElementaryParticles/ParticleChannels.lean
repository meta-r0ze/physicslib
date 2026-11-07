import PersistenceMechanics.DecayChannel
import Mathlib.Tactic

/-! **Experimental/candidate module.**

# Particle channel inventory

A particle decay is a finite list of partial channels.  Branching fractions and
the total lifetime are read from the partial rates.
-/

noncomputable section
namespace PMElementaryParticles.ParticleChannels

open PersistenceMechanics.Decay

structure ParticleChannel where
  name : String
  rate : ℝ

/-- Sum of partial rates. -/
def totalRate (channels : List ParticleChannel) : ℝ :=
  List.sum (channels.map (fun c => c.rate))

/-- Branching fraction of one channel. -/
def branching (channels : List ParticleChannel) (c : ParticleChannel) : ℝ :=
  c.rate / totalRate channels

/-- Total lifetime from the channel sum. -/
def totalLifetime (channels : List ParticleChannel) : ℝ :=
  1 / totalRate channels

theorem totalLifetime_pos (channels : List ParticleChannel)
    (h : 0 < totalRate channels) : 0 < totalLifetime channels := by
  unfold totalLifetime
  exact one_div_pos.mpr h

/-- A one-channel inventory: the simple `K⁺ → μ⁺ν` partial case. -/
def singleChannel (name : String) (rate : ℝ) : List ParticleChannel :=
  [⟨name, rate⟩]

end PMElementaryParticles.ParticleChannels
