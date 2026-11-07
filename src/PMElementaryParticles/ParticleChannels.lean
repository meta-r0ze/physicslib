import PersistenceMechanics.DecayChannel
import PMElementaryParticles.MuonLifetime
import PMElementaryParticles.TauE8
import PMElementaryParticles.PionWidth
import PMElementaryParticles.KaonWidth
import Mathlib.Tactic

/-! **Experimental/candidate module.**

# Particle channel inventory

A particle decay is a finite list of partial channels.  Each channel records its
rate and whether that rate is E8, calibrated, model-input, or blocked.
-/

noncomputable section
namespace PMElementaryParticles.ParticleChannels

open PersistenceMechanics.Decay

/-- Provenance label for a partial rate. -/
inductive RateStatus
  | e8
  | calibrated
  | modelInput
  | blocked
  deriving DecidableEq, Repr

structure ParticleChannel where
  name : String
  rate : ℝ
  status : RateStatus

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

/-- Muon channel. -/
def muonChannels : List ParticleChannel :=
  [⟨"e ν ν̄", PMElementaryParticles.MuonLifetime.muonWidth, .e8⟩]

/-- Tau total rate from the E8-input lifetime. -/
noncomputable def tauTotalRate : ℝ :=
  1 / PMElementaryParticles.TauE8.tauLifetimeE8

/-- Supplied tau branching fractions (comparison data). -/
def tauBe : ℝ := 0.1782
def tauBmu : ℝ := 0.1739
def tauBhad : ℝ := 0.6479

/-- Tau channels: leptonic rates calibrated; hadronic channel model-input. -/
noncomputable def tauChannels : List ParticleChannel :=
  [⟨"e ν ν̄", tauTotalRate * tauBe, .calibrated⟩
  , ⟨"μ ν ν̄", tauTotalRate * tauBmu, .calibrated⟩
  , ⟨"hadrons", tauTotalRate * tauBhad, .modelInput⟩
  ]

/-- Pion channels: μν is E8; the electron mode is blocked. -/
noncomputable def pionChannels : List ParticleChannel :=
  [⟨"μ⁺ ν", PMElementaryParticles.PionWidth.pionWidthE8, .e8⟩
  , ⟨"e⁺ ν", PMElementaryParticles.PionWidth.pionElectronWidthE8, .e8⟩
  ]

/-- Kaon channels: μν is E8; multibody modes are blocked. -/
noncomputable def kaonChannels : List ParticleChannel :=
  [⟨"μ⁺ ν", PMElementaryParticles.KaonWidth.kaonWidthE8, .e8⟩
  , ⟨"π⁺ π⁰", 0, .blocked⟩
  , ⟨"π⁺ π⁺ π⁻", 0, .blocked⟩
  , ⟨"π⁰ e⁺ ν", 0, .blocked⟩
  , ⟨"π⁰ μ⁺ ν", 0, .blocked⟩
  ]

end PMElementaryParticles.ParticleChannels
