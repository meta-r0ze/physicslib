import PersistenceMechanics.DecayChannel
import PMElementaryParticles.MuonLifetimeHigherOrder
import PMElementaryParticles.TauBranching
import PMElementaryParticles.TauE8
import PMHadrons.PionWidth
import PMHadrons.ChargedCurrentRate
import PMHadrons.KaonSemileptonic
import Mathlib.Tactic

/-! **Experimental/candidate module.**

# Particle channel inventory

A particle decay is a finite list of partial channels. Each rate is in electron
mass units and has a provenance label. `modeledLifetime` requires a positive
sum and a rate for every listed channel.
-/

noncomputable section
namespace PMHadrons.ParticleChannels
open PMElementaryParticles

open PersistenceMechanics.Decay

/-- Provenance label for a partial rate. -/
inductive RateStatus
  | e8
  | e8LeadingOrder
  | calibrated
  | modelInput
  | blocked
  deriving DecidableEq, Repr

structure ParticleChannel where
  name : String
  rate : ℝ
  status : RateStatus

/-- Sum of the listed rates, including any placeholders. -/
def totalRate (channels : List ParticleChannel) : ℝ :=
  PersistenceMechanics.Rates.parallelRate (channels.map ParticleChannel.rate)

/-- A channel's fraction of the listed rate sum. -/
def branching (channels : List ParticleChannel) (c : ParticleChannel) : ℝ :=
  c.rate / totalRate channels

/-- Reciprocal of the listed rate sum, in electron time units. -/
def totalLifetime (channels : List ParticleChannel) (h : 0 < totalRate channels) : ℝ :=
  PersistenceMechanics.Rates.meanLife (totalRate channels) h

theorem totalLifetime_pos (channels : List ParticleChannel)
    (h : 0 < totalRate channels) : 0 < totalLifetime channels h :=
  PersistenceMechanics.Rates.meanLife_pos h

/-- The modeled lifetime when every listed channel has a supplied or derived
rate and the sum is positive. -/
def modeledLifetime (channels : List ParticleChannel) : Option ℝ :=
  if channels.any (fun c => decide (c.status = .blocked)) then none
  else if h : 0 < totalRate channels then some (totalLifetime channels h) else none

/-- Recover a natural-unit width from an inverse width in seconds. -/
def rateFromSeconds (seconds : ℝ) : ℝ := PhysicalUnits.electronTime / seconds

theorem seconds_of_rateFromSeconds {seconds : ℝ} (hs : 0 < seconds) :
    PhysicalUnits.electronTime / rateFromSeconds seconds = seconds := by
  unfold rateFromSeconds
  field_simp [PhysicalUnits.electronTime_pos.ne', hs.ne']

/-- Inclusive muon channel with the supplied Fermi-theory QED coefficients. -/
def muonChannels : List ParticleChannel :=
  [⟨"e ν ν̄ [γ]", rateFromSeconds MuonLifetimeHigherOrder.lifetime, .modelInput⟩]

theorem muon_channel_seconds :
    PhysicalUnits.electronTime / totalRate muonChannels = MuonLifetimeHigherOrder.lifetime := by
  simpa [totalRate, muonChannels] using seconds_of_rateFromSeconds
    (lt_trans (by norm_num) MuonLifetimeHigherOrder.lifetime_bounds.1)

/-! Tau channels are conditional on the supplied electronic branching fraction. -/
section Tau
variable (electronicBranch : ℝ)

noncomputable def tauTotalRate : ℝ := 1 / TauE8.tauLifetimeE8 electronicBranch

def tauBmu : ℝ := electronicBranch * MassiveWidth.phase TauBranching.r
def tauBhad : ℝ := 1 - electronicBranch - tauBmu electronicBranch
def tauElectronChannel : ParticleChannel := ⟨"e ν ν̄", tauTotalRate electronicBranch * electronicBranch, .calibrated⟩
def tauMuonChannel : ParticleChannel := ⟨"μ ν ν̄", tauTotalRate electronicBranch * tauBmu electronicBranch, .calibrated⟩
def tauChannels : List ParticleChannel :=
  [tauElectronChannel electronicBranch, tauMuonChannel electronicBranch,
    ⟨"hadrons", tauTotalRate electronicBranch * tauBhad electronicBranch, .modelInput⟩]

theorem tau_channel_sum : totalRate (tauChannels electronicBranch) = tauTotalRate electronicBranch := by
  simp [totalRate, tauChannels, tauElectronChannel, tauMuonChannel, tauBhad]
  ring

theorem tau_leptonic_ratio (hb : 0 < electronicBranch) :
    (tauMuonChannel electronicBranch).rate / (tauElectronChannel electronicBranch).rate =
      MassiveWidth.phase TauBranching.r := by
  have ht : tauTotalRate electronicBranch ≠ 0 :=
    (one_div_pos.mpr (TauE8.tauLifetimeE8_pos hb)).ne'
  simp only [tauMuonChannel, tauElectronChannel, tauBmu]
  field_simp [ht, hb.ne']

theorem tau_hadronic_fraction_pos (hb : 0 ≤ electronicBranch)
    (hsmall : electronicBranch < 1 / 2) : 0 < tauBhad electronicBranch := by
  unfold tauBhad tauBmu
  nlinarith [mul_le_mul_of_nonneg_left TauBranching.phase_bounds.2.le hb]

end Tau

def pionMuonChannel : ParticleChannel :=
  ⟨"μ⁺ ν [γ]", rateFromSeconds ChargedCurrentRate.pionMuLifetimeSeconds, .modelInput⟩

theorem pion_muon_channel_seconds :
    PhysicalUnits.electronTime / pionMuonChannel.rate = ChargedCurrentRate.pionMuLifetimeSeconds :=
  seconds_of_rateFromSeconds (lt_trans (by norm_num) ChargedCurrentRate.pionMuLifetimeSeconds_bounds.1)

/-- The inclusive muonic partial width and the tree-level electronic channel. -/
noncomputable def pionChannels : List ParticleChannel :=
  [pionMuonChannel
  , ⟨"e⁺ ν", PMHadrons.PionWidth.pionElectronWidthE8, .e8⟩
  ]

def kaonMuonChannel : ParticleChannel :=
  ⟨"μ⁺ ν [γ]", rateFromSeconds ChargedCurrentRate.kaonMuLifetimeSeconds, .modelInput⟩

theorem kaon_muon_channel_seconds :
    PhysicalUnits.electronTime / kaonMuonChannel.rate = ChargedCurrentRate.kaonMuLifetimeSeconds :=
  seconds_of_rateFromSeconds (lt_trans (by norm_num) ChargedCurrentRate.kaonMuLifetimeSeconds_bounds.1)

/-- The inclusive muonic partial width uses the supplied radiative factor.
The semileptonic `K_ℓ3` modes are E8 **leading order**
(unit form factor, `m_ℓ → 0`, E8 neutral-pion mass); the nonleptonic multibody
modes stay blocked on the bound-state matrix element. -/
noncomputable def kaonChannels : List ParticleChannel :=
  [kaonMuonChannel
  , ⟨"π⁺ π⁰", 0, .blocked⟩
  , ⟨"π⁺ π⁺ π⁻", 0, .blocked⟩
  , ⟨"π⁰ e⁺ ν", PMHadrons.KaonSemileptonic.kaonL3Width, .e8LeadingOrder⟩
  , ⟨"π⁰ μ⁺ ν", PMHadrons.KaonSemileptonic.kaonL3Width, .e8LeadingOrder⟩
  ]

theorem kaon_modeled_lifetime_eq_none : modeledLifetime kaonChannels = none := by
  simp [modeledLifetime, kaonChannels, kaonMuonChannel]

end PMHadrons.ParticleChannels
