import PMAtoms.NuclearLedger
import PMAtoms.BetaDecay
import PMAtoms.CollectiveRegime
import PMAtoms.NuclearRegime
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.

# Nuclear decay Q-values

The existing `Nucleus.Decay` ledger proves charge, baryon and lepton
conservation.  This module adds the mass comparison for the four nuclear
channels:

```
β⁻, β⁺, α, fission.
```

All masses are in `m_e` units and use the certified smooth ledger
`NuclearLedger.certifiedMass`.  These are mass-allowed tests only; the rate
layer is separate.
-/

noncomputable section
namespace PMAtoms
open PMElementaryParticles PMHadrons

/-- `β⁻` Q-value: parent minus daughter minus the emitted electron. -/
def nuclearBetaMinusQ (p : Nuclide) : ℝ :=
  certifiedMass p.Z p.N - certifiedMass (p.Z + 1) (p.N - 1) - 1

/-- `β⁺` Q-value: parent minus daughter minus the emitted positron. -/
def nuclearBetaPlusQ (p : Nuclide) : ℝ :=
  certifiedMass p.Z p.N - certifiedMass (p.Z - 1) (p.N + 1) - 1

/-- Alpha Q-value: parent minus daughter minus the alpha cluster. -/
def nuclearAlphaQ (p : Nuclide) : ℝ :=
  certifiedMass p.Z p.N - certifiedMass (p.Z - 2) (p.N - 2) -
    certifiedMass 2 2

/-- Fission Q-value for two supplied fragments. -/
def nuclearFissionQ (p f1 f2 : Nuclide) : ℝ :=
  certifiedMass p.Z p.N - certifiedMass f1.Z f1.N - certifiedMass f2.Z f2.N

/-- A channel is mass-allowed when its Q-value is positive. -/
def NuclearMassAllowed (q : ℝ) : Prop := 0 < q

theorem nuclearMassAllowed_iff {q : ℝ} :
    NuclearMassAllowed q ↔ 0 < q := Iff.rfl

/-- `β⁻` mass-allowed. -/
def betaMinusMassAllowed (p : Nuclide) : Prop :=
  NuclearMassAllowed (nuclearBetaMinusQ p)

/-- `β⁺` mass-allowed. -/
def betaPlusMassAllowed (p : Nuclide) : Prop :=
  NuclearMassAllowed (nuclearBetaPlusQ p)

/-- Alpha mass-allowed. -/
def alphaMassAllowed (p : Nuclide) : Prop :=
  NuclearMassAllowed (nuclearAlphaQ p)

/-- Fission mass-allowed. -/
def fissionMassAllowed (p f1 f2 : Nuclide) : Prop :=
  NuclearMassAllowed (nuclearFissionQ p f1 f2)

theorem betaMinusMassAllowed_iff (p : Nuclide) :
    betaMinusMassAllowed p ↔ 0 < nuclearBetaMinusQ p := Iff.rfl

theorem betaPlusMassAllowed_iff (p : Nuclide) :
    betaPlusMassAllowed p ↔ 0 < nuclearBetaPlusQ p := Iff.rfl

theorem alphaMassAllowed_iff (p : Nuclide) :
    alphaMassAllowed p ↔ 0 < nuclearAlphaQ p := Iff.rfl

theorem fissionMassAllowed_iff (p f1 f2 : Nuclide) :
    fissionMassAllowed p f1 f2 ↔ 0 < nuclearFissionQ p f1 f2 := Iff.rfl

/-- `β⁻` Q is the parent mass minus the beta channel's total mass. -/
theorem nuclearBetaMinusQ_eq_betaChannel (p : Nuclide) :
    nuclearBetaMinusQ p =
      certifiedMass p.Z p.N - (betaChannel p).totalMass := by
  simp [nuclearBetaMinusQ, betaChannel, CollectiveChannel.totalMass]
  ring

/-- Alpha Q is the parent mass minus the alpha channel's mass (the barrier is a
separate rate input). -/
theorem nuclearAlphaQ_eq_alphaChannel (p : Nuclide) :
    nuclearAlphaQ p =
      certifiedMass p.Z p.N - (alphaChannel p).mass := by
  simp [nuclearAlphaQ, alphaChannel, certifiedMass]
  ring

/-- Fission Q is the parent mass minus the fragment mass sum. -/
theorem nuclearFissionQ_eq_fissionChannel (p f1 f2 : Nuclide) :
    nuclearFissionQ p f1 f2 =
      certifiedMass p.Z p.N - (fissionChannel p f1 f2).mass := by
  simp [nuclearFissionQ, fissionChannel, certifiedMass]
  ring

/-- Regime label for the parent. -/
def nuclearDecayRegime (p : Nuclide) : NuclearRegime :=
  regimeOf p.Z p.N

end PMAtoms

namespace PMAtoms
open PMElementaryParticles PMHadrons

theorem pb_nuclearDecayRegime :
    nuclearDecayRegime ⟨82, 126⟩ = .mid := by
  unfold nuclearDecayRegime
  exact pb_regime

theorem u_nuclearDecayRegime :
    nuclearDecayRegime ⟨92, 146⟩ = .deformedActinide := by
  unfold nuclearDecayRegime
  exact u_regime

theorem cm_nuclearDecayRegime :
    nuclearDecayRegime ⟨96, 148⟩ = .deformedActinide := by
  unfold nuclearDecayRegime
  exact cm_regime

theorem cf_nuclearDecayRegime :
    nuclearDecayRegime ⟨98, 154⟩ = .beyondFrontier := by
  unfold nuclearDecayRegime
  exact cf_regime

/-- Which ledger governs a nuclear parent. -/
inductive NuclearLedgerKind
  | smooth
  | collective
  deriving DecidableEq, Repr

/-- The smooth ledger through the deformed frontier; the collective ledger beyond it. -/
def nuclearLedgerKind (p : Nuclide) : NuclearLedgerKind :=
  if regimeOf p.Z p.N = .beyondFrontier then .collective else .smooth

/-- Regime-aware persistence: mass-allowed inside the certified domain; collective
barrier/rate envelope beyond it. -/
def regimePersists (p : Nuclide) (q : ℝ) (channels : List CollectiveChannel) : Prop :=
  match nuclearLedgerKind p with
  | .smooth => NuclearMassAllowed q
  | .collective => CollectivePersists (certifiedMass p.Z p.N) channels

theorem cm_nuclearLedgerKind :
    nuclearLedgerKind ⟨96, 148⟩ = .smooth := by
  unfold nuclearLedgerKind
  rw [cm_regime]
  rfl

theorem cf_nuclearLedgerKind :
    nuclearLedgerKind ⟨98, 154⟩ = .collective := by
  unfold nuclearLedgerKind
  rw [cf_regime]
  rfl

theorem cm_regimePersists_iff (q : ℝ) (channels : List CollectiveChannel) :
    regimePersists ⟨96, 148⟩ q channels ↔ NuclearMassAllowed q := by
  simp [regimePersists, cm_nuclearLedgerKind]

theorem cf_regimePersists_iff (q : ℝ) (channels : List CollectiveChannel) :
    regimePersists ⟨98, 154⟩ q channels ↔
      CollectivePersists (certifiedMass 98 154) channels := by
  simp [regimePersists, cf_nuclearLedgerKind]

/-- **Smooth decision rule.** Inside the certified domain, any channel is decided
by its Q-value alone. -/
theorem smooth_regimePersists_iff {p : Nuclide}
    (h : nuclearLedgerKind p = .smooth) (q : ℝ)
    (channels : List CollectiveChannel) :
    regimePersists p q channels ↔ NuclearMassAllowed q := by
  simp [regimePersists, h]

/-- **Collective decision rule.** Beyond the frontier, the collective envelope
decides, not the smooth Q-value. -/
theorem collective_regimePersists_iff {p : Nuclide}
    (h : nuclearLedgerKind p = .collective) (q : ℝ)
    (channels : List CollectiveChannel) :
    regimePersists p q channels ↔
      CollectivePersists (certifiedMass p.Z p.N) channels := by
  simp [regimePersists, h]

/-- A named nuclear exit with its Q-value and barrier. -/
structure NuclearExit where
  name : String
  q : ℝ
  barrier : ℝ

def NuclearExit.massAllowed (e : NuclearExit) : Prop :=
  NuclearMassAllowed e.q

/-- `β⁻` exit. -/
def betaMinusExit (p : Nuclide) : NuclearExit :=
  ⟨"beta-", nuclearBetaMinusQ p, 0⟩

/-- `β⁺` exit. -/
def betaPlusExit (p : Nuclide) : NuclearExit :=
  ⟨"beta+", nuclearBetaPlusQ p, 0⟩

/-- Alpha exit. -/
def alphaExit (p : Nuclide) : NuclearExit :=
  ⟨"alpha", nuclearAlphaQ p, shellWeight⟩

/-- Fission exit for two supplied fragments. -/
def fissionExit (p f1 f2 : Nuclide) : NuclearExit :=
  ⟨"fission", nuclearFissionQ p f1 f2, shellWeight⟩

/-- The standard exit table for a parent and a supplied fission split. -/
def nuclearExits (p f1 f2 : Nuclide) : List NuclearExit :=
  [betaMinusExit p, betaPlusExit p, alphaExit p, fissionExit p f1 f2]

theorem nuclearExits_length (p f1 f2 : Nuclide) :
    (nuclearExits p f1 f2).length = 4 := rfl

/-- Convert an exit to the collective-channel form used by the rate layer.
The channel mass is the parent mass minus the Q-value; the barrier is kept
separate. -/
noncomputable def NuclearExit.toChannel (parent : Nuclide) (e : NuclearExit) :
    CollectiveChannel :=
  { mass := certifiedMass parent.Z parent.N - e.q, barrier := e.barrier }

theorem NuclearExit.toChannel_totalMass (parent : Nuclide) (e : NuclearExit) :
    (e.toChannel parent).totalMass =
      certifiedMass parent.Z parent.N - e.q + e.barrier := by
  simp [NuclearExit.toChannel, CollectiveChannel.totalMass]

/-- Collective-channel form of the standard exit table. -/
noncomputable def nuclearExitChannels (p f1 f2 : Nuclide) : List CollectiveChannel :=
  (nuclearExits p f1 f2).map (NuclearExit.toChannel p)

theorem nuclearExitChannels_length (p f1 f2 : Nuclide) :
    (nuclearExitChannels p f1 f2).length = 4 := by
  simp [nuclearExitChannels, nuclearExits]

/-- Cm-244 is decided by the smooth Q-value even when the full exit table is
passed in. -/
theorem cm_exitTable_regimePersists_iff (q : ℝ) (f1 f2 : Nuclide) :
    regimePersists ⟨96, 148⟩ q (nuclearExitChannels ⟨96, 148⟩ f1 f2) ↔
      NuclearMassAllowed q :=
  cm_regimePersists_iff q _

/-- Cf-252 is decided by the collective envelope even when the full exit table
is passed in. -/
theorem cf_exitTable_regimePersists_iff (q : ℝ) (f1 f2 : Nuclide) :
    regimePersists ⟨98, 154⟩ q (nuclearExitChannels ⟨98, 154⟩ f1 f2) ↔
      CollectivePersists (certifiedMass 98 154)
        (nuclearExitChannels ⟨98, 154⟩ f1 f2) :=
  cf_regimePersists_iff q _

/-- Cm-244 alpha exit under the smooth ledger. -/
theorem cm_alpha_regimePersists_iff (f1 f2 : Nuclide) :
    regimePersists ⟨96, 148⟩ (nuclearAlphaQ ⟨96, 148⟩)
        (nuclearExitChannels ⟨96, 148⟩ f1 f2) ↔
      NuclearMassAllowed (nuclearAlphaQ ⟨96, 148⟩) :=
  cm_exitTable_regimePersists_iff _ f1 f2

/-- Cf-252 alpha exit under the collective ledger. -/
theorem cf_alpha_regimePersists_iff (f1 f2 : Nuclide) :
    regimePersists ⟨98, 154⟩ (nuclearAlphaQ ⟨98, 154⟩)
        (nuclearExitChannels ⟨98, 154⟩ f1 f2) ↔
      CollectivePersists (certifiedMass 98 154)
        (nuclearExitChannels ⟨98, 154⟩ f1 f2) :=
  cf_exitTable_regimePersists_iff _ f1 f2

/-- Pb-208 is decided by the smooth Q-value. -/
theorem pb_exitTable_regimePersists_iff (q : ℝ) (f1 f2 : Nuclide) :
    regimePersists ⟨82, 126⟩ q (nuclearExitChannels ⟨82, 126⟩ f1 f2) ↔
      NuclearMassAllowed q := by
  apply smooth_regimePersists_iff
  unfold nuclearLedgerKind
  rw [pb_regime]
  rfl

/-- U-238 is decided by the smooth Q-value inside the certified domain. -/
theorem u_exitTable_regimePersists_iff (q : ℝ) (f1 f2 : Nuclide) :
    regimePersists ⟨92, 146⟩ q (nuclearExitChannels ⟨92, 146⟩ f1 f2) ↔
      NuclearMassAllowed q := by
  apply smooth_regimePersists_iff
  unfold nuclearLedgerKind
  rw [u_regime]
  rfl

/-- E8-native nuclear cost: the certified smooth mass. -/
def e8NuclearCost (p : Nuclide) : ℝ :=
  certifiedMass p.Z p.N

/-- Persistence under the E8 cost ledger. -/
theorem persists_e8NuclearCost_of_no_lower {p : Nuclide}
    (h : ∀ ns ls, Decay p ns ls → ∀ d ∈ ns,
      e8NuclearCost p ≤ e8NuclearCost d) :
    Persists e8NuclearCost p :=
  persists_of_no_lower h

theorem not_persists_e8NuclearCost_of_lower {p d : Nuclide}
    {ns : List Nuclide} {ls : List Lepton}
    (hdec : Decay p ns ls) (hd : d ∈ ns)
    (hcost : e8NuclearCost d < e8NuclearCost p) :
    ¬ Persists e8NuclearCost p :=
  not_persists_of_lower hdec hd hcost

end PMAtoms
