import PMAtoms.CollectiveRegime
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.


# E8 barrier scales for collective channels

Two E8 barrier scales are used:

* alpha: one clock period `Δ = 43 m_e`
* fission: the shell weight `Δ/(D+χ) = 43/6 m_e`

The absolute time unit / attempt frequency is still an open E8 input; these are
barrier energies in `m_e` units.
-/

noncomputable section
namespace PMAtoms

/-- Alpha barrier `Δ`. -/
def alphaBarrier : ℝ := (Δ : ℝ)
theorem alphaBarrier_eq : alphaBarrier = 43 := by
  norm_num [alphaBarrier, Δ, PMSubstrate.baseline]

/-- Fission barrier `shellWeight = Δ/(D+χ)`. -/
def fissionBarrier : ℝ := shellWeight
theorem fissionBarrier_eq : fissionBarrier = 43 / 6 := by
  rw [fissionBarrier, shellWeight_eq]

/-- One E8 clock period in `m_e` units. -/
def e8ClockPeriod : ℝ := (Δ : ℝ)
theorem e8ClockPeriod_eq : e8ClockPeriod = 43 := by
  norm_num [e8ClockPeriod, Δ, PMSubstrate.baseline]

/-- Alpha channel with the E8 `Δ` barrier. -/
noncomputable def alphaChannelE8 (p : Nuclide) : CollectiveChannel :=
  { mass := nuclearMassPackingShellPaired (p.Z - 2) (p.N - 2) +
      nuclearMassPackingShellPaired 2 2
    barrier := alphaBarrier }

/-- Fission channel with the E8 shell-weight barrier. -/
noncomputable def fissionChannelE8 (_p f1 f2 : Nuclide) : CollectiveChannel :=
  { mass := nuclearMassPackingShellPaired f1.Z f1.N +
      nuclearMassPackingShellPaired f2.Z f2.N
    barrier := fissionBarrier }

theorem alphaChannelE8_totalMass (p : Nuclide) :
    (alphaChannelE8 p).totalMass =
      nuclearMassPackingShellPaired (p.Z - 2) (p.N - 2) +
        nuclearMassPackingShellPaired 2 2 + alphaBarrier := rfl

theorem fissionChannelE8_totalMass (p f1 f2 : Nuclide) :
    (fissionChannelE8 p f1 f2).totalMass =
      nuclearMassPackingShellPaired f1.Z f1.N +
        nuclearMassPackingShellPaired f2.Z f2.N + fissionBarrier := rfl


/-- Coulomb-corrected alpha barrier:
`alphaClosureWeight · Z / (σ · A^(1/3))`. -/
noncomputable def alphaBarrierCoulomb (z a : Nat) : ℝ :=
  alphaClosureWeight * (z : ℝ) /
    ((σ : ℝ) * (a : ℝ) ^ ((1 : ℝ) / 3))

/-- Alpha channel with the Coulomb-corrected E8 barrier. -/
noncomputable def alphaChannelCoulomb (p : Nuclide) : CollectiveChannel :=
  { mass := nuclearMassPackingShellPaired (p.Z - 2) (p.N - 2) +
      nuclearMassPackingShellPaired 2 2
    barrier := alphaBarrierCoulomb p.Z (p.Z + p.N) }

theorem alphaChannelCoulomb_totalMass (p : Nuclide) :
    (alphaChannelCoulomb p).totalMass =
      nuclearMassPackingShellPaired (p.Z - 2) (p.N - 2) +
        nuclearMassPackingShellPaired 2 2 +
          alphaBarrierCoulomb p.Z (p.Z + p.N) := rfl


/-- Geiger–Nuttall barrier exponent from the alpha test:
`(Δ/(ν−χ)) · Z / √Q`. -/
noncomputable def alphaBarrierGeiger (z : Nat) (q : ℝ) : ℝ :=
  ((Δ : ℝ) / (((ν - χ : Nat)) : ℝ)) * (z : ℝ) / Real.sqrt q

theorem alphaBarrierGeiger_eq (z : Nat) (q : ℝ) :
    alphaBarrierGeiger z q = (43 / 14 : ℝ) * (z : ℝ) / Real.sqrt q := by
  unfold alphaBarrierGeiger
  norm_num [Δ, ν, χ, PMSubstrate.baseline]

/-- Alpha energy release from the smooth ledger, in `m_e` units. -/
noncomputable def alphaQ (p : Nuclide) : ℝ :=
  nuclearMassPackingShellPaired p.Z p.N -
    nuclearMassPackingShellPaired (p.Z - 2) (p.N - 2) -
      nuclearMassPackingShellPaired 2 2

/-- Alpha channel with the Geiger–Nuttall E8 barrier. -/
noncomputable def alphaChannelGeiger (p : Nuclide) : CollectiveChannel :=
  { mass := nuclearMassPackingShellPaired (p.Z - 2) (p.N - 2) +
      nuclearMassPackingShellPaired 2 2
    barrier := alphaBarrierGeiger p.Z (alphaQ p) }

end PMAtoms
