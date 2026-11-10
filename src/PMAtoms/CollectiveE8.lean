import PMAtoms.CollectiveRegime
import PMAtoms.NuclearShells
import PMElementaryParticles.MeanLife
import PMAtoms.E8Tick
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
open PMElementaryParticles PMHadrons

/-- Alpha barrier: one substrate clock period. -/
def alphaBarrier : ℝ := e8Tick
theorem alphaBarrier_eq : alphaBarrier = 43 := by
  unfold alphaBarrier
  rw [e8Tick_eq]

/-- Fission barrier `shellWeight = Δ/(D+χ)`. -/
def fissionBarrier : ℝ := shellWeight
theorem fissionBarrier_eq : fissionBarrier = 43 / 6 := by
  rw [fissionBarrier, shellWeight_eq]

/-- One E8 clock period in `m_e` units. Alias of `e8Tick`. -/
def e8ClockPeriod : ℝ := e8Tick
theorem e8ClockPeriod_eq : e8ClockPeriod = 43 := by
  unfold e8ClockPeriod
  rw [e8Tick_eq]

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


/-! ## Daughter-shell alpha preformation

Each unit of distance from the E8 magic ladder costs half a boundary link
(`σ/2 = 5/2`) in the exponent.  This is the E8 form of the daughter-shell
preformation factor; it is a candidate, not part of `certifiedMass`.
-/

/-- Distance from `a` to the nearest E8 magic number. -/
def magicDistance (a : Nat) : Nat :=
  (nuclearMagic.map (fun m => if m ≤ a then a - m else m - a)).min?.getD 0

/-- Proton gap of the daughter to the magic ladder. -/
def daughterShellGapZ (p : Nuclide) : Nat := magicDistance (p.Z - 2)

/-- Neutron gap of the daughter to the magic ladder. -/
def daughterShellGapN (p : Nuclide) : Nat := magicDistance (p.N - 2)

/-- Euclidean distance to the magic ladder in the `(Z,N)` shell plane. -/
noncomputable def daughterShellDistance (p : Nuclide) : ℝ :=
  Real.sqrt ((daughterShellGapZ p : ℝ) ^ 2 + (daughterShellGapN p : ℝ) ^ 2)

/-- Daughter-shell preformation: `exp(−(σ/2)·d)`. -/
noncomputable def alphaPreformationShell (p : Nuclide) : ℝ :=
  Real.exp (-(((σ : ℝ) / 2) * daughterShellDistance p))

theorem daughterShellGapZ_u238 : daughterShellGapZ ⟨92, 146⟩ = 6 := by decide
theorem daughterShellGapN_u238 : daughterShellGapN ⟨92, 146⟩ = 8 := by decide
theorem daughterShellGapZ_cm244 : daughterShellGapZ ⟨96, 148⟩ = 2 := by decide
theorem daughterShellGapN_cm244 : daughterShellGapN ⟨96, 148⟩ = 6 := by decide
theorem daughterShellGapZ_cf252 : daughterShellGapZ ⟨98, 154⟩ = 0 := by decide
theorem daughterShellGapN_cf252 : daughterShellGapN ⟨98, 154⟩ = 0 := by decide

theorem daughterShellDistance_u238 :
    daughterShellDistance ⟨92, 146⟩ = 10 := by
  unfold daughterShellDistance
  norm_num [daughterShellGapZ_u238, daughterShellGapN_u238]

theorem daughterShellDistance_cm244 :
    daughterShellDistance ⟨96, 148⟩ = Real.sqrt 40 := by
  unfold daughterShellDistance
  norm_num [daughterShellGapZ_cm244, daughterShellGapN_cm244]

theorem daughterShellDistance_cf252 :
    daughterShellDistance ⟨98, 154⟩ = 0 := by
  unfold daughterShellDistance
  norm_num [daughterShellGapZ_cf252, daughterShellGapN_cf252]

/-- The log of the daughter-shell preformation is the boundary cost. -/
theorem log_alphaPreformationShell (p : Nuclide) :
    Real.log (alphaPreformationShell p) =
      -(((σ : ℝ) / 2) * daughterShellDistance p) := by
  unfold alphaPreformationShell
  rw [Real.log_exp]

theorem alphaPreformationShell_pos (p : Nuclide) :
    0 < alphaPreformationShell p := by
  unfold alphaPreformationShell
  positivity

theorem alphaPreformationShell_le_one (p : Nuclide) :
    alphaPreformationShell p ≤ 1 := by
  unfold alphaPreformationShell
  rw [Real.exp_le_one_iff]
  have hσ : (0 : ℝ) ≤ (σ : ℝ) / 2 := by
    norm_num [σ, PMSubstrate.baseline]
  have hd : 0 ≤ daughterShellDistance p := Real.sqrt_nonneg _
  have h : (0 : ℝ) ≤ ((σ : ℝ) / 2) * daughterShellDistance p :=
    mul_nonneg hσ hd
  linarith

/-- Barrier with daughter-shell preformation folded in. -/
noncomputable def alphaBarrierShellPreformed (p : Nuclide) : ℝ :=
  alphaBarrierGeiger p.Z (alphaQ p) +
    (((σ : ℝ) / 2) * daughterShellDistance p)

theorem alphaBarrierShellPreformed_eq_log (p : Nuclide) :
    alphaBarrierShellPreformed p =
      alphaBarrierGeiger p.Z (alphaQ p) - Real.log (alphaPreformationShell p) := by
  rw [log_alphaPreformationShell]
  unfold alphaBarrierShellPreformed
  ring

/-- Alpha channel with daughter-shell preformation. -/
noncomputable def alphaChannelShellPreformed (p : Nuclide) : CollectiveChannel :=
  { mass := nuclearMassPackingShellPaired (p.Z - 2) (p.N - 2) +
      nuclearMassPackingShellPaired 2 2
    barrier := alphaBarrierShellPreformed p }

theorem alphaChannelShellPreformed_totalMass (p : Nuclide) :
    (alphaChannelShellPreformed p).totalMass =
      nuclearMassPackingShellPaired (p.Z - 2) (p.N - 2) +
        nuclearMassPackingShellPaired 2 2 +
          alphaBarrierShellPreformed p := rfl


/-- Closure hindrance: at a magic daughter (`d=0`) all `ν=16` active channels
are blocked; distance `d` opens them as `ν/(d+1)`. -/
noncomputable def daughterClosureHindrance (d : ℝ) : ℝ :=
  Real.exp (-((ν : ℝ) / (d + 1)))

theorem daughterClosureHindrance_pos (d : ℝ) : 0 < daughterClosureHindrance d := by
  unfold daughterClosureHindrance
  positivity

theorem daughterClosureHindrance_le_one (d : ℝ) (hd : 0 ≤ d) :
    daughterClosureHindrance d ≤ 1 := by
  unfold daughterClosureHindrance
  rw [Real.exp_le_one_iff]
  apply neg_nonpos.mpr
  apply div_nonneg
  · positivity
  · linarith

/-- E8 daughter phase space from the closure hindrance. -/
noncomputable def alphaPhaseSpace (p : Nuclide) : ℝ :=
  daughterClosureHindrance (daughterShellDistance p)

theorem alphaPhaseSpace_pos (p : Nuclide) : 0 < alphaPhaseSpace p := by
  unfold alphaPhaseSpace
  exact daughterClosureHindrance_pos _

theorem alphaPhaseSpace_le_one (p : Nuclide) : alphaPhaseSpace p ≤ 1 := by
  unfold alphaPhaseSpace
  apply daughterClosureHindrance_le_one
  exact Real.sqrt_nonneg _

/-- Alpha width with the E8 phase-space factor. -/
noncomputable def alphaWidthE8 (attempt : ℝ) (p : Nuclide) : ℝ :=
  attempt * alphaPreformationShell p * alphaPhaseSpace p *
    Real.exp (-(alphaBarrierGeiger p.Z (alphaQ p)))

theorem alphaWidthE8_pos (attempt : ℝ) (p : Nuclide) (h : 0 < attempt) :
    0 < alphaWidthE8 attempt p := by
  unfold alphaWidthE8
  exact mul_pos
    (mul_pos (mul_pos h (alphaPreformationShell_pos p)) (alphaPhaseSpace_pos p))
    (Real.exp_pos _)

/-- Mean life from the E8 alpha width. -/
noncomputable def alphaMeanLifeE8 (attempt : ℝ) (p : Nuclide) : ℝ :=
  MeanLife (alphaWidthE8 attempt p)

theorem alphaMeanLifeE8_eq (attempt : ℝ) (p : Nuclide) :
    alphaMeanLifeE8 attempt p = 1 / alphaWidthE8 attempt p := rfl

/-- Relative mean life including the E8 phase-space factor. -/
noncomputable def alphaRelativeLifetimeE8 (p ref : Nuclide) : ℝ :=
  Real.exp (alphaBarrierShellPreformed p - alphaBarrierShellPreformed ref) *
    (alphaPhaseSpace ref / alphaPhaseSpace p)

theorem alphaRelativeLifetimeE8_pos (p ref : Nuclide) :
    0 < alphaRelativeLifetimeE8 p ref := by
  unfold alphaRelativeLifetimeE8
  exact mul_pos (Real.exp_pos _)
    (div_pos (alphaPhaseSpace_pos ref) (alphaPhaseSpace_pos p))

end PMAtoms
