import PMAtoms.BetaCalibration
import PMAtoms.BetaLattice
import PMAtoms.NuclearPacking3D
import PMAtoms.Invariants
import PMAtoms.AlphaPersistence
import PMSubstrate.E8Margin
import PMElementaryParticles.CompositeMasses
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.

# Neutron beta prediction from the minimal E8 cube

The minimal volume-persistent cube is `3×3×3` (`cube_interior_iff`).  The
neutron Q-window fixes the spectral cutoff between the lowest and second mode,
so only the lowest mode is open.  The spectral fraction is then the finite
Boltzmann weight ratio, and the lifetime follows from `betaHazardE8`.
-/

noncomputable section
namespace PMAtoms

/-- Minimal volume-persistent cube. -/
def neutronCube : Nat := 3

/-- Neutron cutoff in `m_e` units, near the endpoint `m_n − m_p`. -/
def neutronCutoff : ℝ := 253 / 100

theorem neutronCube_minimal : ¬ (∃ v, cubeInterior 2 v) := by
  rw [cube_interior_iff]
  norm_num

/-- Finite spectral fraction for the minimal cube and neutron cutoff. -/
def neutronSpectralFraction : ℝ :=
  betaSpectralRateCutoff 1 1 neutronCube neutronCutoff

theorem neutronSpectralFraction_eq :
    neutronSpectralFraction =
      betaSpectralRate 1 1 neutronCube
        (betaOpenModes neutronCube neutronCutoff) := rfl

/-- Candidate neutron lifetime from the E8 hazard and finite spectral fraction. -/
def neutronLifetimeE8 : ℝ :=
  betaLifetimeFromFraction betaHazardE8 neutronSpectralFraction

theorem neutronLifetimeE8_eq :
    neutronLifetimeE8 = 1 / (betaHazardE8 * neutronSpectralFraction) := rfl

theorem neutronLifetimeE8_pos (hf : 0 < neutronSpectralFraction) :
    0 < neutronLifetimeE8 :=
  betaLifetimeFromFraction_pos betaHazardE8_pos hf

/-- Exact neutron endpoint `m_n − m_p` in `m_e` units. -/
noncomputable def neutronCutoffExact : ℝ :=
  PMElementaryParticles.CompositeMasses.neutron -
    PMElementaryParticles.CompositeMasses.proton

/-- Exact-cutoff spectral fraction; the open set automatically includes any
higher mode that crosses the cutoff. -/
noncomputable def neutronSpectralFractionExact : ℝ :=
  betaSpectralRateCutoff 1 1 neutronCube neutronCutoffExact

/-- Exact-cutoff lifetime. -/
noncomputable def neutronLifetimeExactCutoff : ℝ :=
  betaLifetimeFromFraction betaHazardE8 neutronSpectralFractionExact

/-- E8 margin factor `1 − χ/Δ = 41/43`. -/
def neutronMarginFactor : ℝ :=
  (((Δ - χ : Nat)) : ℝ) / (Δ : ℝ)

theorem neutronMarginFactor_eq : neutronMarginFactor = 41 / 43 := by
  unfold neutronMarginFactor
  norm_num [Δ, χ, PMSubstrate.baseline]

theorem neutronMarginFactor_pos : 0 < neutronMarginFactor := by
  rw [neutronMarginFactor_eq]; norm_num

/-- Margin-corrected endpoint prediction. -/
def neutronLifetimeCorrected : ℝ :=
  neutronMarginFactor * neutronLifetimeExactCutoff

theorem neutronLifetimeCorrected_eq :
    neutronLifetimeCorrected =
      neutronMarginFactor * neutronLifetimeExactCutoff := rfl

/-- The boundary gap `χ=2` leaves `Δ−χ=41` surviving clock phases. -/
theorem neutronMargin_survivingPhases :
    (survivingPhases χ).card = 41 := by
  rw [survivingPhases_card χ (by norm_num [χ, Δ, PMSubstrate.baseline])]
  norm_num [χ, Δ, PMSubstrate.baseline]

/-- The margin is the surviving-phase fraction after a boundary gap `χ`. -/
theorem neutronMarginFactor_eq_phaseFraction :
    neutronMarginFactor = alphaPhaseFraction χ := by
  rw [neutronMarginFactor_eq]
  rw [alphaPhaseFraction_eq χ (by norm_num [χ, Δ, PMSubstrate.baseline])]
  norm_num [χ, Δ, PMSubstrate.baseline]

theorem neutronMarginFactor_eq_substrate :
    neutronMarginFactor = PMSubstrate.E8Margin.phaseMargin := by
  rw [neutronMarginFactor_eq, PMSubstrate.E8Margin.phaseMargin_eq]


/-- The lowest `3×3×3` Dirichlet eigenvalue is `6 − 3√2`. -/
lemma neutron_low_eigenvalue_eq :
    dirichletEigenvalue 3 1 1 1 = 6 - 3 * Real.sqrt 2 := by
  unfold dirichletEigenvalue
  rw [show Real.pi * ((1 : Nat) : ℝ) / (((3 : Nat) : ℝ) + 1) = Real.pi / 4 by ring]
  rw [Real.cos_pi_div_four]
  ring

/-- The next `3×3×3` Dirichlet eigenvalue is `6 − 2√2`. -/
lemma neutron_next_eigenvalue_eq :
    dirichletEigenvalue 3 2 1 1 = 6 - 2 * Real.sqrt 2 := by
  unfold dirichletEigenvalue
  rw [show Real.pi * ((2 : Nat) : ℝ) / (((3 : Nat) : ℝ) + 1) = Real.pi / 2 by ring,
    Real.cos_pi_div_two]
  rw [show Real.pi * ((1 : Nat) : ℝ) / (((3 : Nat) : ℝ) + 1) = Real.pi / 4 by ring,
    Real.cos_pi_div_four]
  ring

lemma neutron_low_eigenvalue_le :
    dirichletEigenvalue 3 1 1 1 ≤ neutronCutoff := by
  rw [neutron_low_eigenvalue_eq]
  have hs : (1.16 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  unfold neutronCutoff
  nlinarith

lemma neutron_next_eigenvalue_gt :
    neutronCutoff < dirichletEigenvalue 3 2 1 1 := by
  rw [neutron_next_eigenvalue_eq]
  have hs : Real.sqrt 2 < (1.735 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  unfold neutronCutoff
  nlinarith

/-- At the neutron cutoff exactly the lowest `3×3×3` mode is open. -/
theorem neutron_openModes :
    betaOpenModes neutronCube neutronCutoff =
      {(⟨0, by decide⟩, (⟨0, by decide⟩, ⟨0, by decide⟩))} := by
  unfold neutronCube
  exact betaOpenModes_eq_singleton_of_gap (n := 3) (by norm_num)
    neutron_low_eigenvalue_le neutron_next_eigenvalue_gt

/-- The finite neutron spectral fraction is the lowest Boltzmann weight
divided by the total `3×3×3` weight. -/
theorem neutronSpectralFraction_eq_lowest_weight :
    neutronSpectralFraction =
      betaSpectralWeight 3 1 1 1 /
        ∑ p : Fin 3 × (Fin 3 × Fin 3),
          betaSpectralWeight 3 (p.1.val + 1) (p.2.1.val + 1) (p.2.2.val + 1) := by
  unfold neutronSpectralFraction neutronCube betaSpectralRateCutoff betaSpectralRate
    betaWeightedRate
  rw [show betaOpenModes 3 neutronCutoff =
    {(⟨0, by omega⟩, (⟨0, by omega⟩, ⟨0, by omega⟩))} from neutron_openModes]
  simp [betaSpectralWeight]

/-- Crude certified bounds: the fraction lies between `1/27` and `1`. -/
theorem neutronSpectralFraction_bounds :
    (1 / 27 : ℝ) ≤ neutronSpectralFraction ∧ neutronSpectralFraction ≤ 1 := by
  rw [neutronSpectralFraction_eq_lowest_weight]
  set w : Fin 3 × (Fin 3 × Fin 3) → ℝ :=
    fun p => betaSpectralWeight 3 (p.1.val + 1) (p.2.1.val + 1) (p.2.2.val + 1) with hwdef
  have hwpos : ∀ p, 0 < w p := by
    intro p
    unfold w
    exact betaSpectralWeight_pos 3 _ _ _
  have htotal : 0 < ∑ p, w p := by
    apply Finset.sum_pos
    · intro p _; exact hwpos p
    · exact Finset.univ_nonempty
  have hwle : ∀ p, w p ≤ w (⟨0, by norm_num⟩, (⟨0, by norm_num⟩, ⟨0, by norm_num⟩)) := by
    intro p
    unfold w
    apply Real.exp_le_exp.mpr
    have h := dirichletEigenvalue_lowest_le (n := 3) (by norm_num)
      (a := p.1.val + 1) (b := p.2.1.val + 1) (c := p.2.2.val + 1)
      (Nat.succ_pos _) (Nat.succ_le_of_lt p.1.isLt)
      (Nat.succ_pos _) (Nat.succ_le_of_lt p.2.1.isLt)
      (Nat.succ_pos _) (Nat.succ_le_of_lt p.2.2.isLt)
    linarith
  have hsum_le : ∑ p, w p ≤
      27 * w (⟨0, by norm_num⟩, (⟨0, by norm_num⟩, ⟨0, by norm_num⟩)) := by
    calc
      ∑ p, w p ≤ ∑ _p : Fin 3 × (Fin 3 × Fin 3),
          w (⟨0, by norm_num⟩, (⟨0, by norm_num⟩, ⟨0, by norm_num⟩)) := by
        apply Finset.sum_le_sum
        intro p _
        exact hwle p
      _ = 27 * w (⟨0, by norm_num⟩, (⟨0, by norm_num⟩, ⟨0, by norm_num⟩)) := by
        simp [Finset.card_univ, Fintype.card_prod]
  constructor
  · rw [le_div_iff₀ htotal]
    nlinarith
  · rw [div_le_one htotal]
    have hsingle : w (⟨0, by norm_num⟩, (⟨0, by norm_num⟩, ⟨0, by norm_num⟩)) ≤ ∑ p, w p := by
      have h := Finset.sum_le_sum_of_subset_of_nonneg
        (s := {(⟨0, by norm_num⟩, (⟨0, by norm_num⟩, ⟨0, by norm_num⟩))})
        (t := Finset.univ) (f := w)
        (by intro x hx; simp)
        (by intro x _ _; exact le_of_lt (hwpos x))
      simpa using h
    exact hsingle

theorem neutronSpectralFraction_pos : 0 < neutronSpectralFraction :=
  lt_of_lt_of_le (by norm_num) neutronSpectralFraction_bounds.1


end PMAtoms
