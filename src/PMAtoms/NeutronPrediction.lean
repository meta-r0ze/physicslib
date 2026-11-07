import PMAtoms.BetaCalibration
import PMAtoms.BetaLattice
import PMAtoms.NuclearPacking3D
import PMAtoms.Invariants
import PMAtoms.AlphaPersistence
import PMSubstrate.E8Margin
import PMElementaryParticles.CompositeMasses
import PMElementaryParticles.PhysicalUnits
import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds

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

/-- The gap `√2` gives the sharper lower bound `1/14` for the neutron fraction. -/
lemma exp_neg_sqrt_two_le_half : Real.exp (-Real.sqrt 2) ≤ (1 / 2 : ℝ) := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hmono : Real.exp (-Real.sqrt 2) ≤ Real.exp (-1 : ℝ) := by
    apply Real.exp_le_exp.mpr
    linarith
  have h2 : (2 : ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_two
  have hinv : Real.exp (-1 : ℝ) ≤ (1 / 2 : ℝ) := by
    rw [Real.exp_neg]
    simpa [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) h2)
  linarith

/-- A degree-10 Taylor lower bound for `exp x` gives a sharp `exp(-√2)` upper bound. -/
lemma exp_neg_le_inv_taylor10 {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤
      1 / ((Finset.range 11).sum (fun i => x ^ i / (i.factorial : ℝ))) := by
  have hsum : (0 : ℝ) < (Finset.range 11).sum (fun i => x ^ i / (i.factorial : ℝ)) := by
    have hnonneg : ∀ i ∈ Finset.range 11, 0 ≤ x ^ i / (i.factorial : ℝ) := by
      intro i hi
      positivity
    have h1 : 1 ∈ Finset.range 11 := by norm_num
    have hxpos : (0 : ℝ) < x ^ 1 / ((1 : ℕ).factorial : ℝ) := by simpa using hx
    exact lt_of_lt_of_le hxpos (Finset.single_le_sum hnonneg h1)
  have h := Real.sum_le_exp_of_nonneg (le_of_lt hx) 11
  rw [Real.exp_neg]
  simpa using one_div_le_one_div_of_le hsum h

lemma exp_neg_sqrt_two_le_0244 : Real.exp (-Real.sqrt 2) ≤ (0.2442 : ℝ) := by
  have hs : (1.41 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hmono : Real.exp (-Real.sqrt 2) ≤ Real.exp (-1.41 : ℝ) := by
    apply Real.exp_le_exp.mpr
    linarith
  have ht := exp_neg_le_inv_taylor10 (x := 1.41) (by norm_num)
  have hconst : 1 / ((Finset.range 11).sum (fun i => (1.41 : ℝ) ^ i / (i.factorial : ℝ))) ≤
      (0.2442 : ℝ) := by norm_num
  exact hmono.trans (ht.trans hconst)

/-- Exact `3×3×3` eigenvalue gap is `√2` times the sum of index excesses. -/
lemma dirichletTerm_three (a : Nat) (ha1 : 1 ≤ a) (ha3 : a ≤ 3) :
    2 - 2 * Real.cos (Real.pi * (a : ℝ) / (((3 : Nat) : ℝ) + 1)) =
      (2 - Real.sqrt 2) + Real.sqrt 2 * ((a : ℝ) - 1) := by
  interval_cases a
  · rw [show Real.pi * ((1 : Nat) : ℝ) / (((3 : Nat) : ℝ) + 1) = Real.pi / 4 by ring,
      Real.cos_pi_div_four]
    ring
  · rw [show Real.pi * ((2 : Nat) : ℝ) / (((3 : Nat) : ℝ) + 1) = Real.pi / 2 by ring,
      Real.cos_pi_div_two]
    norm_num
  · rw [show Real.pi * ((3 : Nat) : ℝ) / (((3 : Nat) : ℝ) + 1) = Real.pi - Real.pi / 4 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_four]
    ring

lemma dirichletEigenvalue_three_eq_low_add (a b c : Nat)
    (ha1 : 1 ≤ a) (ha3 : a ≤ 3) (hb1 : 1 ≤ b) (hb3 : b ≤ 3)
    (hc1 : 1 ≤ c) (hc3 : c ≤ 3) :
    dirichletEigenvalue 3 a b c =
      dirichletEigenvalue 3 1 1 1 + Real.sqrt 2 * ((a : ℝ) + b + c - 3) := by
  have h1 := dirichletTerm_three a ha1 ha3
  have h2 := dirichletTerm_three b hb1 hb3
  have h3 := dirichletTerm_three c hc1 hc3
  have hlow := dirichletTerm_three 1 (by norm_num) (by norm_num)
  unfold dirichletEigenvalue
  nlinarith [h1, h2, h3, hlow]

/-- Weight of a `3×3×3` mode: sum of the three index excesses. -/
def neutronModeWeight (p : Fin 3 × (Fin 3 × Fin 3)) : Fin 7 :=
  ⟨p.1.val + p.2.1.val + p.2.2.val, by
    have h1 := p.1.isLt
    have h2 := p.2.1.isLt
    have h3 := p.2.2.isLt
    omega⟩

/-- Number of modes at each weight `0..6`. -/
def neutronWeightCount (s : Nat) : Nat :=
  match s with
  | 0 => 1
  | 1 => 3
  | 2 => 6
  | 3 => 7
  | 4 => 6
  | 5 => 3
  | 6 => 1
  | _ => 0

lemma neutronModeWeight_card (s : Fin 7) :
    (Finset.univ.filter (fun p : Fin 3 × (Fin 3 × Fin 3) =>
      neutronModeWeight p = s)).card = neutronWeightCount s.val := by
  fin_cases s <;> decide

lemma dirichletEigenvalue_three_mode_eq (p : Fin 3 × (Fin 3 × Fin 3)) :
    dirichletEigenvalue 3 (p.1.val + 1) (p.2.1.val + 1) (p.2.2.val + 1) =
      dirichletEigenvalue 3 1 1 1 + Real.sqrt 2 * ((neutronModeWeight p).val : ℝ) := by
  have h := dirichletEigenvalue_three_eq_low_add (p.1.val + 1) (p.2.1.val + 1) (p.2.2.val + 1)
    (Nat.succ_pos _) (Nat.succ_le_of_lt p.1.isLt)
    (Nat.succ_pos _) (Nat.succ_le_of_lt p.2.1.isLt)
    (Nat.succ_pos _) (Nat.succ_le_of_lt p.2.2.isLt)
  rw [h]
  congr 1
  simp [neutronModeWeight]
  ring

lemma neutron_weight_sum_eq (r : ℝ) :
    (∑ p : Fin 3 × (Fin 3 × Fin 3), r ^ (neutronModeWeight p).val) =
      ∑ s : Fin 7, (neutronWeightCount s.val : ℝ) * r ^ s.val := by
  have hfiber := Finset.sum_fiberwise
    (s := (Finset.univ : Finset (Fin 3 × (Fin 3 × Fin 3))))
    (g := neutronModeWeight) (f := fun p => r ^ (neutronModeWeight p).val)
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro s hs
  rw [show (∑ i with neutronModeWeight i = s, r ^ (neutronModeWeight i).val) =
      ∑ i with neutronModeWeight i = s, r ^ s.val by
    apply Finset.sum_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]]
  rw [Finset.sum_const, nsmul_eq_mul, neutronModeWeight_card]

/-- Sharper certified bound using the first spectral gap `√2`. -/
theorem neutronSpectralFraction_bounds_refined :
    (0.136 : ℝ) ≤ neutronSpectralFraction ∧ neutronSpectralFraction ≤ 1 := by
  rw [neutronSpectralFraction_eq_lowest_weight]
  let low : Fin 3 × (Fin 3 × Fin 3) :=
    (⟨0, by norm_num⟩, (⟨0, by norm_num⟩, ⟨0, by norm_num⟩))
  set w : Fin 3 × (Fin 3 × Fin 3) → ℝ :=
    fun p => betaSpectralWeight 3 (p.1.val + 1) (p.2.1.val + 1) (p.2.2.val + 1) with hwdef
  have hwpos : ∀ p, 0 < w p := by
    intro p; unfold w; exact betaSpectralWeight_pos 3 _ _ _
  have hwle : ∀ p, p ≠ low → w p ≤ w low * 0.2442 := by
    intro p hpne
    have hdisj : p.1.val + 1 ≠ 1 ∨ p.2.1.val + 1 ≠ 1 ∨ p.2.2.val + 1 ≠ 1 := by
      by_contra h
      push Not at h
      apply hpne
      ext <;> norm_num
      all_goals omega
    have hge := dirichletEigenvalue_ge_next (n := 3) (by norm_num)
      (a := p.1.val + 1) (b := p.2.1.val + 1) (c := p.2.2.val + 1)
      (Nat.succ_pos _) (Nat.succ_le_of_lt p.1.isLt)
      (Nat.succ_pos _) (Nat.succ_le_of_lt p.2.1.isLt)
      (Nat.succ_pos _) (Nat.succ_le_of_lt p.2.2.isLt) hdisj
    have hnext : dirichletEigenvalue 3 2 1 1 =
        dirichletEigenvalue 3 1 1 1 + Real.sqrt 2 := by
      rw [neutron_next_eigenvalue_eq, neutron_low_eigenvalue_eq]
      ring
    have harg : -dirichletEigenvalue 3 (p.1.val + 1) (p.2.1.val + 1) (p.2.2.val + 1)
        ≤ -dirichletEigenvalue 3 1 1 1 - Real.sqrt 2 := by
      linarith [hge, hnext]
    calc
      w p = Real.exp (-dirichletEigenvalue 3 (p.1.val + 1) (p.2.1.val + 1) (p.2.2.val + 1)) := rfl
      _ ≤ Real.exp (-dirichletEigenvalue 3 1 1 1 - Real.sqrt 2) :=
        Real.exp_le_exp.mpr harg
      _ = Real.exp (-dirichletEigenvalue 3 1 1 1) * Real.exp (-Real.sqrt 2) := by
        rw [← Real.exp_add]
        ring_nf
      _ ≤ Real.exp (-dirichletEigenvalue 3 1 1 1) * 0.2442 := by
        exact mul_le_mul_of_nonneg_left exp_neg_sqrt_two_le_0244
          (le_of_lt (Real.exp_pos _))
      _ = w low * 0.2442 := by
        simp [w, low, betaSpectralWeight]
  have hrest : (Finset.univ.erase low).sum w ≤ 26 * (w low * 0.2442) := by
    calc
      (Finset.univ.erase low).sum w ≤
          (Finset.univ.erase low).sum (fun _ => w low * 0.2442) := by
        apply Finset.sum_le_sum
        intro p hp
        exact hwle p (Finset.mem_erase.mp hp).1
      _ = (Finset.univ.erase low).card * (w low * 0.2442) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ = 26 * (w low * 0.2442) := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ low)]
        simp [Fintype.card_prod]
  have htotal_eq : ∑ p, w p = w low + (Finset.univ.erase low).sum w := by
    have h := Finset.sum_erase_add (s := Finset.univ) (f := w) (a := low) (Finset.mem_univ low)
    linarith
  have htotal_le : ∑ p, w p ≤ 7.35 * w low := by
    have hwlowpos : 0 < w low := hwpos low
    nlinarith [hrest, htotal_eq, hwlowpos]
  have htotal_pos : 0 < ∑ p, w p := by
    apply Finset.sum_pos
    · intro p _; exact hwpos p
    · exact Finset.univ_nonempty
  constructor
  · rw [le_div_iff₀ htotal_pos]
    nlinarith [htotal_le]
  · rw [div_le_one htotal_pos]
    have hsingle : w low ≤ ∑ p, w p := by
      have h := Finset.sum_le_sum_of_subset_of_nonneg
        (s := {low}) (t := Finset.univ) (f := w)
        (by intro x hx; simp)
        (by intro x _ _; exact le_of_lt (hwpos x))
      simpa using h
    exact hsingle

theorem neutronSpectralFraction_pos : 0 < neutronSpectralFraction :=
  lt_of_lt_of_le (by norm_num) neutronSpectralFraction_bounds.1

/-- Sharper bound from the exact mode-weight decomposition. -/
theorem neutronSpectralFraction_bounds_weighted :
    (0.45 : ℝ) ≤ neutronSpectralFraction ∧ neutronSpectralFraction ≤ 1 := by
  rw [neutronSpectralFraction_eq_lowest_weight]
  let low : Fin 3 × (Fin 3 × Fin 3) :=
    (⟨0, by norm_num⟩, (⟨0, by norm_num⟩, ⟨0, by norm_num⟩))
  set w : Fin 3 × (Fin 3 × Fin 3) → ℝ :=
    fun p => betaSpectralWeight 3 (p.1.val + 1) (p.2.1.val + 1) (p.2.2.val + 1) with hwdef
  let r : ℝ := Real.exp (-Real.sqrt 2)
  have hwpos : ∀ p, 0 < w p := by
    intro p; unfold w; exact betaSpectralWeight_pos 3 _ _ _
  have hw_eq : ∀ p, w p = w low * r ^ (neutronModeWeight p).val := by
    intro p
    have hlam := dirichletEigenvalue_three_mode_eq p
    calc
      w p = Real.exp (-dirichletEigenvalue 3 (p.1.val + 1) (p.2.1.val + 1) (p.2.2.val + 1)) := rfl
      _ = Real.exp (-(dirichletEigenvalue 3 1 1 1 +
          Real.sqrt 2 * ((neutronModeWeight p).val : ℝ))) := by rw [hlam]
      _ = Real.exp (-dirichletEigenvalue 3 1 1 1) *
          Real.exp (-(Real.sqrt 2 * ((neutronModeWeight p).val : ℝ))) := by
        rw [← Real.exp_add]
        ring_nf
      _ = Real.exp (-dirichletEigenvalue 3 1 1 1) *
          Real.exp (-Real.sqrt 2) ^ (neutronModeWeight p).val := by
        congr 1
        rw [show -(Real.sqrt 2 * ((neutronModeWeight p).val : ℝ)) =
            ((neutronModeWeight p).val : ℝ) * (-Real.sqrt 2) by ring,
          Real.exp_nat_mul]
      _ = w low * r ^ (neutronModeWeight p).val := by
        simp [w, low, r, betaSpectralWeight]
  have htotal_eq : ∑ p, w p = w low * ∑ p, r ^ (neutronModeWeight p).val := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hw_eq p]
  have hr0 : 0 ≤ r := le_of_lt (Real.exp_pos _)
  have hrle : r ≤ (0.2442 : ℝ) := exp_neg_sqrt_two_le_0244
  have hsum_le : (∑ p : Fin 3 × (Fin 3 × Fin 3), r ^ (neutronModeWeight p).val) ≤
      (2.217 : ℝ) := by
    rw [neutron_weight_sum_eq]
    calc
      ∑ s : Fin 7, (neutronWeightCount s.val : ℝ) * r ^ s.val ≤
          ∑ s : Fin 7, (neutronWeightCount s.val : ℝ) * (0.2442 : ℝ) ^ s.val := by
        apply Finset.sum_le_sum
        intro s hs
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hrle _) (by positivity)
      _ ≤ (2.217 : ℝ) := by
        simp [Fin.sum_univ_succ, neutronWeightCount]
        norm_num
  have htotal_le : ∑ p, w p ≤ 2.217 * w low := by
    rw [htotal_eq]
    have hwlowpos : 0 < w low := hwpos low
    nlinarith [hsum_le, hwlowpos]
  have htotal_pos : 0 < ∑ p, w p := by
    apply Finset.sum_pos
    · intro p _; exact hwpos p
    · exact Finset.univ_nonempty
  constructor
  · rw [le_div_iff₀ htotal_pos]
    nlinarith [htotal_le]
  · rw [div_le_one htotal_pos]
    have hsingle : w low ≤ ∑ p, w p := by
      have h := Finset.sum_le_sum_of_subset_of_nonneg
        (s := {low}) (t := Finset.univ) (f := w)
        (by intro x hx; simp)
        (by intro x _ _; exact le_of_lt (hwpos x))
      simpa using h
    exact hsingle

/-- Broad certified enclosure of the finite-channel neutron lifetime. -/
theorem neutronLifetimeE8_bounds :
    (2.9e23 : ℝ) < neutronLifetimeE8 ∧ neutronLifetimeE8 < 8.0e23 := by
  have hz := betaHazardE8_bounds
  have hf := neutronSpectralFraction_bounds_weighted
  have hzpos : 0 < betaHazardE8 := lt_trans (by norm_num) hz.1
  have hfpos : 0 < neutronSpectralFraction := neutronSpectralFraction_pos
  have hden_pos : 0 < betaHazardE8 * neutronSpectralFraction := mul_pos hzpos hfpos
  have hden_lo : (2.8e-24 : ℝ) * 0.45 <
      betaHazardE8 * neutronSpectralFraction := by
    exact mul_lt_mul hz.1 hf.1 (by norm_num) (le_of_lt hzpos)
  have hden_hi : betaHazardE8 * neutronSpectralFraction < (3.42e-24 : ℝ) * 1 := by
    exact mul_lt_mul hz.2 hf.2 hfpos (by norm_num)
  have hlo_pos : (0 : ℝ) < (2.8e-24 : ℝ) * 0.45 := by norm_num
  have hhi_pos : (0 : ℝ) < (3.42e-24 : ℝ) * 1 := by norm_num
  have hlow : 1 / ((3.42e-24 : ℝ) * 1) <
      1 / (betaHazardE8 * neutronSpectralFraction) :=
    one_div_lt_one_div_of_lt hden_pos hden_hi
  have hhigh : 1 / (betaHazardE8 * neutronSpectralFraction) <
      1 / ((2.8e-24 : ℝ) * 0.45) :=
    one_div_lt_one_div_of_lt hlo_pos hden_lo
  rw [neutronLifetimeE8_eq]
  constructor <;> nlinarith [hlow, hhigh]

/-- Finite-channel neutron lifetime in seconds. -/
def neutronLifetimeSeconds : ℝ :=
  neutronLifetimeE8 * PMElementaryParticles.PhysicalUnits.electronTime

/-- Broad certified enclosure of the finite-channel neutron lifetime in seconds. -/
theorem neutronLifetimeSeconds_bounds :
    (3.7e2 : ℝ) < neutronLifetimeSeconds ∧ neutronLifetimeSeconds < 1.04e3 := by
  have hn := neutronLifetimeE8_bounds
  have he := PMElementaryParticles.PhysicalUnits.electronTime_bounds
  have hnpos : (0 : ℝ) < neutronLifetimeE8 := lt_trans (by norm_num) hn.1
  have hepos : (0 : ℝ) < PMElementaryParticles.PhysicalUnits.electronTime :=
    lt_trans (by norm_num) he.1
  have hprodlo := mul_lt_mul'' hn.1 he.1 (by norm_num) (by norm_num)
  have hprodhi := mul_lt_mul'' hn.2 he.2 (le_of_lt hnpos) (le_of_lt hepos)
  unfold neutronLifetimeSeconds
  constructor <;> nlinarith [hprodlo, hprodhi]


end PMAtoms
