import PMAtoms.TwoLedger
import PMAtoms.E8AtomValues
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.


# Quadrupole deformation and pairing: exploratory scaffold

The heavy Cm/Cf residual is even-even and localized near the actinide deformed
region.  The chemistry analogy is Jahn–Teller / Peierls: a degenerate open shell
lowers its energy by distorting.

E8 naturally supplies the two order parameters:

* quadrupole deformation has `σ = 5` components,
* pairing has `χ = 2` time-reversed components.

This module records the counts and a candidate negative deformation energy.
It does **not** add a term to the mass ledger yet.
-/

noncomputable section
namespace PMAtoms
open PMElementaryParticles PMHadrons

/-- The five quadrupole components. -/
structure Quadrupole where
  q20 : ℝ
  q21 : ℝ
  q2m1 : ℝ
  q22 : ℝ
  q2m2 : ℝ

/-- Quadrupole deformation has `σ = 5` independent components. -/
def quadrupoleComponents : Nat := σ

theorem quadrupoleComponents_eq_sigma : quadrupoleComponents = σ := rfl
theorem quadrupoleComponents_eq : quadrupoleComponents = 5 := by
  norm_num [quadrupoleComponents, σ, PMSubstrate.baseline]

/-- Pairing uses `χ = 2` time-reversed channels. -/
def pairingComponents : Nat := χ

theorem pairingComponents_eq : pairingComponents = 2 := by
  norm_num [pairingComponents, χ, PMSubstrate.baseline]

/-- Candidate Jahn–Teller deformation energy: a negative quadratic in the
quadrupole components. -/
def deformationEnergy (g : ℝ) (q : Quadrupole) : ℝ :=
  -g * (q.q20 ^ 2 + q.q21 ^ 2 + q.q2m1 ^ 2 + q.q22 ^ 2 + q.q2m2 ^ 2)

theorem deformationEnergy_nonpos {g : ℝ} (hg : 0 ≤ g) (q : Quadrupole) :
    deformationEnergy g q ≤ 0 := by
  unfold deformationEnergy
  have h : 0 ≤ q.q20 ^ 2 + q.q21 ^ 2 + q.q2m1 ^ 2 + q.q22 ^ 2 + q.q2m2 ^ 2 := by
    positivity
  nlinarith


/-- Protons in the `82–126` valence shell. -/
def protonValence (z : Nat) : Nat :=
  if protonShell < z then z - protonShell else 0

/-- Neutrons in the `126–184` valence shell. -/
def neutronValence (n : Nat) : Nat :=
  if neutronShell < n then n - neutronShell else 0

/-- Standard deformation proxy `N_p N_n`. -/
def valenceProduct (z n : Nat) : Nat := protonValence z * neutronValence n

/-- Candidate E8 deformation weight `shellWeight/(Δ+σ) = 43/288`. -/
def deformationWeight : ℝ := shellWeight / ((Δ : ℝ) + (σ : ℝ))

theorem deformationWeight_eq : deformationWeight = 43 / 288 := by
  unfold deformationWeight shellWeight
  norm_num [Δ, σ, D, χ, PMSubstrate.baseline]

/-- Deformation excess above the `Z=82` threshold. -/
def deformationExcess (z n : Nat) : Nat :=
  if protonShell < valenceProduct z n then valenceProduct z n - protonShell else 0

/-- Even–even collective deformation binding, saturating below the `Z=82`
threshold. -/
def deformationBinding (z n : Nat) : ℝ :=
  if (z + n) % 2 = 0 then
    deformationWeight * (deformationExcess z n : ℝ)
  else 0

theorem deformationBinding_nonneg (z n : Nat) : 0 ≤ deformationBinding z n := by
  unfold deformationBinding
  split
  · have hw : 0 ≤ deformationWeight := by rw [deformationWeight_eq]; norm_num
    positivity
  · norm_num

theorem deformationBinding_pb : deformationBinding 82 126 = 0 := by
  simp [deformationBinding, deformationExcess, valenceProduct, protonValence, neutronValence, protonShell_eq, neutronShell_eq]

theorem deformationExcess_cm : deformationExcess 96 148 = 226 := by
  simp [deformationExcess, valenceProduct, protonValence, neutronValence,
    protonShell_eq, neutronShell_eq]

theorem deformationBinding_cm :
    deformationBinding 96 148 = deformationWeight * 226 := by
  simp [deformationBinding, deformationExcess_cm]

/-- Candidate mass with even–even collective deformation binding. -/
def nuclearMassPackingDeformed (z n : Nat) : ℝ :=
  nuclearMassPackingShellPaired z n - deformationBinding z n

theorem nuclearMassPackingDeformed_decomp (z n : Nat) :
    nuclearMassPackingDeformed z n =
      nuclearMassPackingShellPaired z n - deformationBinding z n := rfl




theorem deformationWeight_eq_E8 :
    deformationWeight = (Δ : ℝ) / (((D + χ) * (σ - χ) * ν : Nat) : ℝ) := by
  have hΔ : (Δ : ℝ) + (σ : ℝ) = (((σ - χ) * ν : Nat) : ℝ) := by
    exact_mod_cast delta_add_sigma
  unfold deformationWeight shellWeight
  rw [hΔ, div_div, mul_assoc]
  simp only [Nat.cast_mul]

theorem deformationWeight_eq_shell_axes_channels :
    deformationWeight = shellWeight / (((σ - χ) * ν : Nat) : ℝ) := by
  rw [deformationWeight_eq_E8]
  unfold shellWeight
  rw [div_div, mul_assoc, Nat.cast_mul]


/-- Upper proton closure `(σ−χ)(Δ−1) = 126`. -/
def protonUpperShell : Nat := (σ - χ) * (Δ - 1)
theorem protonUpperShell_eq : protonUpperShell = 126 := by
  norm_num [protonUpperShell, σ, χ, Δ, PMSubstrate.baseline]

/-- Upper neutron closure `D(Δ+σ−χ) = 184`. -/
def neutronUpperShell : Nat := D * (Δ + σ - χ)
theorem neutronUpperShell_eq : neutronUpperShell = 184 := by
  norm_num [neutronUpperShell, D, Δ, σ, χ, PMSubstrate.baseline]

def protonValenceCapped (z : Nat) : Nat :=
  if protonShell < z ∧ z < protonUpperShell then
    min (z - protonShell) (protonUpperShell - z)
  else 0

def neutronValenceCapped (n : Nat) : Nat :=
  if neutronShell < n ∧ n < neutronUpperShell then
    min (n - neutronShell) (neutronUpperShell - n)
  else 0

def valenceProductCapped (z n : Nat) : Nat :=
  protonValenceCapped z * neutronValenceCapped n


/-- Z-dependent deformation factor `(Z−82)/(ν−χ)`, zero below `Z=82`. -/
def deformationZFactor (z : Nat) : ℝ :=
  (protonValence z : ℝ) / (((ν - χ : Nat)) : ℝ)

theorem deformationZFactor_cm : deformationZFactor 96 = 1 := by
  unfold deformationZFactor protonValence
  norm_num [protonShell_eq, ν, χ, PMSubstrate.baseline]

/-- Even-even deformation binding with the Z-dependent factor. -/
def deformationBindingZ (z n : Nat) : ℝ :=
  if (z + n) % 2 = 0 then
    deformationWeight * deformationZFactor z * (deformationExcess z n : ℝ)
  else 0

theorem deformationBindingZ_nonneg (z n : Nat) : 0 ≤ deformationBindingZ z n := by
  unfold deformationBindingZ
  split
  · have hw : 0 ≤ deformationWeight := by rw [deformationWeight_eq]; norm_num
    have hf : 0 ≤ deformationZFactor z := by
      unfold deformationZFactor
      positivity
    positivity
  · norm_num

def nuclearMassPackingDeformedZ (z n : Nat) : ℝ :=
  nuclearMassPackingShellPaired z n - deformationBindingZ z n

theorem nuclearMassPackingDeformedZ_decomp (z n : Nat) :
    nuclearMassPackingDeformedZ z n =
      nuclearMassPackingShellPaired z n - deformationBindingZ z n := rfl


/-- Lower eigenvalue of a two-shape mixing matrix with off-diagonal `V`. -/
noncomputable def mixingMass (m_spherical m_deformed V : ℝ) : ℝ :=
  (m_spherical + m_deformed) / 2 -
    Real.sqrt (((m_spherical - m_deformed) / 2) ^ 2 + V ^ 2)

/-- Two-shape coexistence mass: spherical and Z-deformed configurations mixed by
the shell weight `V = shellWeight`.  The `+ V` keeps the no-deformation limit
equal to the spherical mass. -/
noncomputable def nuclearMassPackingCoexist (z n : Nat) : ℝ :=
  mixingMass (nuclearMassPackingShellPaired z n)
    (nuclearMassPackingDeformedZ z n) shellWeight + shellWeight

theorem nuclearMassPackingCoexist_decomp (z n : Nat) :
    nuclearMassPackingCoexist z n =
      mixingMass (nuclearMassPackingShellPaired z n)
        (nuclearMassPackingDeformedZ z n) shellWeight + shellWeight := rfl


/-- Pairing factor: even–even `1`, odd–odd `1/2`, odd-A `0`. -/
def deformationPairingFactor (z n : Nat) : ℝ :=
  if z % 2 = 0 ∧ n % 2 = 0 then 1
  else if z % 2 = 1 ∧ n % 2 = 1 then 1 / 2
  else 0

theorem deformationPairingFactor_even_even (z n : Nat)
    (hz : z % 2 = 0) (hn : n % 2 = 0) :
    deformationPairingFactor z n = 1 := by
  unfold deformationPairingFactor
  rw [ite_eq_left ⟨hz, hn⟩]

theorem deformationPairingFactor_odd_odd (z n : Nat)
    (hz : z % 2 = 1) (hn : n % 2 = 1) :
    deformationPairingFactor z n = 1 / 2 := by
  unfold deformationPairingFactor
  rw [ite_eq_right (by omega : ¬ (z % 2 = 0 ∧ n % 2 = 0))]
  rw [ite_eq_left ⟨hz, hn⟩]

theorem deformationPairingFactor_odd_A (z n : Nat)
    (h : z % 2 ≠ n % 2) :
    deformationPairingFactor z n = 0 := by
  unfold deformationPairingFactor
  rw [ite_eq_right (by omega : ¬ (z % 2 = 0 ∧ n % 2 = 0))]
  rw [ite_eq_right (by omega : ¬ (z % 2 = 1 ∧ n % 2 = 1))]

def deformationBindingZPair (z n : Nat) : ℝ :=
  deformationWeight * deformationZFactor z * deformationPairingFactor z n *
    (deformationExcess z n : ℝ)

def nuclearMassPackingDeformedZPair (z n : Nat) : ℝ :=
  nuclearMassPackingShellPaired z n - deformationBindingZPair z n

theorem nuclearMassPackingDeformedZPair_decomp (z n : Nat) :
    nuclearMassPackingDeformedZPair z n =
      nuclearMassPackingShellPaired z n - deformationBindingZPair z n := rfl

/-- E8 deformation ledger, replacing the supplied Landau coefficient. -/
noncomputable def e8DeformationLedger (z n : Nat) : ℝ :=
  deformationBinding z n

theorem e8DeformationLedger_eq (z n : Nat) (h : (z + n) % 2 = 0) :
    e8DeformationLedger z n =
      deformationWeight * deformationExcess z n := by
  unfold e8DeformationLedger deformationBinding
  rw [ite_eq_left h]

end PMAtoms
