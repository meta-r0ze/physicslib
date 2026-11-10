import PMAtoms.NuclearDeformation
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.


# Landau shape potential

The series of deformation corrections is the Taylor expansion of one collective
potential.  This module records the general one-dimensional Landau potential

`V(β) = A β² + B β³ + C β⁴`

and its basic stationary/coexistence structure.  The physical coefficients are
to be derived from the E8 invariants and shell filling; this module is the
structural home for that derivation.
-/

noncomputable section
namespace PMAtoms
open PMElementaryParticles PMHadrons

/-- One-dimensional Landau shape potential. -/
structure ShapePotential where
  A : ℝ
  B : ℝ
  C : ℝ

/-- The collective potential. -/
def ShapePotential.V (p : ShapePotential) (β : ℝ) : ℝ :=
  p.A * β ^ 2 + p.B * β ^ 3 + p.C * β ^ 4

theorem ShapePotential.V_zero (p : ShapePotential) : p.V 0 = 0 := by
  simp [ShapePotential.V]

/-- Stationary condition `dV/dβ = 0`. -/
def ShapePotential.Stationary (p : ShapePotential) (β : ℝ) : Prop :=
  2 * p.A * β + 3 * p.B * β ^ 2 + 4 * p.C * β ^ 3 = 0

/-- A nonzero stationary point satisfies the reduced quadratic condition. -/
theorem ShapePotential.stationary_nonzero {p : ShapePotential} {β : ℝ}
    (hβ : β ≠ 0) (h : p.Stationary β) :
    2 * p.A + 3 * p.B * β + 4 * p.C * β ^ 2 = 0 := by
  unfold ShapePotential.Stationary at h
  have hfactor : β * (2 * p.A + 3 * p.B * β + 4 * p.C * β ^ 2) = 0 := by
    calc
      β * (2 * p.A + 3 * p.B * β + 4 * p.C * β ^ 2)
          = 2 * p.A * β + 3 * p.B * β ^ 2 + 4 * p.C * β ^ 3 := by ring
      _ = 0 := h
  exact (mul_eq_zero.mp hfactor).resolve_left hβ

/-- Landau discriminant: positive means two nonzero stationary shapes. -/
def ShapePotential.discriminant (p : ShapePotential) : ℝ :=
  9 * p.B ^ 2 - 32 * p.A * p.C

/-- The symmetric double well `C(β² − β₀²)²`. -/
def doubleWell (C β0 β : ℝ) : ℝ := C * (β ^ 2 - β0 ^ 2) ^ 2

theorem doubleWell_nonneg {C β0 β : ℝ} (hC : 0 ≤ C) :
    0 ≤ doubleWell C β0 β := by
  unfold doubleWell
  positivity

theorem doubleWell_eq_zero_iff {C β0 β : ℝ} (hC : C ≠ 0) :
    doubleWell C β0 β = 0 ↔ β = β0 ∨ β = -β0 := by
  unfold doubleWell
  rw [mul_eq_zero, pow_eq_zero_iff (by norm_num : 2 ≠ 0)]
  constructor
  · rintro (h | h)
    · exact (hC h).elim
    · have : β ^ 2 = β0 ^ 2 := sub_eq_zero.mp h
      exact sq_eq_sq_iff_eq_or_eq_neg.mp this
  · rintro (rfl | rfl)
    · simp
    · simp

theorem doubleWell_min_at_wells {C β0 : ℝ} (hC : 0 ≤ C) :
    doubleWell C β0 β0 = 0 ∧ doubleWell C β0 (-β0) = 0 ∧
      ∀ β, 0 ≤ doubleWell C β0 β := by
  refine ⟨?_, ?_, fun β => doubleWell_nonneg hC⟩
  · unfold doubleWell; ring
  · unfold doubleWell; ring

/-- Candidate coexistence shift from a symmetric double well with depth `D`. -/
def doubleWellShift (D : ℝ) : ℝ := -D


/-- E8 control coefficients for the heavy shape potential:
`A` measures the neutron distance from the `N=126`/`N=152` region,
`B` the proton distance from the deformed `Z=96` closure,
`C` the pairing stiffness `χ`. -/
def e8ShapePotential (z n : Nat) : ShapePotential :=
  { A := (n : ℝ) - (deformedNeutronShell : ℝ)
    B := (z : ℝ) - (deformedProtonShell : ℝ)
    C := (χ : ℝ) }

theorem e8ShapePotential_C (z n : Nat) : (e8ShapePotential z n).C = 2 := by
  simp only [e8ShapePotential]
  norm_num [χ, PMSubstrate.baseline]

/-- The mass shift once an equilibrium deformation `β` is supplied. -/
def e8ShapeShift (z n : Nat) (β : ℝ) : ℝ :=
  - (e8ShapePotential z n).V β

/-- Candidate mass with a supplied equilibrium shape coordinate. -/
def nuclearMassPackingShape (z n : Nat) (β : ℝ) : ℝ :=
  nuclearMassPackingShellPaired z n + e8ShapeShift z n β

theorem nuclearMassPackingShape_decomp (z n : Nat) (β : ℝ) :
    nuclearMassPackingShape z n β =
      nuclearMassPackingShellPaired z n + e8ShapeShift z n β := rfl


/-- E8 cubic coupling `deformationWeight/ν`. -/
def cubicCoupling : ℝ := deformationWeight / (ν : ℝ)

theorem cubicCoupling_eq : cubicCoupling = (43 / 288) / 16 := by
  unfold cubicCoupling deformationWeight shellWeight
  norm_num [Δ, ν, σ, D, χ, PMSubstrate.baseline]

/-- Landau potential with the E8 cubic/asymmetry coupling. -/
def e8CubicPotential (z n : Nat) : ShapePotential :=
  { A := (n : ℝ) - (deformedNeutronShell : ℝ)
    B := cubicCoupling * (valenceProduct z n : ℝ)
    C := (χ : ℝ) }

def e8CubicShift (z n : Nat) (β : ℝ) : ℝ :=
  - (e8CubicPotential z n).V β

def nuclearMassPackingCubic (z n : Nat) (β : ℝ) : ℝ :=
  nuclearMassPackingShellPaired z n + e8CubicShift z n β

theorem nuclearMassPackingCubic_decomp (z n : Nat) (β : ℝ) :
    nuclearMassPackingCubic z n β =
      nuclearMassPackingShellPaired z n + e8CubicShift z n β := rfl

end PMAtoms
