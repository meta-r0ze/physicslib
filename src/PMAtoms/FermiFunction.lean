import PMConstants.Values
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! **Continuum comparison.** Coulomb Fermi function; it is not an E8 assumption. The E8-native alternative is the finite lattice channel of `PMAtoms.BetaLattice`.

 **Experimental/candidate module.** Not part of `certifiedMass`.

# Coulomb Fermi function for beta decay

The allowed beta Coulomb factor is

```
F(Z,E) = 2π η / (1 − exp(−2π η)),    η = Z α E / p.
```

This module proves positivity and `F ≥ 1` for a positively charged daughter.
The nuclear matrix element and the full relativistic Fermi function remain
separate inputs.
-/

noncomputable section
namespace PMAtoms

open PMConstants

/-- Sommerfeld parameter `η = Z α E / p`. -/
def coulombEta (Z E p : ℝ) : ℝ :=
  Z * Values.alpha * E / p

/-- Allowed beta Fermi function. -/
def fermiFunction (Z E p : ℝ) : ℝ :=
  let η := coulombEta Z E p
  2 * Real.pi * η / (1 - Real.exp (-(2 * Real.pi * η)))

theorem alpha_pos : 0 < Values.alpha := by
  have h := Values.alpha_bounds
  linarith

theorem coulombEta_pos {Z E p : ℝ} (hZ : 0 < Z) (hE : 0 < E) (hp : 0 < p) :
    0 < coulombEta Z E p := by
  unfold coulombEta
  exact div_pos (mul_pos (mul_pos hZ alpha_pos) hE) hp

theorem fermiFunction_pos {Z E p : ℝ} (hZ : 0 < Z) (hE : 0 < E) (hp : 0 < p) :
    0 < fermiFunction Z E p := by
  have hη := coulombEta_pos hZ hE hp
  have hx : 0 < 2 * Real.pi * coulombEta Z E p := by positivity
  have hexp : Real.exp (-(2 * Real.pi * coulombEta Z E p)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hden : 0 < 1 - Real.exp (-(2 * Real.pi * coulombEta Z E p)) := by linarith
  unfold fermiFunction
  have hnum : 0 < 2 * Real.pi * coulombEta Z E p := by positivity
  exact div_pos hnum hden

theorem fermiFunction_ge_one {Z E p : ℝ} (hZ : 0 < Z) (hE : 0 < E) (hp : 0 < p) :
    1 ≤ fermiFunction Z E p := by
  have hη := coulombEta_pos hZ hE hp
  have hx : 0 < 2 * Real.pi * coulombEta Z E p := by positivity
  have hexp : Real.exp (-(2 * Real.pi * coulombEta Z E p)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hden : 0 < 1 - Real.exp (-(2 * Real.pi * coulombEta Z E p)) := by linarith
  unfold fermiFunction
  rw [le_div_iff₀ hden]
  have h := Real.add_one_le_exp (-(2 * Real.pi * coulombEta Z E p))
  nlinarith

end PMAtoms

namespace PMAtoms

open PMConstants

/-! ## Threshold behavior

The beta integrand contains `F · p`, not `F` alone.  The product is finite at
threshold and grows at most like `p + 2π Z α E`.  This is why the physical
integrand has no non-integrable Coulomb singularity even though `F` itself
diverges. -/

/-- `F · p`, extended at `p = 0` by its finite limit. -/
def fermiMomentumFactor (Z E p : ℝ) : ℝ :=
  if p = 0 then
    2 * Real.pi * Z * Values.alpha * E
  else
    2 * Real.pi * Z * Values.alpha * E /
      (1 - Real.exp (-(2 * Real.pi * Z * Values.alpha * E / p)))

theorem fermiMomentumFactor_pos {Z E p : ℝ} (hZ : 0 < Z) (hE : 0 < E) (hp : 0 ≤ p) :
    0 < fermiMomentumFactor Z E p := by
  by_cases h0 : p = 0
  · subst p
    unfold fermiMomentumFactor
    rw [ite_eq_left rfl]
    exact mul_pos (mul_pos (mul_pos (by positivity : 0 < 2 * Real.pi) hZ)
      alpha_pos) hE
  · have hp0 : 0 < p := lt_of_le_of_ne hp (Ne.symm h0)
    have hC : 0 < 2 * Real.pi * Z * Values.alpha * E := by
      have ha := alpha_pos
      positivity
    have hx : 0 < 2 * Real.pi * Z * Values.alpha * E / p := div_pos hC hp0
    have hexp : Real.exp (-(2 * Real.pi * Z * Values.alpha * E / p)) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    have hden : 0 < 1 - Real.exp (-(2 * Real.pi * Z * Values.alpha * E / p)) := by
      linarith
    unfold fermiMomentumFactor
    rw [ite_eq_right h0]
    exact div_pos hC hden


/-- Elementary lower bound `1 − e^{−x} ≥ x/(1+x)` for `x > 0`. -/
theorem one_sub_exp_neg_ge (x : ℝ) (hx : 0 < x) :
    x / (1 + x) ≤ 1 - Real.exp (-x) := by
  have hx1 : 0 < 1 + x := by linarith
  have hexp : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hrec : Real.exp (-x) ≤ 1 / (1 + x) := by
    have h := one_div_le_one_div_of_le hx1 hexp
    simpa [Real.exp_neg, one_div] using h
  have h : 1 - 1 / (1 + x) = x / (1 + x) := by
    field_simp
    ring
  linarith

/-- The physical factor `F · p` is bounded by `p + 2π Z α E`. -/
theorem fermiMomentumFactor_le {Z E p : ℝ} (hZ : 0 < Z) (hE : 0 < E) (hp : 0 < p) :
    fermiMomentumFactor Z E p ≤ p + 2 * Real.pi * Z * Values.alpha * E := by
  let C : ℝ := 2 * Real.pi * Z * Values.alpha * E
  have hC : 0 < C := by
    dsimp [C]
    have ha := alpha_pos
    positivity
  have hx : 0 < C / p := div_pos hC hp
  have hx1 : 0 < 1 + C / p := by linarith
  have hden := one_sub_exp_neg_ge (C / p) hx
  have hdenpos : 0 < 1 - Real.exp (-(C / p)) := by
    have hpos : 0 < (C / p) / (1 + C / p) := div_pos hx hx1
    linarith
  have hrec : (1 - Real.exp (-(C / p)))⁻¹ ≤ (1 + C / p) / (C / p) := by
    have hpos : 0 < (C / p) / (1 + C / p) := div_pos hx hx1
    have h := one_div_le_one_div_of_le hpos hden
    simpa [one_div] using h
  unfold fermiMomentumFactor
  rw [ite_eq_right (ne_of_gt hp)]
  change C / (1 - Real.exp (-(C / p))) ≤ p + C
  calc
    C / (1 - Real.exp (-(C / p))) = C * (1 - Real.exp (-(C / p)))⁻¹ := by ring
    _ ≤ C * ((1 + C / p) / (C / p)) :=
      mul_le_mul_of_nonneg_left hrec (le_of_lt hC)
    _ = p + C := by
      field_simp [hp.ne']

end PMAtoms
