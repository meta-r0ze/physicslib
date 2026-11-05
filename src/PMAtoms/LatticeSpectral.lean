import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import PMAtoms.NuclearPacking3D

/-!
# Spectral charge geometry for the `n×n×n` cube

This module defines the separable Dirichlet sine basis and the spectral Green
function.  The two hard identities are left as explicit open targets in the
comments below; the definitions and the symmetry lemma are complete.

Open targets:

* `cubeLapN_mode` — the sine modes diagonalize the Dirichlet Laplacian.
* `cubeLapN_spectralGreen` — the spectral sum is the inverse Laplacian.
* `uniformResponse_odd` — only odd modes contribute to a uniform charge.
* `uniformResponse_asymptotic` — `S(n)/n^5 → 1/(16π)`.
-/

noncomputable section
namespace PMAtoms
open Finset
open scoped BigOperators

/-- Adjacency of the `n×n×n` Dirichlet cube. -/
def cubeAdjN (n : Nat) (u v : CubeVertex n) : Prop :=
  (u.1 = v.1 ∧ u.2.1 = v.2.1 ∧
    (u.2.2.val + 1 = v.2.2.val ∨ v.2.2.val + 1 = u.2.2.val)) ∨
  (u.1 = v.1 ∧ u.2.2 = v.2.2 ∧
    (u.2.1.val + 1 = v.2.1.val ∨ v.2.1.val + 1 = u.2.1.val)) ∨
  (u.2.1 = v.2.1 ∧ u.2.2 = v.2.2 ∧
    (u.1.val + 1 = v.1.val ∨ v.1.val + 1 = u.1.val))

/-- Integer-indexed extension of a path function, zero outside `0..n-1`. -/
def pathExt (n : Nat) (f : Fin n → ℝ) (i : ℤ) : ℝ :=
  if h : 0 ≤ i ∧ i < n then f ⟨i.toNat, by omega⟩ else 0

/-- 1D Dirichlet Laplacian on `Fin n`. -/
def pathLapN (n : Nat) (f : Fin n → ℝ) (i : Fin n) : ℝ :=
  2 * f i - pathExt n f ((i.val : ℤ) - 1) - pathExt n f ((i.val : ℤ) + 1)

/-- 1D Dirichlet eigenvalue. -/
def pathEigenvalue (n k : Nat) : ℝ :=
  2 - 2 * Real.cos (Real.pi * k / (n + 1))

/-- 1D Dirichlet sine mode. -/
def pathMode (n k : Nat) (i : Fin n) : ℝ :=
  Real.sin (Real.pi * k * (i.val + 1) / (n + 1))

lemma sin_lap_identity (x t : ℝ) :
    2 * Real.sin x - Real.sin (x - t) - Real.sin (x + t) =
      (2 - 2 * Real.cos t) * Real.sin x := by
  rw [Real.sin_sub, Real.sin_add]
  ring

lemma pathExt_pathMode (n k : Nat) (i : ℤ) (hi : -1 ≤ i) (hin : i ≤ n) :
    pathExt n (pathMode n k) i =
      Real.sin (Real.pi * k * (i + 1) / (n + 1)) := by
  unfold pathExt pathMode
  by_cases h : 0 ≤ i ∧ i < n
  · rw [dite_eq_left h]
    have hcast : ((i.toNat : Nat) : ℝ) = (i : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg h.1
    congr 1
    push_cast
    rw [hcast]
  · rw [dite_eq_right h]
    have hcases : i = -1 ∨ i = n := by omega
    rcases hcases with rfl | rfl
    · simp
    · have hsin : Real.sin (Real.pi * (k : ℝ)) = 0 := by
        simpa [mul_comm] using Real.sin_nat_mul_pi k
      have harg :
          Real.pi * (k : ℝ) * ((n : ℤ) + 1) / ((n : ℝ) + 1) =
            Real.pi * (k : ℝ) := by
        have hn : (n : ℝ) + 1 ≠ 0 := by positivity
        field_simp [hn]
        norm_num
      rw [harg, hsin]

theorem pathLapN_mode (n k : Nat) (_hk : 1 ≤ k) (_hk' : k ≤ n) :
    pathLapN n (pathMode n k) =
      fun i => pathEigenvalue n k * pathMode n k i := by
  funext i
  unfold pathLapN pathEigenvalue
  have hprev := pathExt_pathMode n k ((i.val : ℤ) - 1) (by omega) (by omega)
  have hnext := pathExt_pathMode n k ((i.val : ℤ) + 1) (by omega) (by omega)
  rw [hprev, hnext]
  unfold pathMode
  convert sin_lap_identity
    (Real.pi * (k : ℝ) * (i.val + 1) / ((n : ℝ) + 1))
    (Real.pi * (k : ℝ) / ((n : ℝ) + 1)) using 2
  all_goals
    congr 1
    push_cast
    ring_nf

/-- Dirichlet Laplacian on the `n×n×n` cube, as the sum of three 1D path
Laplacians. -/
def cubeLapN (n : Nat) (f : CubeVertex n → ℝ) (v : CubeVertex n) : ℝ :=
  pathLapN n (fun i => f (i, v.2.1, v.2.2)) v.1
    + pathLapN n (fun j => f (v.1, j, v.2.2)) v.2.1
    + pathLapN n (fun k => f (v.1, v.2.1, k)) v.2.2

/-- Dirichlet eigenvalue. -/
def dirichletEigenvalue (n a b c : Nat) : ℝ :=
  6
    - 2 * Real.cos (Real.pi * a / (n + 1))
    - 2 * Real.cos (Real.pi * b / (n + 1))
    - 2 * Real.cos (Real.pi * c / (n + 1))

/-- Dirichlet sine mode. -/
def dirichletMode (n a b c : Nat) (v : CubeVertex n) : ℝ :=
  Real.sin (Real.pi * a * (v.1.val + 1) / (n + 1)) *
  Real.sin (Real.pi * b * (v.2.1.val + 1) / (n + 1)) *
  Real.sin (Real.pi * c * (v.2.2.val + 1) / (n + 1))

/-- Spectral Green function. -/
def spectralGreen (n : Nat) (u v : CubeVertex n) : ℝ :=
  (2 / (n + 1)) ^ 3 *
    ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
      dirichletMode n (a.val + 1) (b.val + 1) (c.val + 1) u *
      dirichletMode n (a.val + 1) (b.val + 1) (c.val + 1) v /
      dirichletEigenvalue n (a.val + 1) (b.val + 1) (c.val + 1)

/-- The spectral Green function is symmetric. -/
theorem spectralGreen_symm (n : Nat) (u v : CubeVertex n) :
    spectralGreen n u v = spectralGreen n v u := by
  unfold spectralGreen
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- Uniform-charge response.  Only odd sine modes contribute, and each
contributes the cotangent transform `cot(πk/(2(n+1)))`. -/
def uniformResponse (n : Nat) : ℝ :=
  (2 / ((n : ℝ) + 1)) ^ 3 *
    ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
      if (a.val + 1) % 2 = 1 ∧
         (b.val + 1) % 2 = 1 ∧
         (c.val + 1) % 2 = 1 then
        (1 / Real.tan (Real.pi * (a.val + 1) / (2 * ((n : ℝ) + 1))) *
         1 / Real.tan (Real.pi * (b.val + 1) / (2 * ((n : ℝ) + 1))) *
         1 / Real.tan (Real.pi * (c.val + 1) / (2 * ((n : ℝ) + 1)))) ^ 2 /
        dirichletEigenvalue n (a.val + 1) (b.val + 1) (c.val + 1)
      else 0

end PMAtoms
