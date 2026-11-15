import Mathlib.Tactic

/-!
# Kron reduction of a conserving network: series admittance

A conserving link is a network Laplacian: each off-diagonal entry is minus a conductance and each
diagonal the sum of the incident conductances. At zero energy, eliminating an internal node is the
Schur complement (Kron reduction).

* `kron_two`: a node with legs `g₁`, `g₂` reduces to the coupling `−g₁g₂/(g₁ + g₂)`, minus the series
  admittance `1/(1/g₁ + 1/g₂)`.
* `kron_three`: eliminating a second internal node in a chain adds the next element in series.

Used by the wire's node amplitude (`NodeAmplitude`) and by `PMFlavor.KronSeries`.
-/

namespace PMAction.KronReduction

theorem kron_two (g₁ g₂ : ℝ) (h₁ : 0 < g₁) (h₂ : 0 < g₂) :
    (-g₁) * (-g₂) / (0 - (g₁ + g₂)) = -(1 / (1 / g₁ + 1 / g₂)) := by
  have hs : g₁ + g₂ ≠ 0 := by positivity
  rw [show (0 : ℝ) - (g₁ + g₂) = -(g₁ + g₂) by ring,
    show 1 / g₁ + 1 / g₂ = (g₁ + g₂) / (g₁ * g₂) by field_simp; ring]
  field_simp

theorem kron_three (g₁ g₂ g₃ : ℝ) :
    1 / (1 / (1 / (1 / g₁ + 1 / g₂)) + 1 / g₃) = 1 / (1 / g₁ + 1 / g₂ + 1 / g₃) := by
  rw [one_div_one_div]

end PMAction.KronReduction
