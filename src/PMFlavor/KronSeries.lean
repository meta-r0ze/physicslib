import PMFlavor.VubSeriesPath

/-!
# Why a node-crossing amplitude is a series admittance: the link is a conserving network

`VubSeriesPath` read `|V_ub|` as the admittance of two node legs and a boundary in series, with the
premise "the amplitude of a passive path is its admittance". `NodeElimination` gives the effective
coupling after eliminating the node, `t₁t₂/(e − E)`, but left `e − E` open. Conservation fixes it.

If the link conserves what it transfers (Kirchhoff: each row sums to zero, Conservation), it is a
network Laplacian: the off-diagonal entries are minus the conductances, `t = −g`, and each node's
diagonal is the sum of its incident conductances, `E = g₁ + g₂`. At zero energy (`e = 0`, the
light sector of `PMAction.WallSeesaw`) eliminating the node is Kron reduction:
* `kron_two`: the effective coupling is `−g₁g₂/(g₁ + g₂) = −1/(1/g₁ + 1/g₂)`, minus the series
  admittance. So `e − E = −(g₁ + g₂)` is the node's own conductance, not a free denominator.
* `kron_three`: eliminating a second internal node in a chain adds the next element in series,
  `1/(1/g₁ + 1/g₂ + 1/g₃)`.
* `vub_from_kron`: with the two node legs `g = α = 1/Z` and the unit boundary `g = 1/π`, the
  reduced coupling is `1/(2Z + π) = CKM.s13`.
* `product_reading_wrong`: the leg product with a unit denominator, `g₁g₂ = α²`, is not this; it
  misses the node's own conductance.

So the series-path premise of `VubSeriesPath` follows from Conservation (the link is a Laplacian)
and the node elimination. The same Kirchhoff network gives dividers (`VcbEnvelope`'s
`env 1 / env (Δ − D)` is the potential fraction across one element of a series chain); which
elements the `c`-side hop drives through is the remaining reading there.
-/

namespace PMFlavor.KronSeries

theorem kron_two (g₁ g₂ : ℝ) (h₁ : 0 < g₁) (h₂ : 0 < g₂) :
    (-g₁) * (-g₂) / (0 - (g₁ + g₂)) = -(1 / (1 / g₁ + 1 / g₂)) := by
  have hs : g₁ + g₂ ≠ 0 := by positivity
  rw [show (0 : ℝ) - (g₁ + g₂) = -(g₁ + g₂) by ring,
    show 1 / g₁ + 1 / g₂ = (g₁ + g₂) / (g₁ * g₂) by field_simp; ring]
  field_simp

theorem kron_three (g₁ g₂ g₃ : ℝ) :
    1 / (1 / (1 / (1 / g₁ + 1 / g₂)) + 1 / g₃) = 1 / (1 / g₁ + 1 / g₂ + 1 / g₃) := by
  rw [one_div_one_div]

theorem vub_from_kron (Z : ℝ) :
    1 / (1 / (1 / Z) + 1 / (1 / Z) + 1 / (1 / Real.pi)) = 1 / (2 * Z + Real.pi) := by
  simp only [one_div_one_div]
  congr 1; ring

theorem vub_is_kron : 1 / (1 / (1 / CKM.αinv) + 1 / (1 / CKM.αinv) + 1 / (1 / Real.pi)) =
    CKM.s13 := by
  rw [vub_from_kron]; rfl

theorem product_reading_wrong (Z : ℝ) (hZ : 2 < Z) :
    (1 / Z) * (1 / Z) ≠ 1 / (2 * Z) := by
  intro h
  have hZ0 : 0 < Z := by linarith
  field_simp at h
  nlinarith

end PMFlavor.KronSeries
