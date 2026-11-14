import PMFlavor.ThirdGenerationMixing

/-!
# The charged-current transfer is zero-energy scattering: the Cayley form

`ThirdGenerationMixing` and the numerical fits (`tools/flavour_link_fits.py`, OVERVIEW) leave one
reading of the CKM standing: the masses are generation-diagonal (`GenerationLabel`: root moves
conserve the label) and the CKM is the charged current's transfer through the fluxed incidence
network `K`. This module fixes how `K` generates the transfer, from conventions the library
already uses.

* The dressing is a transfer out of the generation block (`DressingEvent`), transmission is
  admittance (Landauer, `PMConstants.HandoffAdmittance`), and the light sector is the zero-energy
  reduction (`KronSeries`). Zero-energy scattering through a Hermitian network `K` with equal
  leads of width `γ` on the three generations (Closure's one price,
  `HandoffAdmittance.closure_one_price`) is `S = 1 − 2iγ (−K + iγ)⁻¹` (Mahaux–Weidenmüller).
* `mw_eq_cayley`: on each eigenvalue `k = xγ` of `K` this is `−(1 − ix)/(1 + ix)`, the Cayley
  transform of `K/γ` up to a global sign (a rephasing). `cayley_unimodular`: it is a phase, so `S`
  is unitary.
* So the generator is Cayley, not the exponential; the lead width `γ` is one overall scale, and
  only ratios of couplings are data.

**What the data then say** (numerical, `tools/flavour_link_fits.py`; PDG 2024 CKM): a flux of
`49.1 ± 1.1°` and `K₁₃/K₁₂ = 0.0185 ± 0.0005`, `K₂₃/K₁₂ = 0.183`. `VubSeriesPath`'s construction
is the direct first-order path, `K₁₃`; its value over the in-cycle coupling,
`(1/(2α⁻¹ + π))/(π/14) = 0.0161`, is `4.7σ` below `0.0185`. The `1σ` agreement of
`1/(2α⁻¹ + π)` with `|V_ub|` is with the full amplitude, which includes the second-order route
through the in-cycle pair (`−½K₁₂K₂₃`, as large as `K₁₃`). So in this reading the series-path
match is not structural.

Premise: equal lead widths for the three generations. Unequal leads would add two scales and
remove the ratio test.
-/

namespace PMFlavor.TransferGenerator
open Complex

theorem one_add_ne (x : ℝ) : (1 : ℂ) + I * x ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

/-- **Zero-energy scattering is the Cayley transform**, eigenvalue by eigenvalue. For an
eigenvalue `k = x γ` of `K` and lead width `γ`, `1 − 2iγ/(−k + iγ) = −(1 − ix)/(1 + ix)`. -/
theorem mw_eq_cayley (x γ : ℝ) (hγ : γ ≠ 0) :
    1 - 2 * I * γ / (-((x * γ : ℝ) : ℂ) + γ * I) = -((1 - I * x) / (1 + I * x)) := by
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
  have h2 := one_add_ne x
  have h1 : -((x * γ : ℝ) : ℂ) + γ * I = γ * I * (1 + I * x) := by
    push_cast
    linear_combination (-(γ : ℂ) * x) * I_sq
  have e1 : 2 * I * (γ : ℂ) / ((γ : ℂ) * I * (1 + I * x)) = 2 / (1 + I * x) := by
    rw [div_eq_div_iff (mul_ne_zero (mul_ne_zero hγc I_ne_zero) h2) h2]
    ring
  rw [h1, e1, neg_div', eq_div_iff h2, sub_mul, div_mul_cancel₀ _ h2]
  ring

/-- **The Cayley factor is a phase**: `|(1 − ix)/(1 + ix)| = 1` for real `x`, so `S` is unitary. -/
theorem cayley_unimodular (x : ℝ) : ‖(1 - I * x) / (1 + I * x)‖ = 1 := by
  have hn : ‖(1 : ℂ) + I * x‖ ≠ 0 := norm_ne_zero_iff.mpr (one_add_ne x)
  rw [norm_div, div_eq_one_iff_eq hn]
  rw [show (1 : ℂ) - I * x = (starRingEnd ℂ) (1 + I * x) by
    rw [map_add, map_mul, map_one, Complex.conj_I, Complex.conj_ofReal]; ring]
  exact Complex.norm_conj _

end PMFlavor.TransferGenerator
