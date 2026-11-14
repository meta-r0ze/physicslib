import PMFlavor.ThirdGenerationMixing

/-!
# The charged-current transfer is zero-energy scattering: the Cayley form

`ThirdGenerationMixing` and the numerical fits (`tools/flavour_link_fits.py`, OVERVIEW) exclude a
conserving mass link carrying the CKM. The reading with a test is: the masses are generation-diagonal
(`GenerationLabel`: root moves conserve the label) and the CKM is the charged current's transfer
through the fluxed incidence network `K` (a mass link with free diagonal entries is not excluded, but
is untestable until they are derived). This module fixes how `K` generates the transfer, from conventions the library
already uses.

* The dressing is a transfer out of the generation block (`DressingEvent`), transmission is
  admittance (Landauer, `PMConstants.HandoffAdmittance`), and the light sector is the zero-energy
  reduction (`KronSeries`). Zero-energy scattering through a Hermitian network `K` with equal
  leads of width `γ` on the three generations is `S = 1 − 2iγ (−K + iγ)⁻¹` (Mahaux–Weidenmüller).
  Two premises, kept separate: (a) the transfer is zero-energy scattering with leads on the three
  generations; (b) the lead widths are equal, `Γ = γ·1`. Neither is derived here. `mw_eq_cayley`
  and `cayley_unimodular` are scalar identities; they do not construct the leads or fix their
  widths. (b) is motivated by `HandoffAdmittance.closure_one_price`, but that theorem is about a
  price function invariant under relabelling; applying it to lead widths needs the lead coupling to
  be symmetric under a transitive relabelling of the generations, which the node (distinguishing
  the reference-free generation) does not obviously allow.
* `mw_eq_cayley`: on each eigenvalue `k = xγ` of `K` this is `−(1 − ix)/(1 + ix)`, the Cayley
  transform of `K/γ` up to a global sign (a rephasing). `cayley_unimodular`: it is a phase, so `S`
  is unitary.
* So the generator is Cayley, not the exponential; the lead width `γ` is one overall scale, and
  only ratios of couplings are data.

**Observable.** The CKM entries are `S_ij`, not `K_ij`: `S₁₃ = −iK₁₃ − ½(K²)₁₃ + …` (with `K` in units
of `γ/2`). A path admittance is a statement about `K`.

**What the data then say** (external numerical fits, `tools/flavour_link_fits.py`, conditional on
(a) and (b); PDG 2024 CKM): a flux of
`49.1 ± 1.1°` and `K₁₃/K₁₂ = 0.0185 ± 0.0005`, `K₂₃/K₁₂ = 0.183`. `VubSeriesPath`'s construction
is the direct first-order path, `K₁₃`; its value over the in-cycle coupling,
`(1/(2α⁻¹ + π))/(π/14) = 0.0161`, is `4.7σ` below `0.0185`. The `1σ` agreement of
`1/(2α⁻¹ + π)` with `|V_ub|` is with the full amplitude, which includes the second-order route
through the in-cycle pair (`−½K₁₂K₂₃`, as large as `K₁₃`). So in this reading the series-path
match is not structural.

With unequal leads (a diagonal width matrix), the scalar identities still hold eigenvalue by
eigenvalue only when the widths commute with `K`; in general the common-scale reading and the ratio
test both fail. So the numbers above stand or fall with (b).
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
