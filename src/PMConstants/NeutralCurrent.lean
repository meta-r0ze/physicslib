import PMConstants.ReferenceMasses
import PMConstants.TableConsequences

/-!
# The photon and Z couplings from the reference's mass form

`ReferenceMasses.neutral_form` shows the neutral mass form read on the reference has null vector
`(g', g)`: the photon. Rotating the neutral fields onto that basis gives the currents.

With `N = √(g² + g'²)`, `c = g/N`, `s = g'/N`, write `W₃ = cZ + sA` and `B = -sZ + cA`.
* `photon_coupling`: the coefficient of `A` in `g T₃ W₃ + g' (Y/2) B` is `e Q` with `e = g g'/N`.
* `z_coupling`: the coefficient of `Z` is `N (T₃ - s² Q)`.
* `electric_matching`: `1/e² = 1/g² + 1/g'²`. This is the matching that
  `TableConsequences.electric_partition` reads as the sum of the two ledgers; here it follows from
  the massless direction of the reference's mass form.
* `photon_is_null`: the photon direction `(s, c)` is the null vector of the neutral form, and the Z
  direction `(c, -s)` carries the trace `N²/4` (`z_mass`).
-/

noncomputable section
namespace PMConstants.NeutralCurrent
open PMConstants Matrix GeneratorNormalization PacketTraceForm

variable (g g' : ℝ)

def N : ℝ := Real.sqrt (g ^ 2 + g' ^ 2)

lemma N_sq (hg : 0 < g) : N g g' ^ 2 = g ^ 2 + g' ^ 2 := Real.sq_sqrt (by positivity)

lemma N_pos (hg : 0 < g) : 0 < N g g' := Real.sqrt_pos.mpr (by positivity)

/-- **The photon couples to `e Q`.** -/
theorem photon_coupling :
    ((g * (g' / N g g') : ℝ) : ℂ) • t3 + ((g' * (g / N g g') : ℝ) : ℂ) • hyperGen =
      ((g * g' / N g g' : ℝ) : ℂ) • (t3 + hyperGen) := by
  push_cast; module

/-- **The Z couples to `N (T₃ - s² Q)`.** -/
theorem z_coupling (hg : 0 < g) :
    ((g * (g / N g g') : ℝ) : ℂ) • t3 - ((g' * (g' / N g g') : ℝ) : ℂ) • hyperGen =
      ((N g g' : ℝ) : ℂ) • (t3 - ((g' ^ 2 / (g ^ 2 + g' ^ 2) : ℝ) : ℂ) • (t3 + hyperGen)) := by
  have hN := N_pos g g' hg
  have hN2 := N_sq g g' hg
  have hs : g ^ 2 + g' ^ 2 ≠ 0 := by positivity
  have hNc : ((N g g' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have key1 : g * (g / N g g') = N g g' * (1 - g' ^ 2 / (g ^ 2 + g' ^ 2)) := by
    field_simp; linear_combination (-g ^ 2) * hN2
  have key2 : g' * (g' / N g g') = N g g' * (g' ^ 2 / (g ^ 2 + g' ^ 2)) := by
    field_simp; linear_combination (-g' ^ 2) * hN2
  rw [key1, key2]
  push_cast
  module

/-- **The electric matching.** -/
theorem electric_matching (hg : 0 < g) (hg' : 0 < g') :
    1 / (g * g' / N g g') ^ 2 = 1 / g ^ 2 + 1 / g' ^ 2 := by
  have hN2 := N_sq g g' hg
  rw [div_pow, hN2]
  field_simp
  ring

theorem photon_is_null :
    (ReferenceMasses.neutralForm g g') *ᵥ ![g' / N g g', g / N g g'] = 0 := by
  have h := (ReferenceMasses.neutral_form g g').2.2
  have e : ![g' / N g g', g / N g g'] = (1 / N g g') • ![g', g] := by
    ext i; fin_cases i <;> simp <;> ring
  rw [e, mulVec_smul, h, smul_zero]

theorem z_mass (hg : 0 < g) : (ReferenceMasses.neutralForm g g').trace = N g g' ^ 2 / 4 := by
  rw [(ReferenceMasses.neutral_form g g').2.1, N_sq g g' hg]

end PMConstants.NeutralCurrent
