import PMAction.FlatPersistence

/-!
# The three-carrier singlet carries no mean colour source

`FlatPersistence.flat_iff` shows the most persistent links are flat when nothing sources them.
This file supplies the missing half for a hadron: three carriers in the totally antisymmetric
colour state `ε_abc` (the singlet), all in one spatial mode, have zero expectation of every
traceless one-body colour operator on every carrier.

* `eps3`: the antisymmetric symbol on three colour indices.
* `eps_contract`: `Σ_{b,c} ε_abc ε_a'bc = 2 δ_aa'`.
* `singlet_mean_one`, `singlet_mean_two`, `singlet_mean_three`: for a traceless `T` acting on
  carrier 1, 2 or 3, `⟨ε| T |ε⟩ = 2 tr T = 0`.

With all three carriers in the same spatial mode, the mean colour charge density at a site is the
mode density times this expectation, and the mean colour current is the mode current times it, so
both vanish. Together with `flat_iff`, the persistent links inside the hadron carry no colour
field: the colour-magnetic correction to spin enters only through fluctuations, which cost toll.
This closes REVIEW A.1 at leading order; the fluctuation size would still need the gauge `β`.
-/

namespace PMAction.ColourSinglet
open Matrix

/-- The antisymmetric symbol `ε_abc`. -/
def eps3 : Fin 3 → Fin 3 → Fin 3 → ℂ := ![
  ![![0, 0, 0], ![0, 0, 1], ![0, -1, 0]],
  ![![0, 0, -1], ![0, 0, 0], ![1, 0, 0]],
  ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]]]

theorem eps_contract (a a' : Fin 3) :
    ∑ b, ∑ c, eps3 a b c * eps3 a' b c = if a = a' then 2 else 0 := by
  fin_cases a <;> fin_cases a' <;> simp [eps3, Fin.sum_univ_three] <;> norm_num

theorem trace_three (T : Matrix (Fin 3) (Fin 3) ℂ) : T.trace = T 0 0 + T 1 1 + T 2 2 := by
  simp [Matrix.trace, Fin.sum_univ_three]

/-- **Carrier 1.** -/
theorem singlet_mean_one (T : Matrix (Fin 3) (Fin 3) ℂ) (htr : T.trace = 0) :
    ∑ a, ∑ b, ∑ c, ∑ a', eps3 a b c * T a a' * eps3 a' b c = 0 := by
  rw [trace_three] at htr
  simp [eps3, Fin.sum_univ_three]
  linear_combination (2 : ℂ) * htr

/-- **Carrier 2.** -/
theorem singlet_mean_two (T : Matrix (Fin 3) (Fin 3) ℂ) (htr : T.trace = 0) :
    ∑ a, ∑ b, ∑ c, ∑ b', eps3 a b c * T b b' * eps3 a b' c = 0 := by
  rw [trace_three] at htr
  simp [eps3, Fin.sum_univ_three]
  linear_combination (2 : ℂ) * htr

/-- **Carrier 3.** -/
theorem singlet_mean_three (T : Matrix (Fin 3) (Fin 3) ℂ) (htr : T.trace = 0) :
    ∑ a, ∑ b, ∑ c, ∑ c', eps3 a b c * T c c' * eps3 a b c' = 0 := by
  rw [trace_three] at htr
  simp [eps3, Fin.sum_univ_three]
  linear_combination (2 : ℂ) * htr

end PMAction.ColourSinglet
