import PMElementaryParticles.KoideSplit
import PersistenceMechanics.LawSelection

/-!
# Koide from the Selection Principle, with one named premise

`KoideSplit.koide_iff_fair`: `Q = 2/3` iff the two-outcome record
"generation-symmetric / symmetry-breaking" is a fair coin, i.e. the breaking
share of the amplitude norm is `1/2`.

`PersistenceMechanics.LawSelection`: on any finite outcome set, the law that
persists (least average cost rate, `averageRate_eq_iff`; or least worst-case
rate, `worstRate_eq_iff`) is the uniform law.

**Named premise (`GenerationRecord`).** The generation record has two outcomes,
symmetric and breaking, and its law is the norm share
(`1 − breakingShare v`, `breakingShare v`).

Under that premise, the persisting law gives `Q = 2/3`
(`koide_of_selected_average`, `koide_of_selected_worst`). Nothing else is
assumed: no data and no fitted number. What remains open is the premise
itself: that the substrate records a protocol's generation as this one bit.
-/

noncomputable section

namespace PMElementaryParticles.KoideSelection

open PMElementaryParticles.KoideSplit PersistenceMechanics.LawSelection

/-- The two-outcome generation law: outcome `0` symmetric, `1` breaking. -/
def generationLaw (v : Fin 3 → ℝ) : Fin 2 → ℝ :=
  ![1 - breakingShare v, breakingShare v]

theorem singlet_pos (v : Fin 3 → ℝ) (h : total v ≠ 0) : 0 < normSq (singlet v) := by
  rw [normSq_singlet]; positivity

theorem doublet_nonneg (v : Fin 3 → ℝ) : 0 ≤ normSq (doublet v) :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- The generation law is a positive probability law when the state is not
fully symmetric. -/
theorem generationLaw_pos (v : Fin 3 → ℝ) (h : total v ≠ 0)
    (hd : 0 < normSq (doublet v)) : PosLaw (generationLaw v) := by
  have hs := singlet_pos v h
  have hn : normSq v = normSq (singlet v) + normSq (doublet v) := normSq_split v
  have hlt : breakingShare v < 1 := by
    rw [breakingShare, hn, div_lt_one (by linarith)]; linarith
  have hgt : 0 < breakingShare v := by
    rw [breakingShare, hn]; positivity
  refine ⟨fun ω => ?_, ?_⟩
  · fin_cases ω <;> simp [generationLaw] <;> linarith
  · simp [generationLaw, Fin.sum_univ_two]

theorem fair_of_uniform (v : Fin 3 → ℝ) (hu : generationLaw v = uniform) :
    breakingShare v = 1 / 2 := by
  have := congrFun hu 1
  simpa [generationLaw, uniform] using this

/-- **Koide from the persisting law (average-rate reading).** -/
theorem koide_of_selected_average (v : Fin 3 → ℝ) (h : total v ≠ 0)
    (hd : 0 < normSq (doublet v))
    (hsel : averageRate (generationLaw v) = Real.log (Fintype.card (Fin 2))) :
    koideQ v = 2 / 3 :=
  (koide_iff_fair v h).2
    (fair_of_uniform v ((averageRate_eq_iff (generationLaw_pos v h hd)).1 hsel))

/-- **Koide from the persisting law (worst-case reading).** -/
theorem koide_of_selected_worst (v : Fin 3 → ℝ) (h : total v ≠ 0)
    (hd : 0 < normSq (doublet v))
    (hsel : worstRate (generationLaw v) = Real.log (Fintype.card (Fin 2))) :
    koideQ v = 2 / 3 :=
  (koide_iff_fair v h).2
    (fair_of_uniform v ((worstRate_eq_iff (generationLaw_pos v h hd)).1 hsel))

end PMElementaryParticles.KoideSelection

end
