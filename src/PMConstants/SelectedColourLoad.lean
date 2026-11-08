import PMConstants.ColourGeometricLoad
import PMConstants.SelectedAvailability

/-! Close the conditional selection-to-colour chain for an arbitrary positive
reference law. Minimizing the specified return-cost functional is an explicit
hypothesis; its physical realization and the work-density interpretation are
not inferred merely from finiteness or from naming the uniform law selected. -/
noncomputable section
namespace PMConstants.SelectedColourLoad
open Finset ColourGeometricLoad
open PMConstants.General.ReferenceCapacity
open PersistenceMechanics.LawSelection

/-- A positive reference law minimizing the supplied average return cost must
be uniform. The competitor uniform law is included in the stated domain. -/
theorem average_minimizer_uniform (μ : Grid → ℝ) (hμ : PosLaw μ)
    (hopt : ∀ ν : Grid → ℝ, PosLaw ν → averageRate μ ≤ averageRate ν) : μ=uniform := by
  apply (averageRate_eq_iff hμ).mp
  apply le_antisymm
  · simpa only [uniform_averageRate] using hopt uniform uniform_law
  · exact averageRate_ge hμ

theorem worst_minimizer_uniform (μ : Grid → ℝ) (hμ : PosLaw μ)
    (hopt : ∀ ν : Grid → ℝ, PosLaw ν → worstRate μ ≤ worstRate ν) : μ=uniform := by
  apply (worstRate_eq_iff hμ).mp
  apply le_antisymm
  · have hu : worstRate (uniform : Grid → ℝ)=Real.log (Fintype.card Grid) :=
      (worstRate_eq_iff uniform_law).mpr rfl
    simpa only [hu] using hopt uniform uniform_law
  · exact worstRate_ge hμ

def directionMass (μ : Grid → ℝ) (d : Fin 4) : ℝ := ∑ t : Fin PMSubstrate.E8Values.Delta, μ (d,t)

lemma direction_mass_normalized (μ : Grid → ℝ) (hμ : PosLaw μ) :
    (∑ d, directionMass μ d)=1 := by
  simpa only [directionMass,Fintype.sum_prod_type] using hμ.2

lemma uniform_direction : ∀ d, directionMass (uniform : Grid → ℝ) d=1/4 := by
  intro d
  norm_num [directionMass,uniform,Grid]

/-- The averaged geometric colour weights follow from the actual minimizer,
not from substituting the uniform definition for an unspecified physical law. -/
theorem selected_axis (μ : Grid → ℝ) (hμ : PosLaw μ)
    (hsel : μ=uniform) (a : Fin 3) : meanAxis (directionMass μ) a=4*overhead := by
  exact (target_iff_uniform_directions (directionMass μ) (direction_mass_normalized μ hμ)).mpr
    (by rw [hsel]; exact uniform_direction) a

theorem average_selected_axis (μ : Grid → ℝ) (hμ : PosLaw μ)
    (hopt : ∀ ν : Grid → ℝ, PosLaw ν → averageRate μ ≤ averageRate ν) (a : Fin 3) :
    meanAxis (directionMass μ) a=4*overhead :=
  selected_axis μ hμ (average_minimizer_uniform μ hμ hopt) a

theorem worst_selected_axis (μ : Grid → ℝ) (hμ : PosLaw μ)
    (hopt : ∀ ν : Grid → ℝ, PosLaw ν → worstRate μ ≤ worstRate ν) (a : Fin 3) :
    meanAxis (directionMass μ) a=4*overhead :=
  selected_axis μ hμ (worst_minimizer_uniform μ hμ hopt) a

/-- A conditional minimum-cost law supplies the desired colour aggregate;
it does not resolve the distinct raw-versus-index-weighted gauge normalization. -/
theorem selected_colour_total (μ : Grid → ℝ) (hμ : PosLaw μ)
    (hopt : ∀ ν : Grid → ℝ, PosLaw ν → worstRate μ ≤ worstRate ν) :
    (∑ a : Fin 3, meanAxis (directionMass μ) a)=12*overhead := by
  simp_rw [worst_selected_axis μ hμ hopt]
  simp
  ring

end PMConstants.SelectedColourLoad
