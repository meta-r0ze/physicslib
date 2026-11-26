import PersistenceMechanics.ExponentialFilter
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
# Constant hazard, parallel rates and mean life

Sum the rates of parallel channels. For a positive total rate, mean life
is the integral of survival. At zero rate, survival stays at one.
-/

noncomputable section
namespace PersistenceMechanics.Rates

open ExponentialFilter

/-- Survival with a constant hazard. -/
def survive (rate time : ℝ) : ℝ := survival (fun _ => rate) time

theorem survive_eq (rate time : ℝ) : survive rate time = Real.exp (-rate * time) :=
  survival_const rate time

theorem survival_const_eq_survive (rate time : ℝ) :
    survival (fun _ => rate) time = survive rate time := rfl

/-- Add the hazards of parallel channels. -/
def parallelRate (rates : List ℝ) : ℝ := rates.sum

@[simp] theorem parallelRate_nil : parallelRate [] = 0 := rfl

@[simp] theorem parallelRate_cons (r : ℝ) (rs : List ℝ) :
    parallelRate (r :: rs) = r + parallelRate rs := rfl

/-- Finite mean life. A zero hazard gives indefinite survival. -/
def meanLife (rate : ℝ) (_positive : 0 < rate) : ℝ := 1 / rate

theorem meanLife_pos {rate : ℝ} (h : 0 < rate) : 0 < meanLife rate h :=
  one_div_pos.mpr h

theorem meanLife_antitone {r s : ℝ} (hr : 0 < r) (h : r ≤ s) :
    meanLife s (lt_of_lt_of_le hr h) ≤ meanLife r hr :=
  one_div_le_one_div_of_le hr h

/-- Mean life is the integral of constant-hazard survival. -/
theorem meanLife_eq_integral {r : ℝ} (hr : 0 < r) :
    meanLife r hr = ∫ t : ℝ in Set.Ioi (0 : ℝ), Real.exp (-r * t) := by
  rw [integral_exp_mul_Ioi (a := -r) (by linarith) 0]
  unfold meanLife
  rw [mul_zero, Real.exp_zero]
  field_simp

theorem meanLife_eq_survival_integral {r : ℝ} (hr : 0 < r) :
    meanLife r hr = ∫ t : ℝ in Set.Ioi (0 : ℝ), survival (fun _ => r) t := by
  simp_rw [survival_const]
  exact meanLife_eq_integral hr

def halfTime (rate : ℝ) (h : 0 < rate) : ℝ := meanLife rate h * Real.log 2

theorem positive (rate time : ℝ) : 0 < survive rate time := by rw [survive_eq]; exact Real.exp_pos _

theorem bounded {rate time : ℝ} (hr : 0 ≤ rate) (ht : 0 ≤ time) :
    0 < survive rate time ∧ survive rate time ≤ 1 := by
  refine ⟨positive _ _, ?_⟩
  rw [survive_eq]
  exact Real.exp_le_one_iff.mpr (by nlinarith)

theorem memoryless (rate t u : ℝ) : survive rate (t+u) = survive rate t * survive rate u := by
  simp only [survive_eq, ← Real.exp_add]
  congr 1
  ring

theorem competing_hazards (a b t : ℝ) : survive (a+b) t = survive a t * survive b t := by
  simp only [survive_eq, ← Real.exp_add]
  congr 1
  ring

theorem zero_rate (t : ℝ) : survive 0 t = 1 := by simp [survive_eq]

theorem at_time_constant {rate : ℝ} (hr : 0 < rate) :
    survive rate (meanLife rate hr) = Real.exp (-1) := by
  rw [survive_eq]
  unfold meanLife
  congr 1
  field_simp

theorem at_half_time {rate : ℝ} (hr : 0 < rate) :
    survive rate (halfTime rate hr) = 1 / 2 := by
  have he : -rate * halfTime rate hr = -Real.log 2 := by
    unfold halfTime meanLife
    field_simp
  rw [survive_eq, he, Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

end PersistenceMechanics.Rates
