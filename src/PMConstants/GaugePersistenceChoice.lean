import PMConstants.GaugeTraceNormalization
import PMConstants.General.WorkSelection
import PMConstants.SelectedColourLoad

/-! What persistence selects once work has an operational meaning.
The two queues are weak/hypercharge comparison-repair queues under a common
unit-capacity pool. Their weights include the packet indices. This is not a
claim that the two gauge sectors actually share this serial pool. Raw-work
floors and throughput maximization are explicit additional hypotheses. -/
noncomputable section
namespace PMConstants.GaugePersistenceChoice
open Finset General.WorkSelection GaugeTraceNormalization

/-- A positive common rescaling of the existing reference return-cost
functional preserves its unique uniform minimizer. Reference-law selection
therefore cannot determine that prefactor. This is a common prefactor result;
it does not assume that arbitrary label-dependent rescalings cancel. -/
theorem scaled_reference_minimizer (μ : General.ReferenceCapacity.Grid → ℝ)
    (hμ : PersistenceMechanics.LawSelection.PosLaw μ) {c : ℝ} (hc : 0 < c) :
    (∀ ν : General.ReferenceCapacity.Grid → ℝ,
      PersistenceMechanics.LawSelection.PosLaw ν →
      c*PersistenceMechanics.LawSelection.averageRate μ ≤
        c*PersistenceMechanics.LawSelection.averageRate ν) ↔
      μ=PersistenceMechanics.LawSelection.uniform := by
  constructor
  · intro h
    apply SelectedColourLoad.average_minimizer_uniform μ hμ
    intro ν hν
    exact (mul_le_mul_iff_right₀ hc).mp (h ν hν)
  · intro h ν hν
    rw [h,PersistenceMechanics.LawSelection.uniform_averageRate]
    exact mul_le_mul_of_nonneg_left (PersistenceMechanics.LawSelection.averageRate_ge hν) hc.le

/-- Index-weighted demand from positive raw comparison multipliers. -/
def work (kW kY : ℝ) : Fin 2 → ℝ :=
  ![2*kW*43,(10/3)*kY*(footprint-43)]

lemma total (kW kY : ℝ) :
    (∑ i, work kW kY i)=86*kW+(10/3)*kY*(footprint-43) := by
  simp [work,Fin.sum_univ_succ]
  ring

lemma work_pos {kW kY : ℝ} (hw : 0 < kW) (hy : 0 < kY) :
    ∀ i, 0 < work kW kY i := by
  intro i
  fin_cases i <;> norm_num [work,footprint,overhead] <;> positivity

lemma total_pos {kW kY : ℝ} (hw : 0 < kW) (hy : 0 < kY) :
    0 < ∑ i, work kW kY i :=
  sum_pos (fun i _ => work_pos hw hy i) univ_nonempty

/-- Persistence at some positive rate alone permits every positive pair.
The same queue conservation and capacity rules hold in all these witnesses. -/
theorem all_positive_persist {kW kY : ℝ} (hw : 0 < kW) (hy : 0 < kY) :
    ∃ r : ℝ, 0 < r ∧ Feasible (work kW kY) r := by
  refine ⟨1/(∑ i, work kW kY i),by positivity [total_pos hw hy],?_⟩
  exact (maximum_rate _ (fun i => (work_pos hw hy i).le) (total_pos hw hy)).1

/-- Both the raw interpretation and a ratio-compatible one persist. Thus
bounded queues and conservation alone do not choose the manuscript ratio. -/
theorem persistent_alternatives :
    (∃ r : ℝ, 0 < r ∧ Feasible (work 1 1) r) ∧
    (∃ r : ℝ, 0 < r ∧ Feasible (work (5/3) 1) r) ∧
    adjustedMixing 1 1 ≠ clockRatio ∧ adjustedMixing (5/3) 1=clockRatio := by
  refine ⟨all_positive_persist (by norm_num) (by norm_num),
    all_positive_persist (by norm_num) (by norm_num),?_,?_⟩ <;>
    norm_num [adjustedMixing,clockRatio,footprint,overhead]

/-- Under the explicit primitive floor k_i ≥ 1, fastest sustainable operation
uses the unadjusted raw weights. This optimization is stronger than persistence. -/
theorem raw_rate_bound {kW kY r : ℝ} (hw : 1 ≤ kW) (hy : 1 ≤ kY)
    (hp : Feasible (work kW kY) r) : r ≤ 129/75554 := by
  have hc := capacity_bound hp
  have hd : (75554/129 : ℝ) ≤ ∑ i, work kW kY i := by
    rw [total]; norm_num [footprint,overhead]; linarith
  have hm := mul_le_mul_of_nonneg_left hd hp.1
  linarith

theorem raw_optimum : Feasible (work 1 1) (129/75554) := by
  apply (feasible_iff _ (fun i => (work_pos (by norm_num) (by norm_num) i).le) _).mpr
  norm_num [work,Fin.sum_univ_succ,footprint,overhead]

/-- Equality in the rate bound excludes all additional raw work. -/
theorem raw_optimum_unique {kW kY : ℝ} (hw : 1 ≤ kW) (hy : 1 ≤ kY)
    (hp : Feasible (work kW kY) (129/75554)) : kW=1 ∧ kY=1 := by
  have hc := capacity_bound hp
  rw [total] at hc
  norm_num [footprint,overhead] at hc
  constructor <;> linarith

/-- Recovering the manuscript ratio while respecting the raw floors requires
extra weak work. It cannot be obtained by deleting required hypercharge work. -/
theorem target_requires_extra_weak {kW kY : ℝ} (hw : 1 ≤ kW) (hy : 1 ≤ kY)
    (ht : adjustedMixing kW kY=clockRatio) : 5/3 ≤ kW := by
  have he := (compensation_iff (by linarith : 0 < kW) (by linarith : 0 < kY)).mp ht
  linarith

theorem target_rate_bound {kW kY r : ℝ} (hw : 1 ≤ kW) (hy : 1 ≤ kY)
    (ht : adjustedMixing kW kY=clockRatio) (hp : Feasible (work kW kY) r) :
    r ≤ 43/27650 := by
  have hk := target_requires_extra_weak hw hy ht
  have hd : (27650/43 : ℝ) ≤ ∑ i, work kW kY i := by
    rw [total]; norm_num [footprint,overhead]; linarith
  have hc := capacity_bound hp
  have hm := mul_le_mul_of_nonneg_left hd hp.1
  linarith

theorem target_optimum : Feasible (work (5/3) 1) (43/27650) := by
  apply (feasible_iff _ (fun i => (work_pos (by norm_num) (by norm_num) i).le) _).mpr
  norm_num [work,Fin.sum_univ_succ,footprint,overhead]

/-- With this common pool and these raw-work floors, the ratio-compatible
optimum is strictly slower than the unconstrained raw optimum. -/
theorem target_strictly_slower : (43/27650 : ℝ) < 129/75554 := by norm_num

/-- The ordering survives any common nonnegative baseline per operation;
adding shared colour/reference work cannot reverse this particular comparison. -/
theorem common_baseline_order (b : ℝ) (hb : 0 ≤ b) :
    1/(b+∑ i, work (5/3) 1 i) < 1/(b+∑ i, work 1 1 i) := by
  apply one_div_lt_one_div_of_lt
  · have ht := total_pos (kW := (1 : ℝ)) (kY := (1 : ℝ)) (by norm_num) (by norm_num)
    linarith
  · rw [total,total]
    norm_num [footprint,overhead]

/-- With no primitive floor, even fastest-rate selection is ill-posed:
scaling both raw costs down preserves their mixing ratio and increases the
maximum sustainable rate. The scaling is a mathematical family of workload
contracts, not an executable way to make E8 events cheaper. -/
theorem no_floor_improvement {kW kY : ℝ} (hw : 0 < kW) (hy : 0 < kY) :
    adjustedMixing (kW/2) (kY/2)=adjustedMixing kW kY ∧
    1/(∑ i, work kW kY i) < 1/(∑ i, work (kW/2) (kY/2) i) := by
  constructor
  · unfold adjustedMixing
    have he : 2*(kW/2)*43+(10/3)*(kY/2)*(footprint-43)=
        (2*kW*43+(10/3)*kY*(footprint-43))/2 := by ring
    rw [he]
    field_simp
  · apply one_div_lt_one_div_of_lt (total_pos (by positivity) (by positivity))
    have hp := total_pos hw hy
    rw [total] at hp
    rw [total,total]
    nlinarith

/-- If ledger values are effective stiffness instead, the matching raw
multipliers violate both raw floors. The floor contract must not be silently
transferred between the two different meanings of a ledger. -/
theorem effective_reading_factors :
    2*(1/2 : ℝ)*43=43 ∧ (10/3)*(3/10 : ℝ)*(footprint-43)=footprint-43 ∧
    (1/2 : ℝ)<1 ∧ (3/10 : ℝ)<1 := by
  constructor
  · norm_num
  constructor
  · ring
  norm_num

end PMConstants.GaugePersistenceChoice
