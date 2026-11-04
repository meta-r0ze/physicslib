import PMAction.RestorationResponse
import PMConstants.RepairBudget

/-!
# The reference's real drift family under Paper II's reset response

Paper II's `RestorationResponse` (Codex) derives the comparison response of any exact unitary
reset and warns that its trace theorem counts *complex* coordinate modes, while Paper III's
reference tangent has *three real* directions inside two complex modes. This file evaluates the
response on the actual reference tangent of the coherent restorer (`CoherentBudget`) and shows
which count the response sees.

* `tangent_nsq`: the tangent embedding `d ↦ (i a, i z)` is an isometry, `‖tangent d‖² = a² + |z|²`.
* `drift_response`: the coherent exchange on (reference + tangent, reference) responds
  `‖d‖²/2` (Paper II `prepared_exchange_response`): every unit drift direction responds the same,
  whatever its direction. This is frame independence realized by the readout rather than assumed.
* `real_family_total`: over the three unit real drift directions `(1,0)`, `(0,1)`, `(0,i)` the
  total is `3/2`, three times one direction's response.
* `complex_basis_total`: over the two complex coordinate modes of the live doublet the total is
  `1` (Paper II `basis_response_trace` at `n = Fin 2`): two units.
* `count_by_lambda`: in units of one direction's response, the real family gives `3` and the
  complex basis `2`; `(2 − 1/43)/23` lies outside the `λ` window, `(3 − 1/43)/23` inside.

So under the common response, the budget's "one unit per restored direction" is "one direction's
response per unit drift test", and the test family has to be the real drift directions (the
electroweak drifts, `RepairBudget.drift_covers_neighborhood`), not the complex coordinates.
Premises (as Codex's note says): that the maintained disturbance family is the real drift
family, unit-normalized per test, and that the budget is this summed response in units of one
test. This is a net-response readout; it is not a primitive event ledger
(`RestorationResponse.roundtrip_instruction_price`).
-/

noncomputable section
namespace PMConstants.TangentResponse
open Matrix PMAction CommonResponse

abbrev D := ℝ × ℂ
abbrev Doublet := Fin 2 → ℂ

def reference : Doublet := ![1, 0]
def tangent (d : D) : Doublet := ![Complex.I * (d.1 : ℂ), Complex.I * d.2]

theorem tangent_nsq (d : D) : nsq (tangent d) = d.1 ^ 2 + Complex.normSq d.2 := by
  unfold nsq tangent
  simp [dotProduct, Fin.sum_univ_two, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

local notation "X" => BranchMixerSynthesis.exchange (n := Fin 2)

/-- **Every unit drift responds the same.** -/
theorem drift_response (d : D) :
    stateFlag X (Sum.elim (reference + tangent d) reference) = (d.1 ^ 2 + Complex.normSq d.2) / 2 := by
  rw [RestorationResponse.prepared_exchange_response, add_sub_cancel_left, tangent_nsq]

/-- **The real drift family totals three directions' response.** -/
theorem real_family_total :
    stateFlag X (Sum.elim (reference + tangent (1, 0)) reference) +
      stateFlag X (Sum.elim (reference + tangent (0, 1)) reference) +
      stateFlag X (Sum.elim (reference + tangent (0, Complex.I)) reference) = 3 * (1 / 2) := by
  rw [drift_response, drift_response, drift_response]
  simp [Complex.normSq_apply]; norm_num

/-- **The complex coordinate basis totals two.** -/
theorem complex_basis_total :
    (∑ a : Fin 2, stateFlag X (RestorationResponse.prepare (r := Fin 2) (Pi.single a 1))) =
      2 * (1 / 2) := by
  rw [RestorationResponse.basis_response_trace X CoherentRecordRestoration.exchange_unitary
    RestorationResponse.exchange_resets, RestorationResponse.reset_gain X
    RestorationResponse.exchange_resets]
  simp

/-- **The count λ keeps is the real family's.** -/
theorem count_by_lambda :
    ¬ ((0.1286 : ℝ) < (2 - 1/43) / 23) ∧ (0.1286 : ℝ) < (3 - 1/43) / 23 ∧ (3 - 1/43 : ℝ) / 23 < 0.1300 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

end PMConstants.TangentResponse
