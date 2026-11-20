import PMFlavor.TransferGraph
import PMFlavor.VubSeriesPath
import PMFlavor.KronSeries
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Amplitude rules for the node-crossing transfers

`TransferGraph`: two of the three generation transfers cross the reference node, by two legs of
impedance `Z = α⁻¹` each, and they differ only by the wall their class sits on. The jump (class on
the other wall) enters and leaves the node; its amplitude is the series admittance of its path, two
legs and a unit boundary (`KronSeries`, `VubSeriesPath.vub_is_path`): `jump_eq_s13`.

This module writes down what each amplitude rule already in the library gives for the other node
crossing, the promotion (class on the reference's wall), so that each can be tested. Nothing is
fitted.

* `promoA`: one series rule for every node crossing, wall-blind. Then `promoA = jump`
  (`promoA_ratio`): the two node crossings are equal.
* `promoB`: the node is one end of the promotion (its hop starts inside the node's refresh), so the
  path is one leg and the boundary, `1/(Z + π)`. `promoB_ratio`: `promoB / jump` lies in
  `(1.97, 1.98)`.
* `promoC`: one leg read as a probability, as for a lepton-axis state (`NodeElimination.one_leg`):
  amplitude `√α`. `promoC_sq`: `promoC² = α`; `promoC_ratio_sq`: `(promoC / jump)²` lies in
  `(560, 561)`.

So the library's rules give `|promotion/jump| ∈ {1, ≈ 1.98, ≈ 23.7}`. Read out as `|V_cb|/|V_ub|`
(e8p's naming, `TransferGraph`), the comparison with measurement is in
`E8PConstants.CandidateTests` (`promo_rules_excluded`): all three are excluded. The wall must change
the amplitude by a factor the existing rules do not produce. The one
form in the library that reaches it, the removed unbased envelope candidate's refresh-tick envelope `env 1 / env (Δ − D)`, has
no schedule basis (REVIEW).
-/

noncomputable section
namespace PMFlavor.TransferAmplitude
open PMFlavor.CKM

/-- The jump: two node legs and a unit boundary in series. -/
def jump : ℝ := VubSeriesPath.seriesAdmittance [αinv, αinv, Real.pi]

/-- **The jump is `s₁₃`.** -/
theorem jump_eq_s13 : jump = s13 := VubSeriesPath.vub_is_path

/-- Rule A: the same series path for every node crossing. -/
def promoA : ℝ := jump

/-- Rule B: the node is one end; one leg and the boundary. -/
def promoB : ℝ := VubSeriesPath.seriesAdmittance [αinv, Real.pi]

/-- Rule C: one leg read as a probability `α`, amplitude `√α`. -/
def promoC : ℝ := Real.sqrt (1 / αinv)

lemma αinv_pos : 0 < αinv := by linarith [ai_bounds.1]

lemma jump_eq : jump = 1 / (2 * αinv + Real.pi) := by
  unfold jump VubSeriesPath.seriesAdmittance; simp only [List.sum_cons, List.sum_nil]; ring

lemma promoB_eq : promoB = 1 / (αinv + Real.pi) := by
  unfold promoB VubSeriesPath.seriesAdmittance; simp only [List.sum_cons, List.sum_nil]; ring

/-- **Rule A gives equal node crossings.** -/
theorem promoA_ratio : promoA / jump = 1 := by
  have h : 0 < jump := by rw [jump_eq]; have := Real.pi_pos; have := αinv_pos; positivity
  unfold promoA; exact div_self h.ne'

/-- **Rule B gives a ratio just under `2`.** -/
theorem promoB_ratio : 1.97 < promoB / jump ∧ promoB / jump < 1.98 := by
  have ha := ai_bounds
  have hp1 := Real.pi_gt_d4; have hp2 := Real.pi_lt_d4
  have h1 : 0 < αinv + Real.pi := by linarith
  have h2 : 0 < 2 * αinv + Real.pi := by linarith
  have e : promoB / jump = (2 * αinv + Real.pi) / (αinv + Real.pi) := by
    rw [promoB_eq, jump_eq]; field_simp
  rw [e]
  constructor
  · rw [lt_div_iff₀ h1]; nlinarith
  · rw [div_lt_iff₀ h1]; nlinarith

/-- **Rule C: `promoC² = α`.** -/
theorem promoC_sq : promoC ^ 2 = 1 / αinv := by
  unfold promoC; rw [Real.sq_sqrt (by have := αinv_pos; positivity)]

/-- **Rule C gives a ratio near `23.7`** (its square lies in `(560, 561)`). -/
theorem promoC_ratio_sq : 560 < (promoC / jump) ^ 2 ∧ (promoC / jump) ^ 2 < 561 := by
  have ha := ai_bounds
  have hp1 := Real.pi_gt_d4; have hp2 := Real.pi_lt_d4
  have hpos := αinv_pos
  have h2 : 0 < 2 * αinv + Real.pi := by linarith
  have e : (promoC / jump) ^ 2 = (2 * αinv + Real.pi) ^ 2 / αinv := by
    rw [div_pow, promoC_sq, jump_eq]; field_simp
  have z2l : (137.0359992 : ℝ) ^ 2 < αinv ^ 2 := by nlinarith
  have z2u : αinv ^ 2 < (137.0359993 : ℝ) ^ 2 := by nlinarith
  have zpl : (137.0359992 : ℝ) * 3.1415 < αinv * Real.pi := by nlinarith
  have zpu : αinv * Real.pi < (137.0359993 : ℝ) * 3.1416 := by nlinarith
  have p2l : (3.1415 : ℝ) ^ 2 < Real.pi ^ 2 := by nlinarith
  have p2u : Real.pi ^ 2 < (3.1416 : ℝ) ^ 2 := by nlinarith
  rw [e]
  constructor
  · rw [lt_div_iff₀ hpos]; nlinarith
  · rw [div_lt_iff₀ hpos]; nlinarith

end PMFlavor.TransferAmplitude
