import PMConstants.GravityAccounting
import PMConstants.CarrierRepresentation

/-!
# The gravity residual's boundary-storage term

`B_res = ν − s − α` with the proposed `s = χ/(σ − χ) = 2/3`. Newton's constant pins `s` directly.

* `storage_window`: if `(16 − s − α)α^{43/2}` lies in the CODATA window `(1.751770, 1.751849)·10⁻⁴⁵`,
  then `0.6662 < s < 0.6670`.
* `chi_over_k`: among `χ/k` with `k` natural, only `k = 3` lies in that window.
* `payload_weighted_excluded`: the payload-weighted `2η/3` lies below it, the same frame-versus-payload
  result as `GravityAccounting`.
* `storage_is_charge_quantum`: `2/3 = χ · (B − L per colour axis)`, the `1/3` forced by tracelessness
  in `CarrierRepresentation.bl_traceless`: the boundary's `χ = 2` units each store one colour-axis
  charge quantum. This identifies the `3` as the colour axes (`σ − χ`) rather than an independent
  count.
-/

noncomputable section
namespace PMConstants.BoundaryStorage
open PMConstants CertifiedConstants GravityAccounting

theorem storage_window {s : ℝ}
    (h : 1.751770e-45 < (16 - s - α) * α ^ ((43 : ℝ) / 2) ∧
      (16 - s - α) * α ^ ((43 : ℝ) / 2) < 1.751849e-45) :
    0.6662 < s ∧ s < 0.6670 := by
  have ha := alpha_bounds
  have hA := attenuation_bounds
  have hApos : 0 < α ^ ((43 : ℝ) / 2) := by linarith [hA.1]
  constructor
  · by_contra hc; push Not at hc
    have : (16 - s - α) * α ^ ((43 : ℝ) / 2) ≥ (16 - 0.6662 - 0.007297352563) * 1.143021965e-46 := by
      have h1 : 16 - s - α ≥ 16 - 0.6662 - 0.007297352563 := by linarith [ha.2]
      nlinarith [hA.1]
    norm_num at this; linarith [h.2]
  · by_contra hc; push Not at hc
    have : (16 - s - α) * α ^ ((43 : ℝ) / 2) ≤ (16 - 0.6670 - 0.007297352562) * 1.143021969e-46 := by
      have h1 : 16 - s - α ≤ 16 - 0.6670 - 0.007297352562 := by linarith [ha.1]
      have h0 : 0 ≤ 16 - s - α ∨ 16 - s - α < 0 := le_or_gt 0 _
      rcases h0 with h0 | h0
      · nlinarith [hA.2]
      · nlinarith [hA.2]
    norm_num at this; linarith [h.1]

theorem chi_over_k (k : ℕ) : ((0.6662 : ℚ) < 2 / k ∧ 2 / (k : ℚ) < 0.6670) ↔ k = 3 := by
  constructor
  · rintro ⟨h1, h2⟩
    rcases Nat.lt_or_ge k 3 with hk | hk
    · interval_cases k <;> revert h1 h2 <;> norm_num
    · rcases Nat.eq_or_lt_of_le hk with hk | hk
      · exact hk.symm
      · have hk4 : (4 : ℚ) ≤ k := by exact_mod_cast hk
        have : 2 / (k : ℚ) ≤ 1/2 := by
          rw [div_le_iff₀ (by linarith)]; linarith
        linarith
  · rintro rfl; norm_num

theorem payload_weighted_excluded : 2 * overhead / 3 < (0.6662 : ℝ) := by
  norm_num [overhead]

theorem storage_is_charge_quantum : (2 : ℚ) * (1/3) = 2/3 ∧
    ∀ a b : ℚ, 3 * a + b = 0 → b = -1 → 2 * a = 2/3 := by
  refine ⟨by norm_num, fun a b htr hl => ?_⟩
  have := (CarrierRepresentation.bl_traceless a b htr hl).1
  rw [this]; norm_num

end PMConstants.BoundaryStorage
