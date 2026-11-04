import PMConstants.ReferenceDirections
import PMConstants.RegulatoryBudget

/-!
# Equal regulatory gain from maximin, and the count 23 from the measured coupling

`RegulatoryBudget` takes equal restoring gain on the regulatory labels as given and bounds it by
`(B - 1/43)/23`. Two steps here.

**Equal gain is the maximin allocation.** Let `n` labels receive nonnegative gains `g i` with
`Σ g + s ≤ B`.

* `min_gain_le`: some label gets at most `(B - s)/n`.
* `maximin_attained`: equal gains `(B - s)/n` are feasible and give every label that margin.
* `maximin_forces_equal`: any feasible allocation whose least gain reaches `(B - s)/n` is the equal
  one.

So maximizing the worst label's restoring margin (the persistence maximin of the framework's
selection) selects equal gains; `RegulatoryBudget.Feasible`'s uniform form is a consequence.

**The count is pinned once the budget is.**

* `count_unique`: with `B = 3` (`ReferenceDirections.budget_is_moved_count`) and the clock credit
  `1/43`, only `N = 23` puts `(3 - 1/43)/N` within `3σ` of the measured `λ`.
* `pair_not_pinned`: the pair `(B, N)` is not fixed by `λ` alone: `(7, 54)` also fits. The budget
  has to come from elsewhere, and the moved-direction count supplies it.

**The unit per direction.** `full_restore_trace`: a restoring map that returns every displacement
of the reference in one step is the identity on the displacement space, so its total gain (trace)
is `3`. This is the same additive gain accounting as the label side `Σ g`. The budget premise of
`ReferenceDirections` thus becomes: the scalar fully restores each displacement within one update,
with total gain counted additively.

What remains: identifying the 23 labels as `ν + σ + χ` (channels, wires, boundary units) rather
than another sum equal to 23; `ScalarAccounting` already excludes counting the channels as payload.
-/

noncomputable section
namespace PMConstants.RegulatoryMaximin
open Finset

variable {n : ℕ}

theorem min_gain_le (hn : 0 < n) (g : Fin n → ℝ) {s B : ℝ} (hb : ∑ i, g i + s ≤ B) :
    ∃ i, g i ≤ (B - s) / n := by
  by_contra h
  push Not at h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have : ∑ _i : Fin n, (B - s) / n < ∑ i, g i :=
    Finset.sum_lt_sum_of_nonempty ⟨⟨0, hn⟩, mem_univ _⟩ (fun i _ => h i)
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_cancel₀ _ hn'.ne'] at this
  linarith

theorem maximin_attained (hn : 0 < n) {s B : ℝ} (hs : s ≤ B) :
    (∀ i : Fin n, 0 ≤ (fun _ => (B - s) / n) i) ∧ ∑ _i : Fin n, (B - s) / n + s ≤ B := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨fun _ => div_nonneg (by linarith) hn'.le, ?_⟩
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_cancel₀ _ hn'.ne']
  linarith

/-- **Maximin forces equal gains.** -/
theorem maximin_forces_equal (hn : 0 < n) (g : Fin n → ℝ) {s B : ℝ} (hb : ∑ i, g i + s ≤ B)
    (hmin : ∀ i, (B - s) / n ≤ g i) : ∀ i, g i = (B - s) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  intro i
  by_contra hne
  have hlt : (B - s) / n < g i := lt_of_le_of_ne (hmin i) (Ne.symm hne)
  have : ∑ _j : Fin n, (B - s) / n < ∑ j, g j :=
    Finset.sum_lt_sum (fun j _ => hmin j) ⟨i, mem_univ _, hlt⟩
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_cancel₀ _ hn'.ne'] at this
  linarith

/-- **The measured coupling pins the count to 23.** -/
theorem count_unique (N : ℕ) :
    ((0.1286 : ℚ) < (3 - 1/43) / N ∧ (3 - 1/43) / N < (0.1300 : ℚ)) ↔ N = 23 := by
  constructor
  · rintro ⟨h1, h2⟩
    have hN : (0 : ℚ) < N := by
      by_contra h; push Not at h
      have : (N : ℚ) = 0 := le_antisymm h (Nat.cast_nonneg N)
      rw [this] at h1; norm_num at h1
    rw [lt_div_iff₀ hN] at h1
    rw [div_lt_iff₀ hN] at h2
    have a : (22 : ℚ) < N := by linarith
    have b : (N : ℚ) < 24 := by linarith
    have : 22 < N := by exact_mod_cast a
    have : N < 24 := by exact_mod_cast b
    omega
  · rintro rfl; norm_num

/-- **One unit per moved direction is the trace of full restoration.** A restoring map on the
displacement space that returns every displacement in one step is the identity, and its total
gain (trace) is the number of moved directions. -/
theorem full_restore_trace (K : (ℝ × ℂ) →ₗ[ℝ] (ℝ × ℂ)) (hK : ∀ d, K d = d) :
    LinearMap.trace ℝ (ℝ × ℂ) K = 3 := by
  have : K = LinearMap.id := LinearMap.ext hK
  rw [this, LinearMap.trace_id, ReferenceDirections.displacement_dim]; norm_num

theorem pair_not_pinned :
    (0.1286 : ℚ) < (7 - 1/43) / 54 ∧ (7 - 1/43) / 54 < (0.1300 : ℚ) := by norm_num

end PMConstants.RegulatoryMaximin
