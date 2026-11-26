import PMConstants.Values

/-!
# Fermion mass-law measured pulls (moved from the PMConstants leaves)

The substrate selects law A (the vacuum value sets the detuning **cost** `δ² ∝ v`) with no
measured input, twice over: the event law prices a displacement by its square
(`PMConstants.FermionMassLaw.massA_event_priced`), and Economy admits exactly one doublet
insertion (`PMConstants.VevEntry.economy_law_A`). The measured comparisons live here.

The coupling modifier is `κ = (v/m) dm/dv`; the Standard Model value is `1`. CMS (2022) measures
`κ_τ = 0.92 ± 0.08`.

* `tau_pull`: for a light fermion law A's pull is at most `1.0σ` and law B's exceeds `13σ`.
* `link_pull`: the inter-wall-link reading gives a negative `κ`, more than `11σ` away.
-/

namespace E8PConstants.FermionLawPulls

open PMConstants.Values

/-- Law A against law B on the measured `κ_τ`. -/
theorem tau_pull {m : ℝ} (h0 : 0 ≤ m) (h1 : m ≤ 1/100) :
    |(m + 1) / (2 * m + 1) - 0.92| / 0.08 ≤ 1.0 ∧
      13 < |2 * (m + 1) / (2 * m + 1) - 0.92| / 0.08 := by
  obtain ⟨a1, a2⟩ := kappa_cost_light h0 h1
  obtain ⟨b1, b2⟩ := kappa_amp_light h0 h1
  constructor
  · rw [abs_of_pos (by linarith), div_le_iff₀ (by norm_num)]; linarith
  · rw [abs_of_pos (by linarith), lt_div_iff₀ (by norm_num)]; linarith

/-- The inter-wall-link reading against the measured `κ_τ`. -/
theorem link_pull (δ y : ℝ) (hy : 0 < y) (hδ : δ ≠ 0) :
    11 < |y / (2 * lightGapSq δ y) * (y - y * (y ^ 2 + 2 * δ ^ 2) / rr δ y) - 0.92| / 0.08 := by
  have h := link_kappa_neg δ y hy hδ
  rw [abs_of_neg (by linarith), lt_div_iff₀ (by norm_num)]
  linarith

end E8PConstants.FermionLawPulls
