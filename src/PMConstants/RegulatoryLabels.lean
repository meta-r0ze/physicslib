import PMConstants.RegulatoryMaximin
import PMConstants.ReferenceRestoration

/-!
# The 23 regulatory labels are the coordinates of a link hop

The scalar is the inter-sector link (`SectorLinks`, `ReferenceLink`), and it regulates the
reference (`ReferenceDirections`). Paper III's map pillar indexes an interaction aperture by a
channel (`ν = 16`), an internal generator wire (`σ = 5`) and a boundary unit (`χ = 2`). So a hop is
a triple `(c, w, b)`, and its regulatory labels are the coordinate values `Label = Fin 16 ⊕ Fin 5 ⊕
Fin 2`.

**Which labels must be regulated.** To first order (the linear response already used for the
restorer), a hop's deviation is the sum of its coordinates' deviations,
`δ(c, w, b) = d(c) + d(w) + d(b)`. Regulating a label set `S` resets `d` on `S`.
* `restores_iff`: every first-order displacement is removed on every hop exactly when `S` contains
  all labels. Conservation therefore requires all of them; leaving out any one label leaves the
  displacement concentrated on it (`missing_label_fails`).
* `label_count`: there are `ν + σ + χ = 23` labels.
* `joint_count`: regulating joint configurations instead would need `16 · 5 · 2 = 160` labels.
  Economy prefers the coordinates, since they already suffice. `joint_excluded`: `N = 160` is also
  far outside the measured `λ` (`RegulatoryMaximin.count_unique` admits only `23`).

Together with `ReferenceRestoration.unique_decomposition` (only `ν + σ + χ` sums to 23), the count
and its identification follow from the hop's coordinates. Premises: a hop is indexed by
(channel, wire, boundary unit), and its deviation is first order in their deviations.
-/

noncomputable section
namespace PMConstants.RegulatoryLabels

abbrev Label := Fin 16 ⊕ Fin 5 ⊕ Fin 2
abbrev Hop := Fin 16 × Fin 5 × Fin 2

/-- First-order deviation of a hop from per-label deviations. -/
def deviation (d : Label → ℝ) (h : Hop) : ℝ :=
  d (.inl h.1) + d (.inr (.inl h.2.1)) + d (.inr (.inr h.2.2))

/-- Regulating the labels in `S` resets their deviations. -/
def regulate (S : Finset Label) (d : Label → ℝ) : Label → ℝ :=
  fun x => if x ∈ S then 0 else d x

/-- A hop through a given label. -/
def hopThrough : Label → Hop
  | .inl c => (c, 0, 0)
  | .inr (.inl w) => (0, w, 0)
  | .inr (.inr b) => (0, 0, b)

lemma indicator_deviation (x : Label) :
    deviation (fun y => if y = x then 1 else 0) (hopThrough x) = 1 := by
  rcases x with c | w | b <;> simp [deviation, hopThrough]

/-- **Leaving out a label leaves a displacement.** -/
theorem missing_label_fails (S : Finset Label) (x : Label) (hx : x ∉ S) :
    deviation (regulate S fun y => if y = x then 1 else 0) (hopThrough x) = 1 := by
  have h : regulate S (fun y => if y = x then 1 else 0) = fun y => if y = x then 1 else 0 := by
    funext y; by_cases hy : y = x
    · subst hy; simp [regulate, hx]
    · simp [regulate, hy]
  rw [h, indicator_deviation]

/-- **All labels are required, and they suffice.** -/
theorem restores_iff (S : Finset Label) :
    (∀ d h, deviation (regulate S d) h = 0) ↔ S = Finset.univ := by
  constructor
  · intro hS
    ext x; simp only [Finset.mem_univ, iff_true]
    by_contra hx
    have := hS (fun y => if y = x then 1 else 0) (hopThrough x)
    rw [missing_label_fails S x hx] at this; norm_num at this
  · rintro rfl d h; simp [deviation, regulate]

theorem label_count : Fintype.card Label = 16 + 5 + 2 ∧ Fintype.card Label = 23 := by
  simp

theorem joint_count : Fintype.card Hop = 160 := by simp

theorem joint_excluded :
    ¬ ((0.1286 : ℚ) < (3 - 1/43) / (160 : ℕ) ∧ (3 - 1/43) / (160 : ℕ) < (0.1300 : ℚ)) := by
  rw [RegulatoryMaximin.count_unique]; norm_num

end PMConstants.RegulatoryLabels
