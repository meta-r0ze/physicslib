import PMFlavor.GoldenGeometry

/-! **Explicit 600-cell pentagon.**

Five vertices of the 600-cell form a regular pentagon.  Its edge length is
`1/φ` and its diagonal length is `1`, so the diagonal/side ratio is `φ`.
-/

noncomputable section
namespace PMFlavor.SixHundredCell

open PMFlavor

local notation "φ" => FlavourPulls.φ

lemma phi_sq : φ ^ 2 = φ + 1 := by
  unfold FlavourPulls.φ
  have h : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith

lemma phi_pos : 0 < φ := by
  unfold FlavourPulls.φ
  have h := Real.sqrt_nonneg 5
  linarith

lemma inv_phi_sq : (φ ^ 2)⁻¹ = 2 - φ := by
  have hφ : φ ≠ 0 := ne_of_gt phi_pos
  field_simp [hφ]
  nlinarith [phi_sq]


/-- Squared Euclidean distance in the 4-coordinate 600-cell space. -/
def distSq (x y : Fin 4 → ℝ) : ℝ := ∑ i, (x i - y i) ^ 2

/-- Five 600-cell vertices forming a regular pentagon. -/
def pentagon : Fin 5 → (Fin 4 → ℝ) :=
  ![![1, 0, 0, 0],
    ![φ / 2, 1 / 2, 0, (φ - 1) / 2],
    ![1 / 2, 1 / 2, 1 / 2, 1 / 2],
    ![1 / 2, 0, φ / 2, (φ - 1) / 2],
    ![φ / 2, -(φ - 1) / 2, 1 / 2, 0]]

theorem edge_sq (i : Fin 5) :
    distSq (pentagon i) (pentagon (i + 1)) = 1 / φ ^ 2 := by
  fin_cases i <;>
    simp [distSq, pentagon, Fin.sum_univ_four, inv_phi_sq] <;>
    nlinarith [phi_sq]

theorem diagonal_sq (i : Fin 5) :
    distSq (pentagon i) (pentagon (i + 2)) = 1 := by
  fin_cases i <;>
    simp [distSq, pentagon, Fin.sum_univ_four] <;>
    nlinarith [phi_sq]

/-- The squared diagonal/side ratio is `φ²`. -/
theorem ratio_sq : (1 : ℝ) / (1 / φ ^ 2) = φ ^ 2 := by
  field_simp [phi_sq]

/-- The diagonal/side ratio of this 600-cell pentagon is `φ`. -/
theorem diagonal_over_edge : (1 : ℝ) / (1 / φ) = φ := by
  field_simp [ne_of_gt phi_pos]

/-- Scaled Ptolemy relation for this pentagon. -/
theorem ptolemy_scaled :
    (1 : ℝ) = (1 / φ) ^ 2 + (1 / φ) * 1 := by
  field_simp [ne_of_gt phi_pos]
  nlinarith [phi_sq]

end PMFlavor.SixHundredCell
