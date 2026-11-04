import PMConstants.ReferenceLink

/-!
# What the reference gives the gauge bosons

The selected reference is the neutral carrier `ν` of the lepton-doublet type. Reading the
electroweak generators on it gives the quadratic mass form of the gauge fields.

* `charged_entry`: `⟨ν|T₁²|ν⟩ = 1/4`, so `m_W² ∝ g²/4`.
* `neutral_entries`: `⟨ν|T₃²|ν⟩ = ⟨ν|(Y/2)²|ν⟩ = 1/4` and `⟨ν|T₃·Y/2|ν⟩ = -1/4`.
* `neutral_form`: the neutral mass form `[[g²/4, -gg'/4], [-gg'/4, g'²/4]]` has determinant `0` (a
  massless photon) and trace `(g² + g'²)/4` (so `m_Z² ∝ (g² + g'²)/4`), and its null vector is
  `(g', g)`, the photon combination.
* `rho_one`: hence `m_W²/m_Z² = g²/(g² + g'²)`: tree-level `ρ = 1`, the relation the W-mass tests
  use with the measured `m_Z`.
* `rho_multiplet`: for a reference multiplet of isospin `T ≤ 3/2` with neutral component `T₃ ≠ 0`,
  `ρ = (T(T+1) - T₃²)/(2T₃²) = 1` only for `T = 1/2`. A larger reference multiplet would spoil
  `ρ = 1`.
* `link_charge`: a weak doublet of hypercharge `h` has charges `(h ± 1)/2`; they are `{0, -1}`, the
  reference displacement's charges (`ReferenceAnchor.reference_charges`), up to sign exactly when
  `|h| = 1`. This is the hypercharge matching used by `ReferenceLink`.
* `colour_moves_iff`: a channel is fixed by every colour generator exactly when it is a lepton
  channel, so colour moves exactly the twelve coloured channels (`colour_moved_card`), the count in
  `ColourReference.coloured_card`, now read from the actions rather than the type labels.
-/

noncomputable section
namespace PMConstants.ReferenceMasses
open PMConstants Matrix GeneratorNormalization PacketTraceForm ReferenceAnchor ReferenceStabilizer

def t1 : PacketGaugeActions.M := weakGen !![0, (1 / 2 : ℂ); 1 / 2, 0]

theorem charged_entry : (t1 * t1) (lepton 0) (lepton 0) = 1 / 4 := by
  have : t1 * t1 = weakGen (!![0, (1 / 2 : ℂ); 1 / 2, 0] * !![0, (1 / 2 : ℂ); 1 / 2, 0]) := by
    simp only [t1, weakGen, PacketGaugeActions.block_mul, ← mul_kronecker_mul, mul_one, mul_zero]
  rw [this, weak_lepton]; simp [Matrix.mul_apply, Fin.sum_univ_two]; norm_num

lemma t3_diag_entries (c : PacketGaugeActions.Channels) :
    (t3 * t3) c (lepton 0) = t3 c (lepton 0) * t3 (lepton 0) (lepton 0) ∧
    (hyperGen * hyperGen) c (lepton 0) = hyperGen c (lepton 0) * hyperGen (lepton 0) (lepton 0) ∧
    (t3 * hyperGen) c (lepton 0) = t3 c (lepton 0) * hyperGen (lepton 0) (lepton 0) := by
  have h1 := ReferenceRestoration.t3_isDiag
  have h2 := ReferenceRestoration.hyper_isDiag
  rw [← h1.diagonal_diag, ← h2.diagonal_diag]
  simp only [diagonal_mul_diagonal, diagonal_apply, Matrix.diag]
  refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> simp_all

theorem neutral_entries :
    (t3 * t3) (lepton 0) (lepton 0) = 1 / 4 ∧ (hyperGen * hyperGen) (lepton 0) (lepton 0) = 1 / 4 ∧
      (t3 * hyperGen) (lepton 0) (lepton 0) = -1 / 4 := by
  obtain ⟨a, b, c⟩ := t3_diag_entries (lepton 0)
  have ht : t3 (lepton 0) (lepton 0) = 1 / 2 := by simp [t3, weak_lepton]
  have hy : hyperGen (lepton 0) (lepton 0) = -1 / 2 := by simp [hyper_lepton]
  rw [a, b, c, ht, hy]; norm_num

/-- The neutral mass form read on the reference. -/
def neutralForm (g g' : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![g ^ 2 / 4, -(g * g') / 4; -(g * g') / 4, g' ^ 2 / 4]

/-- The form is the reference reading of `g T₃` and `g' Y/2`. -/
theorem form_from_reference (g g' : ℝ) (i j : Fin 2) :
    ((neutralForm g g' i j : ℝ) : ℂ) =
      !![(g : ℂ) ^ 2 * (t3 * t3) (lepton 0) (lepton 0), g * g' * (t3 * hyperGen) (lepton 0) (lepton 0);
        g * g' * (t3 * hyperGen) (lepton 0) (lepton 0),
        (g' : ℂ) ^ 2 * (hyperGen * hyperGen) (lepton 0) (lepton 0)] i j := by
  obtain ⟨a, b, c⟩ := neutral_entries
  fin_cases i <;> fin_cases j <;> simp [neutralForm, a, b, c] <;> ring

theorem neutral_form (g g' : ℝ) :
    (neutralForm g g').det = 0 ∧ (neutralForm g g').trace = (g ^ 2 + g' ^ 2) / 4 ∧
      (neutralForm g g') *ᵥ ![g', g] = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [neutralForm, Matrix.det_fin_two]; ring
  · simp [neutralForm, Matrix.trace, Fin.sum_univ_two]; ring
  · ext i; fin_cases i <;> simp [neutralForm, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- **Tree-level `ρ = 1`.** -/
theorem rho_one (g g' : ℝ) (h : 0 < g ^ 2 + g' ^ 2) :
    (g ^ 2 / 4) / (neutralForm g g').trace = g ^ 2 / (g ^ 2 + g' ^ 2) := by
  rw [(neutral_form g g').2.1]; field_simp

/-- `ρ` for a reference multiplet of isospin `T` whose neutral component has `T₃`. -/
def rho (T T3 : ℚ) : ℚ := (T * (T + 1) - T3 ^ 2) / (2 * T3 ^ 2)

theorem rho_multiplet :
    (∀ T3 ∈ ({1/2, -1/2} : Finset ℚ), rho (1/2) T3 = 1) ∧
    (∀ T3 ∈ ({1, -1} : Finset ℚ), rho 1 T3 ≠ 1) ∧
    (∀ T3 ∈ ({1/2, -1/2, 3/2, -3/2} : Finset ℚ), rho (3/2) T3 ≠ 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro T3 hT <;> simp only [Finset.mem_insert, Finset.mem_singleton] at hT <;>
    rcases hT with rfl | rfl | rfl | rfl <;> norm_num [rho]

/-- **The link's hypercharge.** A doublet of hypercharge `h` has charges `(h + 1)/2, (h - 1)/2`. -/
theorem link_charge (h : ℚ) :
    ((({(h + 1) / 2, (h - 1) / 2} : Finset ℚ) = {0, -1}) ∨
      (({(h + 1) / 2, (h - 1) / 2} : Finset ℚ) = {0, 1})) ↔ h = -1 ∨ h = 1 := by
  constructor
  · rintro (H | H)
    · have : (0 : ℚ) ∈ ({(h + 1) / 2, (h - 1) / 2} : Finset ℚ) := by rw [H]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with e | e
      · left; linarith
      · have : (-1 : ℚ) ∈ ({(h + 1) / 2, (h - 1) / 2} : Finset ℚ) := by rw [H]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with e' | e' <;> (exfalso; linarith)
    · have : (0 : ℚ) ∈ ({(h + 1) / 2, (h - 1) / 2} : Finset ℚ) := by rw [H]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with e | e
      · have : (1 : ℚ) ∈ ({(h + 1) / 2, (h - 1) / 2} : Finset ℚ) := by rw [H]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with e' | e' <;> (exfalso; linarith)
      · right; linarith
  · rintro (rfl | rfl)
    · left; norm_num
    · right; norm_num; exact Finset.pair_comm _ _

/-- Lepton channels: the doublet and the two singlets. -/
def leptonic : PacketGaugeActions.Channels → Bool
  | .inr (.inr _) => true
  | _ => false

/-- **Colour moves exactly the coloured channels.** -/
theorem colour_moves_iff (c : PacketGaugeActions.Channels) :
    (∀ B : Matrix (Fin 3) (Fin 3) ℂ, Fixes (colourGen B) c) ↔ leptonic c = true := by
  constructor
  · intro h
    have hc := h (Matrix.of fun _ _ => 1) c
    rcases c with q | q | s
    · simp [colourGen, PacketGaugeActions.block, Matrix.kroneckerMap_apply] at hc
    · simp [colourGen, PacketGaugeActions.block, Matrix.kroneckerMap_apply] at hc
    · rfl
  · intro h B
    rcases c with q | q | s
    · simp [leptonic] at h
    · simp [leptonic] at h
    · intro d
      rcases d with q | q | t | t <;> rcases s with s | s <;>
        simp [colourGen, PacketGaugeActions.block]

theorem colour_moved_card :
    (Finset.univ.filter fun c : PacketGaugeActions.Channels => leptonic c = false).card = 12 := by
  decide

end PMConstants.ReferenceMasses
