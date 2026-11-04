import PMConstants.ReadScale
import PMAction.RayPersistence
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# Why an executing mode is read at its mass

`ReadScale` reduced the read scale to one statement: the record of an event is taken at the
executing mode's own scale. This module derives that from persistence and frame independence. It
uses no separate notion of a "real particle".

* **Persistence selects normal modes.** `beats`: a superposition of two neutral directions with
  different frequencies does not stay on one ray. It returns to it only if one amplitude is zero.
  `mixed_not_persistent` applies this to the photon (`ω = |k|`) and the `Z`
  (`ω = √(k² + m²)`, `m > 0`). A direction that persists as itself, and so can execute a repeated
  read, is a normal mode.
* **Normal modes have the form's masses.** `variation`, `stationary_iff_mode`: the neutral
  quadratic action `s |A|² − A·MA` (with `s = ω² − k²`) is stationary exactly when `M A = s A`.
  `neutral_eigen`: the neutral form has determinant zero, so a nonzero mode has `s = 0` (photon)
  or `s = tr M = N²/4` (the `Z`, `NeutralCurrent.z_mass`). So `ω² − k²` is the mode's mass squared.
* **A frame-independent scale depends only on the invariant mass.** `boost_invariant`: boosts
  preserve `ω² − k²`. `to_rest`: a massive mode can be boosted to rest. So `scale_at_rest`: any
  scale `σ(ω, k)` that is the same in every frame equals its rest value `σ(m, 0)`.
* `z_read_scale`: for the `Z` mode, the frame-independent scale is `σ(m_Z, 0)`. With the scale
  measured as the rest-frame frequency, it is `m_Z`.

The photon is massless and has no rest frame. Its read needs no scale, because the abelian
slope vanishes below charged thresholds (`ReadScale.photon_read_flat`).

Still inputs: a read is frame independent; the scale is measured in frequency units, so a mode at
rest has scale `ω`.
-/

noncomputable section
namespace PMConstants.OnShell
open Matrix Complex

/-! ## Persistence selects normal modes -/

/-- **Two frequencies beat.** -/
theorem beats (a b : ℂ) (ω₁ ω₂ : ℝ) (hω : ω₁ ≠ ω₂) :
    (∀ t : ℝ, ∃ c : ℂ, a * exp (-((ω₁ * t : ℝ) : ℂ) * I) = c * a ∧
        b * exp (-((ω₂ * t : ℝ) : ℂ) * I) = c * b) ↔ a = 0 ∨ b = 0 :=
  PMAction.RayPersistence.beats a b ω₁ ω₂ hω

/-- **A photon–Z mixture does not persist.** For a massive `Z` (`m > 0`), a neutral state with
both a photon amplitude `a` and a `Z` amplitude `b` leaves its ray. -/
theorem mixed_not_persistent (a b : ℂ) (k m : ℝ) (hm : 0 < m) (ha : a ≠ 0) (hb : b ≠ 0) :
    ¬ ∀ t : ℝ, ∃ c : ℂ, a * exp (-((Real.sqrt (k ^ 2) * t : ℝ) : ℂ) * I) = c * a ∧
        b * exp (-((Real.sqrt (k ^ 2 + m ^ 2) * t : ℝ) : ℂ) * I) = c * b := by
  have hne : Real.sqrt (k ^ 2) ≠ Real.sqrt (k ^ 2 + m ^ 2) := by
    intro h
    have := congrArg (· ^ 2) h
    simp only [Real.sq_sqrt (sq_nonneg k), Real.sq_sqrt (by positivity : 0 ≤ k ^ 2 + m ^ 2)] at this
    nlinarith
  rw [beats a b _ _ hne]
  tauto

/-! ## Normal modes carry the form's masses -/

/-- The neutral quadratic action at invariant `s = ω² − k²`. -/
def action (M : Matrix (Fin 2) (Fin 2) ℝ) (s : ℝ) (A : Fin 2 → ℝ) : ℝ :=
  s * (A ⬝ᵥ A) - A ⬝ᵥ (M *ᵥ A)

/-- **First variation.** -/
theorem variation (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : Mᵀ = M) (s ε : ℝ) (A δ : Fin 2 → ℝ) :
    action M s (A + ε • δ) =
      action M s A + ε * (2 * (δ ⬝ᵥ (s • A - M *ᵥ A))) + ε ^ 2 * action M s δ := by
  have hsym : A ⬝ᵥ (M *ᵥ δ) = δ ⬝ᵥ (M *ᵥ A) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hM, dotProduct_comm]
  simp only [action, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, dotProduct_sub, smul_eq_mul, hsym, dotProduct_comm A δ]
  ring

/-- **Stationary exactly at a normal mode.** -/
theorem stationary_iff_mode (M : Matrix (Fin 2) (Fin 2) ℝ) (s : ℝ) (A : Fin 2 → ℝ) :
    (∀ δ : Fin 2 → ℝ, δ ⬝ᵥ (s • A - M *ᵥ A) = 0) ↔ M *ᵥ A = s • A := by
  constructor
  · intro h
    have hw : s • A - M *ᵥ A = 0 := by
      ext i
      have := h (Pi.single i 1)
      rw [single_dotProduct, one_mul] at this
      rw [Pi.zero_apply]; exact this
    exact (sub_eq_zero.mp hw).symm
  · intro h δ
    rw [h, sub_self, dotProduct_zero]

/-- **The neutral form's modes are the photon and the `Z`.** -/
theorem neutral_eigen (g g' s : ℝ) (A : Fin 2 → ℝ) (hA : A ≠ 0)
    (h : ReferenceMasses.neutralForm g g' *ᵥ A = s • A) :
    s = 0 ∨ s = (ReferenceMasses.neutralForm g g').trace := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [ReferenceMasses.neutralForm, mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  have htr : (ReferenceMasses.neutralForm g g').trace = g ^ 2 / 4 + g' ^ 2 / 4 := by
    simp [ReferenceMasses.neutralForm, Matrix.trace, Fin.sum_univ_two]
  rw [htr]
  have hD0 : (s * (s - (g ^ 2 / 4 + g' ^ 2 / 4))) * A 0 = 0 := by
    linear_combination (g' ^ 2 / 4 - s) * h0 + (g * g' / 4) * h1
  have hD1 : (s * (s - (g ^ 2 / 4 + g' ^ 2 / 4))) * A 1 = 0 := by
    linear_combination (g * g' / 4) * h0 + (g ^ 2 / 4 - s) * h1
  have hD : s * (s - (g ^ 2 / 4 + g' ^ 2 / 4)) = 0 := by
    by_contra hne
    apply hA
    ext i
    fin_cases i
    · exact (mul_eq_zero.mp hD0).resolve_left hne
    · exact (mul_eq_zero.mp hD1).resolve_left hne
  rcases mul_eq_zero.mp hD with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- **A stationary neutral mode has invariant `0` or `m_Z²`.** -/
theorem mode_mass (g g' s : ℝ) (hg : 0 < g) (A : Fin 2 → ℝ) (hA : A ≠ 0)
    (hstat : ∀ δ : Fin 2 → ℝ, δ ⬝ᵥ (s • A - ReferenceMasses.neutralForm g g' *ᵥ A) = 0) :
    s = 0 ∨ s = NeutralCurrent.N g g' ^ 2 / 4 := by
  rw [← NeutralCurrent.z_mass g g' hg]
  exact neutral_eigen g g' s A hA ((stationary_iff_mode _ s A).mp hstat)

/-! ## Frame independence -/

/-- A boost of rapidity `η` in `1 + 1` dimensions. -/
def boost (η : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 * Real.cosh η - p.2 * Real.sinh η, p.2 * Real.cosh η - p.1 * Real.sinh η)

/-- **Boosts preserve `ω² − k²`.** -/
theorem boost_invariant (η : ℝ) (p : ℝ × ℝ) :
    (boost η p).1 ^ 2 - (boost η p).2 ^ 2 = p.1 ^ 2 - p.2 ^ 2 := by
  have := Real.cosh_sq_sub_sinh_sq η
  simp only [boost]
  linear_combination (p.1 ^ 2 - p.2 ^ 2) * this

/-- **A massive mode can be boosted to rest.** -/
theorem to_rest (ω k m : ℝ) (hm : 0 < m) (hω : 0 < ω) (hshell : ω ^ 2 - k ^ 2 = m ^ 2) :
    ∃ η, boost η (ω, k) = (m, 0) := by
  refine ⟨Real.arsinh (k / m), ?_⟩
  have hc : Real.cosh (Real.arsinh (k / m)) = ω / m := by
    rw [Real.cosh_arsinh]
    have hpos : 0 ≤ ω / m := by positivity
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) hpos]
    field_simp
    linarith
  simp only [boost, Real.sinh_arsinh, hc, Prod.mk.injEq]
  constructor
  · field_simp; linarith
  · field_simp; ring

/-- **A frame-independent scale is its rest value.** -/
theorem scale_at_rest (σ : ℝ × ℝ → ℝ) (hσ : ∀ η p, σ (boost η p) = σ p) (ω k m : ℝ)
    (hm : 0 < m) (hω : 0 < ω) (hshell : ω ^ 2 - k ^ 2 = m ^ 2) : σ (ω, k) = σ (m, 0) := by
  obtain ⟨η, h⟩ := to_rest ω k m hm hω hshell
  rw [← hσ η, h]

/-- **The `Z` read is at `m_Z`.** A persistent, stationary, massive neutral mode has
`ω² − k² = m_Z²`. A frame-independent scale measured as the rest-frame frequency is then `m_Z`. -/
theorem z_read_scale (g g' : ℝ) (hg : 0 < g) (σ : ℝ × ℝ → ℝ) (hσ : ∀ η p, σ (boost η p) = σ p)
    (hunit : ∀ ω, σ (ω, 0) = ω) (ω k : ℝ) (hω : 0 < ω) (A : Fin 2 → ℝ) (hA : A ≠ 0)
    (hstat : ∀ δ : Fin 2 → ℝ,
      δ ⬝ᵥ ((ω ^ 2 - k ^ 2) • A - ReferenceMasses.neutralForm g g' *ᵥ A) = 0)
    (hmassive : ω ^ 2 - k ^ 2 ≠ 0) :
    σ (ω, k) = NeutralCurrent.N g g' / 2 := by
  have hs := (mode_mass g g' _ hg A hA hstat).resolve_left hmassive
  have hN := NeutralCurrent.N_pos g g' hg
  rw [scale_at_rest σ hσ ω k (NeutralCurrent.N g g' / 2) (by positivity) hω (by rw [hs]; ring),
    hunit]

end PMConstants.OnShell
