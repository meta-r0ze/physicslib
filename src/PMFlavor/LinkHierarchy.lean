import PMFlavor.LinkKronComparison
import PMElementaryParticles.LeptonMasses

/-!
# The eigenvector link cannot carry a charged-lepton hierarchy

`LinkKronComparison` retired the eigenvector link (`brokenLink δ`, `brokenLinkB ε`) for quarks and
left it a lepton candidate. This module tests it against the masses the same link must give.

**The link fixes the mass ratios.** `PMAction.WallSeesaw.seesaw`: the light masses are `δ₀²/σᵢ(Y)`
with a flavour-blind on-site mass `δ₀` (`PMAction.WallExchange`: `δβ ⊗ 1`), so the ratios of the
light masses are the inverse ratios of the link's singular values. No free scale per generation.

**The spectrum is rigid.** For every `δ` the spectrum of `brokenLink δ` is `{1, rootP δ, rootM δ}`
(`BreakingLink.brokenLink_antisym`, `MixingMatrix.brokenLink_eigP/M`), and the same holds for
`brokenLinkB` (`LinkKronComparison.brokenLinkB_antiB`, `MixingMatrix.brokenLinkB_eigP/M`).
* `block_product`: `(rootP x − 3)(rootM x − 3) = −2` for every `x`.
* `close_pair`: hence either `3 < rootP x ≤ 4` or `1 < rootM x < 3`.
* `brokenLink_close_pair`, `brokenLinkB_close_pair`: every such link has, besides the eigenvalue
  `1`, a second eigenvalue `r` with `1 < r ≤ 4`. Two of its light masses are within a factor `4`.
  (The sharp factor, found numerically, is `2 + √3`.)

**The test.** The argument needs only that the three charged-lepton masses are pairwise more than
a factor `4` apart. `measured_gaps`: the measured masses (PDG 2024, MeV: `m_e = 0.51099895`,
`m_μ = 105.6583755`, `m_τ = 1776.93 ± 0.09`; smallest ratio `m_τ/m_μ ≈ 16.8`) satisfy it with a
wide margin, so the test does not depend on any library mass. `lepton_gaps` checks the library's
own values (`LeptonMasses`: `1`, `206.77`, `3477` in units of `m_e`) agree; a later error there
does not affect the result. `no_close_pair` (for any set with the gap property) and
`no_lepton_link`: no light-mass pair of an eigenvector link is a pair of charged leptons, for any
`δ` or `ε`. The charged leptons are therefore not
either sector. With the charged-lepton basis the generation basis instead, one sector alone sets
the PMNS, and its protected state (`(0, 1, −1)` or `(1, 0, −1)`) puts a zero in it, excluded by
every NuFIT `|U|` range (`GenerationBreaking.pmns_no_shared_state` is the same obstruction).

**Premise this rests on.** `WallSeesaw`'s identification of the light masses with `δ₀²/σᵢ(Y)` for
the same `Y` whose eigenvectors give the mixing (`WallExchange` lists "the zero-mode mass matrix is
this link `Y`" as an input). If that identification is wrong, this module says nothing.

**Result.** Given that premise, the identification `Y = brokenLink` is retired for leptons as for
quarks. What
survives is only the reading that the mixings are eigenvectors of the cardinality link while the
masses come from a different matrix with the same eigenvectors: that needs a new premise and three
free spectral values, and its one content is the `|U| = 1/2` entry of `LinkKronComparison`.
-/

noncomputable section
namespace PMFlavor.LinkHierarchy
open Matrix BreakingLink MixingMatrix LinkKronComparison

theorem rootP_gt_three (x : ℝ) : 3 < rootP x := by
  have hs : |x - 1| < Real.sqrt ((x - 1) ^ 2 + 8) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  have ha := neg_abs_le (x - 1)
  unfold rootP
  linarith

/-- **The two non-protected eigenvalues are tied**: `(rootP − 3)(rootM − 3) = −2`. -/
theorem block_product (x : ℝ) : (rootP x - 3) * (rootM x - 3) = -2 := by
  have hs : Real.sqrt ((x - 1) ^ 2 + 8) ^ 2 = (x - 1) ^ 2 + 8 := Real.sq_sqrt (by positivity)
  unfold rootP rootM
  linear_combination (-1 / 4 : ℝ) * hs

/-- **One block eigenvalue is always within a factor `4` of the protected eigenvalue `1`.** -/
theorem close_pair (x : ℝ) : (3 < rootP x ∧ rootP x ≤ 4) ∨ (1 < rootM x ∧ rootM x < 3) := by
  have hP := rootP_gt_three x
  have hM := rootM_lt_three x
  have hprod := block_product x
  by_cases h : rootP x ≤ 4
  · exact Or.inl ⟨hP, h⟩
  · right
    have h := not_le.mp h
    refine ⟨?_, hM⟩
    nlinarith [mul_pos (sub_pos.2 h) (sub_pos.2 hM)]

theorem close_value (x : ℝ) :
    ∃ r : ℝ, 1 < r ∧ r ≤ 4 ∧ (r = rootP x ∨ r = rootM x) := by
  rcases close_pair x with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨rootP x, by linarith, h2, Or.inl rfl⟩
  · exact ⟨rootM x, h1, by linarith, Or.inr rfl⟩

/-- **The first-sector link has eigenvalues `1` and `r ∈ (1, 4]`, for every `δ`.** -/
theorem brokenLink_close_pair (δ : ℝ) :
    brokenLink δ *ᵥ GenerationBreaking.anti = (1 : ℂ) • GenerationBreaking.anti ∧
      ∃ r : ℝ, 1 < r ∧ r ≤ 4 ∧
        brokenLink δ *ᵥ (![(r : ℂ) - 3, 1, 1] : Fin 3 → ℂ) =
          (r : ℂ) • (![(r : ℂ) - 3, 1, 1] : Fin 3 → ℂ) := by
  refine ⟨brokenLink_antisym δ, ?_⟩
  obtain ⟨r, h1, h4, hr⟩ := close_value δ
  refine ⟨r, h1, h4, ?_⟩
  rcases hr with rfl | rfl
  · exact brokenLink_eigP δ
  · exact brokenLink_eigM δ

/-- **The second-sector link likewise, for every `ε`.** -/
theorem brokenLinkB_close_pair (ε : ℝ) :
    brokenLinkB ε *ᵥ antiB = (1 : ℂ) • antiB ∧
      ∃ r : ℝ, 1 < r ∧ r ≤ 4 ∧
        brokenLinkB ε *ᵥ (![1, (r : ℂ) - 3, 1] : Fin 3 → ℂ) =
          (r : ℂ) • (![1, (r : ℂ) - 3, 1] : Fin 3 → ℂ) := by
  refine ⟨brokenLinkB_antiB ε, ?_⟩
  obtain ⟨r, h1, h4, hr⟩ := close_value ε
  refine ⟨r, h1, h4, ?_⟩
  rcases hr with rfl | rfl
  · exact brokenLinkB_eigP ε
  · exact brokenLinkB_eigM ε

/-! ## The charged-lepton test -/

/-- A charged-lepton mass in units of `m_e`, as the library derives them. -/
def IsLepton (m : ℝ) : Prop :=
  m = 1 ∨ m = PMElementaryParticles.LeptonMasses.muon ∨ m = PMElementaryParticles.LeptonMasses.tau

/-- **Charged-lepton masses are pairwise more than a factor `4` apart.** -/
theorem lepton_gaps (a b : ℝ) (ha : IsLepton a) (hb : IsLepton b) (h : a < b) : 4 * a < b := by
  have hm := PMElementaryParticles.LeptonMasses.muon_value
  have ht := PMElementaryParticles.LeptonMasses.tau_value
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> linarith [hm.1, hm.2]

/-- **The gap property kills any close pair.** If every two members of a set of positive masses
are more than a factor `4` apart, no seesaw pair `c/r, c` with `1 < r ≤ 4` lies in it. -/
theorem no_close_pair (S : ℝ → Prop) (gaps : ∀ a b, S a → S b → a < b → 4 * a < b)
    (c r : ℝ) (hc : 0 < c) (hr1 : 1 < r) (hr4 : r ≤ 4) (hlo : S (c / r)) (hhi : S c) : False := by
  have h1 : c / r < c := div_lt_self hc hr1
  have h2 := gaps _ _ hlo hhi h1
  have h3 : c ≤ 4 * (c / r) := by
    rw [mul_div_assoc', le_div_iff₀ (by linarith)]
    nlinarith
  linarith

/-- Measured charged-lepton masses in MeV (PDG 2024). -/
def IsMeasuredLepton (m : ℝ) : Prop := m = 0.51099895 ∨ m = 105.6583755 ∨ m = 1776.93

theorem measured_gaps (a b : ℝ) (ha : IsMeasuredLepton a) (hb : IsMeasuredLepton b) (h : a < b) :
    4 * a < b := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first | (norm_num at h; done) | norm_num

/-- **No eigenvector link carries two measured charged leptons**, at any overall scale. -/
theorem no_measured_lepton_link (c r : ℝ) (hc : 0 < c) (hr1 : 1 < r) (hr4 : r ≤ 4)
    (hlo : IsMeasuredLepton (c / r)) (hhi : IsMeasuredLepton c) : False :=
  no_close_pair IsMeasuredLepton measured_gaps c r hc hr1 hr4 hlo hhi

/-- **No eigenvector link carries two charged leptons**, with the library's values. With seesaw masses `c/1` and `c/r` from
the eigenvalues `1` and `r ∈ (1, 4]` (`WallSeesaw.seesaw`), the two masses cannot both be charged
leptons, for any scale `c`. -/
theorem no_lepton_link (c r : ℝ) (hc : 0 < c) (hr1 : 1 < r) (hr4 : r ≤ 4)
    (hlo : IsLepton (c / r)) (hhi : IsLepton c) : False :=
  no_close_pair IsLepton lepton_gaps c r hc hr1 hr4 hlo hhi

end PMFlavor.LinkHierarchy
