import PMConstants.MatchedRegulation
import PMConstants.SurfaceBudget

/-!
# What persists at the scalar interface: maximal gain that pays for its own reflection

Two candidate laws were left open: maximal gain `λ = 128/989`, which exhausts the 23-label
regulatory ledger, and exact aperture matching, which reflects nothing but leaves slack.
Ask what persists. Under Closure there is no external reserve, so any reflected load must be
serviced from the same ledger at some nonnegative charge rate `c` (units of ledger per unit
reflected fraction; `c` is not fixed here). Persistence at gain `g` is

  `c · R(g) ≤ 3 − (23 g + 1/43)`,  `R(g) = ((6η − Z(g))/(6η + Z(g)))²`,  `Z(g) = e^{−2g}/g`.

* `maximal_not_persistent`: for every `c > 0`, maximal gain fails (its reflection is positive
  and its slack is zero).
* `matched_persistent`: exact matching persists for every `c ≥ 0`, with unused slack.
* `persistent_maximum`: for every `c > 0` there is a unique largest persistent gain `g*`.
  It lies strictly between the matched gain and `128/989`, and
  `128/989 − g* < c · 10⁻⁸ / 23`.

So Economy within persistence selects neither candidate exactly: it selects maximal gain
corrected by the reflection it must service, and that correction is below `4.4·10⁻¹⁰ c`.
Exact matching is selected only in the limit of unbounded reflection cost.
-/

noncomputable section
namespace PMConstants.PersistentGain
open PMConstants Matching MatchedRegulation

def aperture : ℝ := 6*overhead
def refl (g : ℝ) : ℝ := General.Matching.reflected 1 (regulator g) aperture
def slack (g : ℝ) : ℝ := 3 - (23*g + 1/43)

def Persistent (c g : ℝ) : Prop :=
  0 < g ∧ 0 ≤ slack g ∧ General.Matching.Admissible c (slack g) (regulator g) aperture

lemma aperture_pos : 0 < aperture := by norm_num [aperture, overhead]

lemma regulator_pos {g : ℝ} (hg : 0 < g) : 0 < regulator g :=
  div_pos (Real.exp_pos _) hg

lemma refl_eq (g : ℝ) :
    refl g = ((aperture - regulator g)/(aperture + regulator g))^2 := by
  simp [refl, General.Matching.reflected, Interface.reflection]

lemma slack_eq (g : ℝ) : slack g = 23*(selfCoupling - g) := by
  unfold slack; norm_num [selfCoupling]; ring

lemma admissible_iff (c g : ℝ) :
    General.Matching.Admissible c (slack g) (regulator g) aperture ↔ c * refl g ≤ slack g := by
  unfold General.Matching.Admissible General.Matching.reflected refl General.Matching.reflected
  simp

theorem maximal_not_persistent {c : ℝ} (hc : 0 < c) : ¬ Persistent c selfCoupling := by
  rintro ⟨-, -, h⟩
  rw [admissible_iff] at h
  have hr : (0.000000001 : ℝ) < refl selfCoupling := SurfaceBudget.reflected_bounds.1
  have hs : slack selfCoupling = 0 := by rw [slack_eq]; ring
  rw [hs] at h
  nlinarith

theorem matched_persistent {c gm : ℝ} (_hc : 0 ≤ c) (hg : 0 < gm)
    (hm : regulator gm = aperture) : Persistent c gm ∧ 0 < slack gm := by
  have hs : 0 < slack gm := by
    have := match_leaves_positive_slack hg (by simpa [aperture] using hm)
    unfold slack; linarith
  refine ⟨⟨hg, hs.le, ?_⟩, hs⟩
  rw [admissible_iff, refl_eq, hm]; simp; linarith

/-- Reflection grows with gain above the matched point. -/
lemma refl_mono {gm a b : ℝ} (hg : 0 < gm) (hm : regulator gm = aperture)
    (ha : gm ≤ a) (hab : a ≤ b) : refl a ≤ refl b := by
  have ha0 : 0 < a := hg.trans_le ha
  have hb0 : 0 < b := ha0.trans_le hab
  have hZa : regulator a ≤ aperture := by
    rcases ha.eq_or_lt with h | h
    · rw [← h, hm]
    · exact (regulator_strict hg h).le.trans hm.le
  have hZb : regulator b ≤ regulator a := by
    rcases hab.eq_or_lt with h | h
    · rw [h]
    · exact (regulator_strict ha0 h).le
  have hpa := regulator_pos ha0
  have hpb := regulator_pos hb0
  have hA := aperture_pos
  rw [refl_eq, refl_eq]
  have h1 : 0 ≤ (aperture - regulator a)/(aperture + regulator a) :=
    div_nonneg (by linarith) (by linarith)
  have h2 : (aperture - regulator a)/(aperture + regulator a) ≤
      (aperture - regulator b)/(aperture + regulator b) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  exact pow_le_pow_left₀ h1 h2 2

lemma refl_continuousOn {a b : ℝ} (ha : 0 < a) : ContinuousOn refl (Set.Icc a b) := by
  have hZ := regulator_continuousOn (b := b) ha
  have hden : ∀ x ∈ Set.Icc a b, aperture + regulator x ≠ 0 := fun x hx =>
    (add_pos aperture_pos (regulator_pos (ha.trans_le hx.1))).ne'
  have : ContinuousOn (fun g => ((aperture - regulator g)/(aperture + regulator g))^2)
      (Set.Icc a b) :=
    ((continuousOn_const.sub hZ).div (continuousOn_const.add hZ) hden).pow 2
  exact this.congr (fun x _ => refl_eq x)

theorem persistent_maximum {c : ℝ} (hc : 0 < c) :
    ∃ gs : ℝ, Persistent c gs ∧ (∀ g, Persistent c g → g ≤ gs) ∧
      (∀ gm, 0 < gm → regulator gm = aperture → gm < gs) ∧ gs < selfCoupling ∧
      selfCoupling - gs < c * 0.00000001 / 23 := by
  obtain ⟨gm, hg, hm⟩ := positive_match_exists aperture_pos
  have hlt : gm < selfCoupling := match_below_baseline hg (by simpa [aperture] using hm)
  let F : ℝ → ℝ := fun g => c * refl g - slack g
  have hF : ContinuousOn F (Set.Icc gm selfCoupling) := by
    have h1 : ContinuousOn (fun g => c * refl g) (Set.Icc gm selfCoupling) :=
      continuousOn_const.mul (refl_continuousOn hg)
    have h2 : ContinuousOn (fun g : ℝ => slack g) (Set.Icc gm selfCoupling) := by
      unfold slack; fun_prop
    exact h1.sub h2
  have hFa : F gm < 0 := by
    have := (matched_persistent hc.le hg hm).2
    simp only [F]; rw [refl_eq, hm]; simp; linarith
  have hrmax : (0.000000001 : ℝ) < refl selfCoupling := SurfaceBudget.reflected_bounds.1
  have hrmax' : refl selfCoupling < 0.00000001 := SurfaceBudget.reflected_bounds.2
  have hFb : 0 < F selfCoupling := by
    simp only [F]; rw [show slack selfCoupling = 0 by rw [slack_eq]; ring]; nlinarith
  obtain ⟨gs, hgs, hzero⟩ := intermediate_value_Icc hlt.le hF ⟨hFa.le, hFb.le⟩
  have hgs0 : 0 < gs := hg.trans_le hgs.1
  have hpers : Persistent c gs := by
    refine ⟨hgs0, ?_, ?_⟩
    · rw [slack_eq]; linarith [hgs.2]
    · rw [admissible_iff]; simp only [F] at hzero; linarith
  have hne_m : gs ≠ gm := by rintro rfl; linarith
  have hne_M : gs ≠ selfCoupling := by rintro rfl; linarith
  have hgm_lt : gm < gs := lt_of_le_of_ne hgs.1 (Ne.symm hne_m)
  have hgs_lt : gs < selfCoupling := lt_of_le_of_ne hgs.2 hne_M
  refine ⟨gs, hpers, ?_, ?_, hgs_lt, ?_⟩
  · intro g ⟨hg0, hsl, had⟩
    rw [admissible_iff] at had
    by_contra hcon
    have hgt : gs < g := lt_of_not_ge hcon
    have hgM : g ≤ selfCoupling := by rw [slack_eq] at hsl; linarith
    have hr := refl_mono hg hm hgm_lt.le hgt.le
    have hz : c * refl gs = slack gs := by simp only [F] at hzero; linarith
    have hsl' : slack g < slack gs := by rw [slack_eq, slack_eq]; linarith
    nlinarith
  · intro gm' hg' hm'
    rw [matching_unique hg' hg hm' hm]; exact hgm_lt
  · have hz : c * refl gs = slack gs := by simp only [F] at hzero; linarith
    have hr := refl_mono hg hm hgm_lt.le hgs_lt.le
    rw [slack_eq] at hz
    have : 23*(selfCoupling - gs) < c * 0.00000001 := by nlinarith
    linarith

end PMConstants.PersistentGain
