import PMAction.LatticeToContinuum
import PMAction.LatticeSiteAction

/-! Integrated classical second variation on a bounded D₄ region.
Spatial refinement is taken before the fluctuation amplitude tends to zero.
The result concerns the ungauge-fixed classical Wilson action. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.IntegratedSecondVariation
open Matrix MeasureTheory Set Filter Topology
open scoped Matrix.Norms.L2Operator
local notation "V4" => (Fin 4 → ℝ)
open LatticeToContinuum LatticeSiteAction VaryingFields

variable {N : ℕ}
-- Keep the real algebra action explicit through the nested operator spaces.
local instance : NormedSpace ℝ (Matrix (Fin N) (Fin N) ℂ) :=
  NormedAlgebra.toNormedSpace (Matrix (Fin N) (Fin N) ℂ)
local instance : NormedSpace ℝ (V4 →L[ℝ] Matrix (Fin N) (Fin N) ℂ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
local instance : NormedAddCommGroup (V4 →L[ℝ] (V4 →L[ℝ] Matrix (Fin N) (Fin N) ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
variable (A a : V4 → V4 →L[ℝ] Matrix (Fin N) (Fin N) ℂ)
  (DA Da : V4 → V4 →L[ℝ] (V4 →L[ℝ] Matrix (Fin N) (Fin N) ℂ))

lemma continuous_density (hA : Continuous A) (ha : Continuous a)
    (hDA : Continuous DA) (hDa : Continuous Da) (β t : ℝ) :
    Continuous (fun x => ymDensity A a DA Da x β t) := by
  simp only [ymDensity, fieldStrength, curvature, fam, dfam,
    _root_.add_apply, ContinuousLinearMap.comp_apply, scaleL_apply]
  fun_prop

lemma continuous_quadratic (hA : Continuous A) (ha : Continuous a)
    (hDA : Continuous DA) (hDa : Continuous Da) (β : ℝ) :
    Continuous (fun x => q2 A a DA Da x β) := by
  unfold q2 Gc Hc fieldStrength curvature
  fun_prop

lemma continuous_quartic (ha : Continuous a) (β : ℝ) :
    Continuous (fun x => q4 a x β) := by
  unfold q4 Hc
  fun_prop

def action (S : Set V4) (β t : ℝ) := ∫ x in S, ymDensity A a DA Da x β t
def quadratic (S : Set V4) (β : ℝ) := ∫ x in S, q2 A a DA Da x β
def quartic (S : Set V4) (β : ℝ) := ∫ x in S, q4 a x β

lemma integrable_on_bounded {f : V4 → ℝ} (hf : Continuous f) {S : Set V4}
    (hS : Bornology.IsBounded S) : IntegrableOn f S := by
  exact (hf.continuousOn.integrableOn_compact hS.isCompact_closure).mono_set subset_closure

/-- Exact integrated quartic identity, with integrability derived from
continuity on the bounded region. -/
theorem second_difference {S : Set V4} (hS : Bornology.IsBounded S)
    (hA : Continuous A) (ha : Continuous a) (hDA : Continuous DA) (hDa : Continuous Da)
    (β s : ℝ) :
    action A a DA Da S β s + action A a DA Da S β (-s) - 2 * action A a DA Da S β 0 =
      2*s^2 * quadratic A a DA Da S β + 2*s^4 * quartic a S β := by
  have hi (t) := integrable_on_bounded (continuous_density A a DA Da hA ha hDA hDa β t) hS
  have h2 := integrable_on_bounded (continuous_quadratic A a DA Da hA ha hDA hDa β) hS
  have h4 := integrable_on_bounded (continuous_quartic a ha β) hS
  unfold action quadratic quartic
  calc
    _ = ∫ x in S, (ymDensity A a DA Da x β s + ymDensity A a DA Da x β (-s) -
        2 * ymDensity A a DA Da x β 0) := by
      symm
      have he := integral_sub ((hi s).add (hi (-s))) ((hi 0).const_mul 2)
      simp only [Pi.add_apply] at he
      rw [integral_add (hi s) (hi (-s))] at he
      simpa only [integral_const_mul] using he
    _ = ∫ x in S, (2*s^2 * q2 A a DA Da x β + 2*s^4 * q4 a x β) := by
      congr 1
      funext x
      exact ym_second_difference A a DA Da x β s
    _ = _ := by
      rw [integral_add (h2.const_mul _) (h4.const_mul _), integral_const_mul, integral_const_mul]

theorem hessian_limit {S : Set V4} (hS : Bornology.IsBounded S)
    (hA : Continuous A) (ha : Continuous a) (hDA : Continuous DA) (hDa : Continuous Da) (β : ℝ) :
    Tendsto (fun s : ℝ => (action A a DA Da S β s + action A a DA Da S β (-s) -
        2 * action A a DA Da S β 0) / s^2) (nhdsWithin 0 {0}ᶜ)
      (𝓝 (2 * quadratic A a DA Da S β)) := by
  simp_rw [second_difference A a DA Da hS hA ha hDA hDa]
  have hc : Continuous (fun s : ℝ => 2 * quadratic A a DA Da S β +
      2 * s^2 * quartic a S β) := by fun_prop
  have ht := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
  simp only [zero_pow two_ne_zero, mul_zero, zero_mul, add_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s ≠ 0 := hs
  field_simp


lemma family_lipschitz
    (hLA : ∀ S : Set V4, IsCompact S → ∃ L : ℝ, 0 ≤ L ∧
      ∀ x ∈ S, ∀ y ∈ S, ‖DA x - DA y‖ ≤ L * ‖x-y‖)
    (hLa : ∀ S : Set V4, IsCompact S → ∃ L : ℝ, 0 ≤ L ∧
      ∀ x ∈ S, ∀ y ∈ S, ‖Da x - Da y‖ ≤ L * ‖x-y‖) (t : ℝ) :
    ∀ S : Set V4, IsCompact S → ∃ L : ℝ, 0 ≤ L ∧
      ∀ x ∈ S, ∀ y ∈ S, ‖dfam DA Da t x - dfam DA Da t y‖ ≤ L * ‖x-y‖ := by
  intro S hS
  obtain ⟨LA, hLA0, hDA⟩ := hLA S hS
  obtain ⟨La, hLa0, hDa⟩ := hLa S hS
  refine ⟨LA + ‖scaleL N t‖ * La, by positivity, ?_⟩
  intro x hx y hy
  have he : dfam DA Da t x - dfam DA Da t y =
      (DA x - DA y) + (scaleL N t).comp (Da x - Da y) := by
    simp only [dfam, ContinuousLinearMap.comp_sub]
    abel
  rw [he]
  have h1 := norm_add_le (DA x - DA y) ((scaleL N t).comp (Da x - Da y))
  have h2 := ContinuousLinearMap.opNorm_comp_le (scaleL N t) (Da x - Da y)
  have h3 := mul_le_mul_of_nonneg_left (hDa x hx y hy) (norm_nonneg (scaleL N t))
  have h4 := hDA x hx y hy
  nlinarith

section Lattice
variable {S : Set V4}
  (hSb : Bornology.IsBounded S) (hSm : MeasurableSet S) (hSf : volume (frontier S) = 0)
  (hA : ∀ y, HasFDerivAt A (DA y) y) (ha : ∀ y, HasFDerivAt a (Da y) y)
  (hDA : Continuous DA) (hDa : Continuous Da)
  (hLA : ∀ C : Set V4, IsCompact C → ∃ L : ℝ, 0 ≤ L ∧
    ∀ x ∈ C, ∀ y ∈ C, ‖DA x - DA y‖ ≤ L * ‖x-y‖)
  (hLa : ∀ C : Set V4, IsCompact C → ∃ L : ℝ, 0 ≤ L ∧
    ∀ x ∈ C, ∀ y ∈ C, ‖Da x - Da y‖ ≤ L * ‖x-y‖)
  (sA : ∀ y v, star (A y v) = -A y v)
  (sa : ∀ y v, star (a y v) = -a y v)
  (T : ℝ → V4 → V4 → ℝ → Matrix (Fin N) (Fin N) ℂ)
  (hT0 : ∀ t y v, T t y v 0 = 1)
  (hTd : ∀ t y v u, HasDerivAt (T t y v)
    (T t y v u * fam A a t (y + u • v) v) u)

include hSb hSm hSf hA ha hDA hDa hLA hLa sA sa hT0 hTd

/-- Spatial refinement of the actual D₄ site action at fixed fluctuation
size gives the integrated second difference. -/
theorem lattice_second_difference (β s : ℝ) :
    Tendsto (fun n => siteAction (T s) β S n + siteAction (T (-s)) β S n -
      2 * siteAction (T 0) β S n) atTop
      (𝓝 (2*s^2 * quadratic A a DA Da S β + 2*s^4 * quartic a S β)) := by
  have hAc : Continuous A := continuous_iff_continuousAt.mpr (fun x => (hA x).continuousAt)
  have hac : Continuous a := continuous_iff_continuousAt.mpr (fun x => (ha x).continuousAt)
  have lim (t : ℝ) : Tendsto (fun n => siteAction (T t) β S n) atTop
      (𝓝 (action A a DA Da S β t)) := by
    have hf : Continuous (dfam DA Da t) := by
      unfold dfam
      exact hDA.add (hDa.const_clm_comp (scaleL N t))
    exact d4_yang_mills_action hSb hSm hSf (fam_deriv hA ha t) hf
      (family_lipschitz DA Da hLA hLa t) (fam_skew sA sa t)
      (T t) (hT0 t) (hTd t) β
  rw [← second_difference A a DA Da hSb hAc hac hDA hDa]
  exact ((lim s).add (lim (-s))).sub ((lim 0).const_mul 2)

/-- The integrated classical Hessian is the iterated limit, taking the
site-spacing limit before the fluctuation-amplitude limit. -/
theorem iterated_hessian (β : ℝ) :
    Tendsto (fun s : ℝ => limUnder atTop
      (fun n => siteAction (T s) β S n + siteAction (T (-s)) β S n -
        2 * siteAction (T 0) β S n) / s^2)
      (nhdsWithin 0 {0}ᶜ) (𝓝 (2 * quadratic A a DA Da S β)) := by
  have hAc : Continuous A := continuous_iff_continuousAt.mpr (fun x => (hA x).continuousAt)
  have hac : Continuous a := continuous_iff_continuousAt.mpr (fun x => (ha x).continuousAt)
  have he (s : ℝ) := (lattice_second_difference A a DA Da hSb hSm hSf hA ha hDA hDa
    hLA hLa sA sa T hT0 hTd β s).limUnder_eq
  have ht := hessian_limit A a DA Da hSb hAc hac hDA hDa β
  simp_rw [he]
  simpa only [second_difference A a DA Da hSb hAc hac hDA hDa] using ht

end Lattice

end PMAction.IntegratedSecondVariation
