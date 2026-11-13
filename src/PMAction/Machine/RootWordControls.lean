import PMAction.Machine.ProfileControls

/-!
# Controls from the substrate's links: a root word on one edge

`ProfileControls` realizes site-varying links along one fixed generator. A general substrate link
is not one exponential: the substrate's root events happen one after another, so a step that runs
all four root generators gives the ordered product `exp R₀ · exp R₁ · exp R₂ · exp R₃`,
`Rⱼ = aⱼ • packetRoot c j`. This module realizes that root word by smooth controls.

The controls stagger the roots across the slab `0 ≤ f ≤ 1`: root `j` runs only while `4f − j` is in
`(0, 1)`, with profile `Gⱼ(t) = smoothTransition (4t − j)` and rate `gⱼ = Gⱼ'`.

* `deriv_transition_zero_of_nonpos`, `deriv_transition_zero_of_one_le`: the smooth transition is
  flat outside `(0, 1)` (its extreme values are attained there), so `gⱼ t ≠ 0` only while root `j`
  is running (`rate_ne`).
* `later_idle`: while root `j` runs, every later root `i > j` has not started, so its factor is the
  identity. This is what lets the generators that do not commute be ordered: `stagger_mul`.
* `stagger_c2`: the controls are C².
* `root_word_link`: on an edge leaving the slab `f = 0` along `v` (`f v = 1`), the realized link
  is exactly `exp R₀ · (exp R₁ · (exp R₂ · exp R₃))`.

So a general one-step substrate link on an edge, an ordered word of root exponentials with any
rates, is realized by C² controls. **Still open:** doing this on every edge at once with different
rates, which needs the staggered profiles localized to each edge rather than to a slab.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.RootWordControls
open Matrix NativeCoherentLinks NativePacketUpdate ProfileControls
open scoped Matrix.Norms.L2Operator

local notation "st" => Real.smoothTransition

theorem deriv_transition_zero_of_nonpos {t : ℝ} (h : t ≤ 0) : deriv st t = 0 :=
  IsLocalMin.deriv_eq_zero (Filter.Eventually.of_forall fun x => by
    rw [Real.smoothTransition.zero_of_nonpos h]; exact Real.smoothTransition.nonneg x)

theorem deriv_transition_zero_of_one_le {t : ℝ} (h : 1 ≤ t) : deriv st t = 0 :=
  IsLocalMax.deriv_eq_zero (Filter.Eventually.of_forall fun x => by
    rw [Real.smoothTransition.one_of_one_le h]; exact Real.smoothTransition.le_one x)

/-- Profile of root `j`: it runs while `4t − j ∈ (0, 1)`. -/
def G (j : Fin 4) (t : ℝ) : ℝ := st (4 * t - (j.val : ℝ))

/-- Rate of root `j`. -/
def g (j : Fin 4) (t : ℝ) : ℝ := 4 * deriv st (4 * t - (j.val : ℝ))

theorem hasDerivAt_G (j : Fin 4) (t : ℝ) : HasDerivAt (G j) (g j t) t := by
  have h := (transition_diff.1 (4 * t - (j.val : ℝ))).hasDerivAt
  have hi : HasDerivAt (fun x : ℝ => 4 * x - (j.val : ℝ)) (4 * 1) t :=
    ((hasDerivAt_id' t).const_mul 4).sub_const _
  have hc := h.comp t hi
  rw [show g j t = deriv st (4 * t - (j.val : ℝ)) * (4 * 1) by unfold g; ring]
  exact hc

theorem rate_ne {j : Fin 4} {t : ℝ} (h : g j t ≠ 0) : 0 < 4 * t - j.val ∧ 4 * t - j.val < 1 := by
  unfold g at h
  constructor
  · by_contra h1
    exact h (by rw [deriv_transition_zero_of_nonpos (not_lt.1 h1), mul_zero])
  · by_contra h1
    exact h (by rw [deriv_transition_zero_of_one_le (not_lt.1 h1), mul_zero])

/-- Root `j`'s step generator. -/
def R (c : Fin 3) (a : Fin 4 → ℝ) (j : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ := a j • packetRoot c j

/-- Root `j`'s accumulated factor. -/
def E (c : Fin 3) (a : Fin 4 → ℝ) (j : Fin 4) (t : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  NormedSpace.exp (G j t • R c a j)

theorem hasDerivAt_E (c : Fin 3) (a : Fin 4 → ℝ) (j : Fin 4) (s : ℝ) :
    HasDerivAt (E c a j) (E c a j s * (g j s • R c a j)) s := by
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (R c a j) (G j s)
  rw [mul_smul_comm]
  exact h2.scomp s (hasDerivAt_G j s)

theorem E_zero (c : Fin 3) (a : Fin 4 → ℝ) (j : Fin 4) : E c a j 0 = 1 := by
  have hj : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  unfold E G
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_smul, NormedSpace.exp_zero]

theorem E_one (c : Fin 3) (a : Fin 4 → ℝ) (j : Fin 4) :
    E c a j 1 = NormedSpace.exp (R c a j) := by
  have hj : (j.val : ℝ) ≤ 3 := by exact_mod_cast Nat.le_of_lt_succ j.isLt
  unfold E G
  rw [Real.smoothTransition.one_of_one_le (by linarith), one_smul]

/-- **While root `j` runs, later roots have not started.** -/
theorem later_idle (c : Fin 3) (a : Fin 4 → ℝ) {i j : Fin 4} (hij : j < i) {s : ℝ}
    (h : g j s ≠ 0) : E c a i s = 1 := by
  have hr := (rate_ne h).2
  have hl : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast Nat.lt_iff_add_one_le.1 (Fin.lt_def.1 hij)
  unfold E G
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_smul, NormedSpace.exp_zero]

/-- A running generator commutes with any factor that is the identity while it runs. -/
theorem running_comm (c : Fin 3) (a : Fin 4 → ℝ) (j : Fin 4) (s : ℝ)
    (X : Matrix (Fin 4) (Fin 4) ℂ) (hX : g j s ≠ 0 → X = 1) :
    (g j s • R c a j) * X = X * (g j s • R c a j) := by
  by_cases h : g j s = 0
  · simp [h]
  · rw [hX h, mul_one, one_mul]

/-- **Ordered product rule.** If `B` commutes with `U` at `s`, `T · U` solves the transport ODE
with generator `B + C`. -/
theorem stagger_mul {T U : ℝ → Matrix (Fin 4) (Fin 4) ℂ} {B C : Matrix (Fin 4) (Fin 4) ℂ} {s : ℝ}
    (hT : HasDerivAt T (T s * B) s) (hU : HasDerivAt U (U s * C) s) (hc : B * U s = U s * B) :
    HasDerivAt (fun t => T t * U t) ((T s * U s) * (B + C)) s := by
  have h := hT.mul hU
  convert h using 1
  simp only [mul_add, mul_assoc, hc]

/-- Staggered root controls. -/
def stagger (f : V →L[ℝ] ℝ) (a : Fin 4 → ℝ) : Controls := fun j x => (a j * g j (f x)) • f

theorem stagger_c2 (f : V →L[ℝ] ℝ) (a : Fin 4 → ℝ) : ∀ j, ContDiff ℝ 2 (stagger f a j) := by
  intro j
  unfold stagger g
  exact (contDiff_const.mul ((contDiff_const.mul (transition_diff.2.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const))).comp f.contDiff)).smul contDiff_const

lemma packetA_stagger (c : Fin 3) (f : V →L[ℝ] ℝ) (a : Fin 4 → ℝ) (y v : V) :
    packetA c (stagger f a) y v = ∑ j, (g j (f y) * f v) • R c a j := by
  simp [packetA, form, stagger, R, ContinuousLinearMap.smulRight_apply, smul_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  ring

/-- **A root word on one edge is realized by C² controls.** -/
theorem root_word_link (c : Fin 3) (f : V →L[ℝ] ℝ) (a : Fin 4 → ℝ)
    (r : Realization c (stagger f a)) (y v : V) (hv : f v = 1) (hy : f y = 0) :
    r.packet y v 1 = NormedSpace.exp (R c a 0) * (NormedSpace.exp (R c a 1) *
      (NormedSpace.exp (R c a 2) * NormedSpace.exp (R c a 3))) := by
  let B : ℝ → Matrix (Fin 4) (Fin 4) ℂ := fun t =>
    g 0 t • R c a 0 + (g 1 t • R c a 1 + (g 2 t • R c a 2 + g 3 t • R c a 3))
  have key : ∀ t : ℝ, packetA c (stagger f a) (y + t • v) v = B t := by
    intro t
    rw [packetA_stagger, map_add, map_smul, hy, hv]
    simp [B, Fin.sum_univ_four, add_assoc]
  have hE := hasDerivAt_E c a
  have hT : ∀ s, HasDerivAt (fun t => E c a 0 t * (E c a 1 t * (E c a 2 t * E c a 3 t)))
      ((E c a 0 s * (E c a 1 s * (E c a 2 s * E c a 3 s))) * B s) s := by
    intro s
    have h23 := stagger_mul (hE 2 s) (hE 3 s)
      (running_comm c a 2 s _ fun h => later_idle c a (by decide) h)
    have h123 := stagger_mul (hE 1 s) h23 (running_comm c a 1 s _ fun h => by
      rw [later_idle c a (i := 2) (by decide) h, later_idle c a (i := 3) (by decide) h, one_mul])
    exact stagger_mul (hE 0 s) h123 (running_comm c a 0 s _ fun h => by
      rw [later_idle c a (i := 1) (by decide) h, later_idle c a (i := 2) (by decide) h,
        later_idle c a (i := 3) (by decide) h, one_mul, one_mul])
  have hskew : ∀ t, star (B t) = -B t := fun t => by
    have hs := packet_skew c (stagger f a) (y + t • v) v
    rwa [key] at hs
  have hU : ∀ t, HasDerivAt (r.packet y v) (r.packet y v t * B t) t := fun t => by
    have hd := r.packet_deriv y v t
    rwa [key] at hd
  have h := transport_unique hskew (by simp [E_zero]) (r.packet_zero y v) hT hU
    (r.packet_unitary y v) 1
  rw [← h]
  simp only [E_one]

end PMAction.RootWordControls
