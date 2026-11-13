import PMAction.Machine.ConstantControls
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Controls from the substrate's links: site-varying profiles

`ConstantControls` realizes homogeneous substrate links (the same rates on every edge of a
direction) by constant controls. This module realizes links that vary from site to site, by
controls whose rates follow a smooth profile across the lattice.

Fix a direction `v`, a functional `f` with `f v = 1` (it labels the slabs crossed along `v`),
root rates `a`, and a smooth profile `G` with derivative `g`. The controls
`profile f g a j x = (a j * g (f x)) • f` run the fixed generator `A = Σⱼ aⱼ • packetRoot c j`
at the rate `g (f x)`.

* `profile_c2`: if `g` is C², so are the controls.
* `profile_transport`: `exp ((G (t₀ + s) − G t₀) • A)` solves the transport ODE with generator
  `g (t₀ + s) • A`. The generator at different points is one matrix times a scalar, so the
  transport is the exponential of the accumulated rate.
* `profile_link`: the realized transport from `y` along `v` is
  `exp ((G (f y + s) − G (f y)) • A)`. Each edge carries the profile's increment across it.
* `wall_link`, `wall_free_above`, `wall_free_below`: with `G` the smooth transition (`0` below
  `0`, `1` above `1`), the edges from the slab `f y = 0` carry `exp A`, and edges starting at
  `f y ≥ 1` or `f y ≤ −1` carry the identity. So a site-varying configuration, a wall of
  nontrivial links in vacuum, is realized by smooth controls.

**Still open:** a general site-varying configuration, where every edge has its own rates. On one
edge, generators that do not commute can be run one after another by staggered profiles, which
gives an ordered product of root exponentials (a root word, the substrate's own event order).
Assembling this over all edges needs profiles localized to each edge.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.ProfileControls
open Matrix NativeCoherentLinks NativePacketUpdate
open scoped Matrix.Norms.L2Operator

/-- Rates `aⱼ` scaled by the profile `g` evaluated on the slab label `f x`. -/
def profile (f : V →L[ℝ] ℝ) (g : ℝ → ℝ) (a : Fin 4 → ℝ) : Controls :=
  fun j x => (a j * g (f x)) • f

/-- **Profile controls are C² when the profile's derivative is.** -/
theorem profile_c2 (f : V →L[ℝ] ℝ) (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (a : Fin 4 → ℝ) :
    ∀ j, ContDiff ℝ 2 (profile f g a j) := fun j => by
  unfold profile
  exact (contDiff_const.mul (hg.comp f.contDiff)).smul contDiff_const

/-- The generator the profile scales. -/
def gen (c : Fin 3) (a : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ := ∑ j, a j • packetRoot c j

lemma packetA_profile (c : Fin 3) (f : V →L[ℝ] ℝ) (g : ℝ → ℝ) (a : Fin 4 → ℝ) (y v : V) :
    packetA c (profile f g a) y v = (g (f y) * f v) • gen c a := by
  simp [packetA, form, profile, gen, ContinuousLinearMap.smulRight_apply, Finset.smul_sum,
    smul_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  ring

/-- **The transport of a scalar profile is the exponential of the accumulated rate.** -/
theorem profile_transport {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (G g : ℝ → ℝ) (hG : ∀ t, HasDerivAt G (g t) t) (t₀ s : ℝ) :
    HasDerivAt (fun s => NormedSpace.exp ((G (t₀ + s) - G t₀) • A))
      (NormedSpace.exp ((G (t₀ + s) - G t₀) • A) * (g (t₀ + s) • A)) s := by
  have h1 : HasDerivAt (fun s => G (t₀ + s) - G t₀) (g (t₀ + s)) s :=
    ((hG (t₀ + s)).comp_const_add t₀ s).sub_const _
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) A (G (t₀ + s) - G t₀)
  rw [mul_smul_comm]
  exact h2.scomp s h1

/-- **Each edge carries the profile's increment across it.** -/
theorem profile_link (c : Fin 3) (f : V →L[ℝ] ℝ) (G g : ℝ → ℝ) (hG : ∀ t, HasDerivAt G (g t) t)
    (a : Fin 4 → ℝ) (r : Realization c (profile f g a)) (y v : V) (hv : f v = 1) (s : ℝ) :
    r.packet y v s = NormedSpace.exp ((G (f y + s) - G (f y)) • gen c a) := by
  have key : ∀ t : ℝ, packetA c (profile f g a) (y + t • v) v = g (f y + t) • gen c a := by
    intro t
    rw [packetA_profile, map_add, map_smul, hv, smul_eq_mul, mul_one, mul_one]
  symm
  refine transport_unique (B := fun t => g (f y + t) • gen c a) (fun t => ?_) ?_
    (r.packet_zero y v) (fun t => profile_transport _ G g hG (f y) t) (fun t => ?_)
    (r.packet_unitary y v) s
  · have h := packet_skew c (profile f g a) (y + t • v) v
    rwa [key] at h
  · simp
  · have h := r.packet_deriv y v t
    rwa [key] at h

/-- The smooth transition is differentiable, with C² derivative. -/
lemma transition_diff : Differentiable ℝ Real.smoothTransition ∧
    ContDiff ℝ 2 (deriv Real.smoothTransition) := by
  have h := contDiff_infty_iff_deriv.1 (Real.smoothTransition.contDiff (n := ⊤))
  exact ⟨h.1, by simpa using contDiff_infty.1 h.2 2⟩

/-- Controls for a wall of links `exp A` across the slab `0 ≤ f ≤ 1`. -/
def wall (f : V →L[ℝ] ℝ) (a : Fin 4 → ℝ) : Controls := profile f (deriv Real.smoothTransition) a

theorem wall_c2 (f : V →L[ℝ] ℝ) (a : Fin 4 → ℝ) : ∀ j, ContDiff ℝ 2 (wall f a j) :=
  profile_c2 f _ transition_diff.2 a

lemma wall_link_eq (c : Fin 3) (f : V →L[ℝ] ℝ) (a : Fin 4 → ℝ) (r : Realization c (wall f a))
    (y v : V) (hv : f v = 1) :
    r.packet y v 1 = NormedSpace.exp ((Real.smoothTransition (f y + 1) -
      Real.smoothTransition (f y)) • gen c a) :=
  profile_link c f _ _ (fun t => (transition_diff.1 t).hasDerivAt) a r y v hv 1

/-- **Edges leaving the slab `f = 0` carry `exp A`.** -/
theorem wall_link (c : Fin 3) (f : V →L[ℝ] ℝ) (a : Fin 4 → ℝ) (r : Realization c (wall f a))
    (y v : V) (hv : f v = 1) (hy : f y = 0) :
    r.packet y v 1 = NormedSpace.exp (gen c a) := by
  rw [wall_link_eq c f a r y v hv, hy, zero_add, Real.smoothTransition.one,
    Real.smoothTransition.zero, sub_zero, one_smul]

/-- **Edges above the wall carry the identity.** -/
theorem wall_free_above (c : Fin 3) (f : V →L[ℝ] ℝ) (a : Fin 4 → ℝ) (r : Realization c (wall f a))
    (y v : V) (hv : f v = 1) (hy : 1 ≤ f y) : r.packet y v 1 = 1 := by
  rw [wall_link_eq c f a r y v hv, Real.smoothTransition.one_of_one_le hy,
    Real.smoothTransition.one_of_one_le (by linarith), sub_self, zero_smul, NormedSpace.exp_zero]

/-- **Edges below the wall carry the identity.** -/
theorem wall_free_below (c : Fin 3) (f : V →L[ℝ] ℝ) (a : Fin 4 → ℝ) (r : Realization c (wall f a))
    (y v : V) (hv : f v = 1) (hy : f y ≤ -1) : r.packet y v 1 = 1 := by
  rw [wall_link_eq c f a r y v hv, Real.smoothTransition.zero_of_nonpos (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith), sub_self, zero_smul, NormedSpace.exp_zero]

end PMAction.ProfileControls
