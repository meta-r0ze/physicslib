import PMKAutomaton.Machine.FiniteRootWordControls

/-!
# Arbitrary finite root programs on a finite D4 edge configuration

Each distinct geometric edge has its own finite root sequence, rate data and
length. Smooth bumps isolate their middle halves exactly as in the one-pass
construction. The supplied word on each edge is realized in its stated order,
including repeated passes and the empty program. This interpolates finite link
data; it does not derive that data, physical control admission or a clock.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.FiniteConfigurationControls
open Matrix NativeCoherentLinks NativePacketUpdate Set
open scoped Matrix.Norms.L2Operator

structure Edge where
  y : V
  v : V
  f : V →L[ℝ] ℝ
  hv : f v = 1
  length : ℕ
  roots : Fin length → Fin 4
  rates : Fin length → ℝ

/-- Only geometry is reused from the one-pass edge type; its old rates are zero.
The actual supplied program is carried by roots and rates above. -/
def geometry (e : Edge) : ConfigurationControls.Edge := ⟨e.y,e.v,e.f,e.hv,0⟩
def seg (e : Edge) := ConfigurationControls.seg (geometry e)
def mid (e : Edge) := ConfigurationControls.mid (geometry e)
def localControls (e : Edge) := FiniteRootWordControls.controls e.f (e.f e.y) e.roots e.rates

def controls {ι : Type*} [Fintype ι] (E : ι → Edge) (χ : ι → V → ℝ) : Controls :=
  fun j x => ∑ e, χ e x • localControls (E e) j x

lemma agree {ι : Type*} [Fintype ι] (E : ι → Edge) (χ : ι → V → ℝ)
    (hone : ∀ e, EqOn (χ e) 1 (mid (E e)))
    (hzero : ∀ e e', e ≠ e' → EqOn (χ e) 0 (seg (E e')))
    (e : ι) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (j : Fin 4) :
    controls E χ j ((E e).y+t • (E e).v) = localControls (E e) j ((E e).y+t • (E e).v) := by
  have hx : (E e).y+t • (E e).v ∈ seg (E e) := ⟨t,ht,rfl⟩
  unfold controls
  rw [Finset.sum_eq_single e]
  · by_cases hm : t ∈ Icc (1/4 : ℝ) (3/4)
    · rw [(hone e ⟨t,hm,rfl⟩ : χ e ((E e).y+t • (E e).v) = 1), Pi.one_apply, one_smul]
    · have ht' : (E e).f ((E e).y+t • (E e).v) - (E e).f (E e).y = t := by
        rw [map_add, map_smul, (E e).hv, smul_eq_mul]
        ring
      have hout : t ≤ 1/4 ∨ 3/4 ≤ t := by
        simp only [mem_Icc, not_and_or, not_le] at hm
        rcases hm with h | h
        · left; linarith
        · right; linarith
      have hz : localControls (E e) j ((E e).y+t • (E e).v) = 0 := by
        unfold localControls FiniteRootWordControls.controls
        rw [ht']
        simp [FiniteRootWordControls.rate_outside _ hout]
      rw [hz, smul_zero]
  · intro e' _ he'
    rw [(hzero e' e he' hx : χ e' ((E e).y+t • (E e).v) = 0), Pi.zero_apply, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ e) h

/-- One smooth control field carries arbitrary supplied finite programs on every edge. -/
theorem configuration_realized {ι : Type*} [Fintype ι] (c : Fin 3) (E : ι → Edge)
    (hdisj : ∀ e e', e ≠ e' → Disjoint (mid (E e)) (seg (E e'))) :
    ∃ w : Controls, (∀ j, ContDiff ℝ 2 (w j)) ∧
      ∀ (r : Realization c w) (e : ι), r.packet (E e).y (E e).v 1 =
        FiniteRootWordControls.word c (E e).roots (E e).rates := by
  choose χ hχ hone hzero using ConfigurationControls.bump_exists (fun e => geometry (E e)) hdisj
  refine ⟨controls E χ, fun j => ?_, fun r e => ?_⟩
  · unfold controls
    exact ContDiff.sum fun e _ => (hχ e).smul
      (FiniteRootWordControls.controls_c2 (E e).f ((E e).f (E e).y) (E e).roots (E e).rates j)
  · rw [EdgeLocality.edge_local c r
      (realized c _ (FiniteRootWordControls.controls_c2 (E e).f ((E e).f (E e).y)
        (E e).roots (E e).rates)) (E e).y (E e).v fun t ht =>
          ConfigurationControls.packetA_congr c _ _ fun j => agree E χ hone hzero e t ht j]
    exact FiniteRootWordControls.word_link c _ _ _ _ _ _ _ (E e).hv rfl

/-- Different D4 edges may carry different program lengths and repeated root passes. -/
theorem d4_configuration_realized {ι : Type*} [Fintype ι] (c : Fin 3)
    (Y : ι → Fin 4 → ℤ) (hY : ∀ e, Even (∑ i, Y e i))
    (r : ι → AxisHop.Tri) (hr : ∀ e, AxisHop.IsRoot (r e))
    (n : ι → ℕ) (roots : ∀ e, Fin (n e) → Fin 4) (a : ∀ e, Fin (n e) → ℝ)
    (hdist : ∀ e e', e ≠ e' → ¬ D4EdgeSeparation.sameSeg (Y e) (r e) (Y e') (r e')) :
    ∃ w : Controls, (∀ j, ContDiff ℝ 2 (w j)) ∧
      ∀ (R : Realization c w) (e : ι),
        R.packet (D4EdgeSeparation.pt (Y e)) (D4EdgeSeparation.dir (r e)) 1 =
          FiniteRootWordControls.word c (roots e) (a e) := by
  have hne : ∀ e, D4EdgeSeparation.dir (r e) ≠ 0 := fun e h => by
    obtain ⟨i, hi⟩ := D4EdgeSeparation.root_nonzero (hr e)
    have h0 := congrFun h i
    simp only [D4EdgeSeparation.dir, Pi.zero_apply, Int.cast_eq_zero] at h0
    exact hi ((D4EdgeSeparation.val_eq_zero _).1 h0)
  choose f hf using fun e => SeparatingDual.exists_eq_one (R := ℝ) (hne e)
  let E : ι → Edge := fun e =>
    ⟨D4EdgeSeparation.pt (Y e),D4EdgeSeparation.dir (r e),f e,hf e,n e,roots e,a e⟩
  obtain ⟨w, hw, hlink⟩ := configuration_realized c E fun e e' h =>
    D4EdgeSeparation.d4_disjoint _ _ (hY e) (hY e') _ _ (hr e) (hdist e e' h)
      (geometry (E e)) (geometry (E e')) rfl rfl rfl rfl
  exact ⟨w,hw,fun R e => hlink R e⟩

end PMAction.FiniteConfigurationControls
