import PMAction.Machine.ConfigurationControls
import PMAction.Machine.SliceHop

/-!
# Distinct `D₄` edges are separated

`ConfigurationControls.configuration_realized` needs each edge's middle half to miss every other
edge's segment. This module proves it for the `D₄` lattice and closes the controls route for finite
configurations.

A lattice edge is `Y + [0, 1] r` with `Y ∈ ℤ⁴` of even coordinate sum and `r` a root (two entries
`±1`). Suppose a point of the middle half of `(Y, r)` lies on the segment of `(Y', r')`:
`Y + s r = Y' + t r'`, `s ∈ [1/4, 3/4]`, `t ∈ [0, 1]`.

* `t_strict`: on a coordinate where `r` is nonzero, `t = 0` or `t = 1` would make `±s` an integer
  plus an integer, so `0 < t < 1`.
* `coord`: on each coordinate, with `k = Yᵢ − Y'ᵢ ∈ ℤ`, `aᵢ = rᵢ`, `bᵢ = r'ᵢ`: either both are
  zero and `k = 0`, or `bᵢ = aᵢ ≠ 0` and `k = 0`, or `bᵢ = −aᵢ ≠ 0` and `k = −aᵢ`. Nothing else
  fits the bounds.
* `comb` (finite check): if the coordinates where `r'` reverses `r` are neither none nor all, the
  difference `Y − Y'` has odd coordinate sum, contradicting `D₄`.
* `separated`: so the two edges are the same segment: `(Y', r') = (Y, r)` or `(Y + r, −r)`.
* `d4_configuration_realized`: **every finite configuration of distinct `D₄` edges, each with its
  own root rates, is realized by one set of C² controls**, and each edge carries its own root
  word.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.D4EdgeSeparation
open AxisHop ConfigurationControls NativeCoherentLinks Set

lemma val_cases (x : Fin 3) : val x = -1 ∨ val x = 0 ∨ val x = 1 := by fin_cases x <;> decide

lemma val_eq_zero (x : Fin 3) : val x = 0 ↔ x = 0 := by fin_cases x <;> decide

lemma val_nonzero (x : Fin 3) (hx : x ≠ 0) : val x = -1 ∨ val x = 1 := by
  fin_cases x <;> first | exact absurd rfl hx | decide

lemma root_nonzero {r : Tri} (hr : IsRoot r) : ∃ i, r i ≠ 0 := by
  have h : 0 < (Finset.univ.filter fun i => r i ≠ 0).card := by unfold IsRoot at hr; omega
  obtain ⟨i, hi⟩ := Finset.card_pos.1 h
  exact ⟨i, (Finset.mem_filter.1 hi).2⟩

/-- **The far edge's parameter is strictly inside.** -/
lemma t_strict {s t : ℝ} (hs1 : 1 / 4 ≤ s) (hs2 : s ≤ 3 / 4) (ht1 : 0 ≤ t) (ht2 : t ≤ 1)
    (a b k : ℤ) (ha : a = -1 ∨ a = 1) (hb : b = -1 ∨ b = 0 ∨ b = 1)
    (hk : (k : ℝ) = t * b - s * a) : 0 < t ∧ t < 1 := by
  have h1 : (k : ℝ) < 2 := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> push_cast at hk <;> nlinarith
  have h2 : (-2 : ℝ) < k := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> push_cast at hk <;> nlinarith
  have h1' : k < 2 := by exact_mod_cast h1
  have h2' : -2 < k := by exact_mod_cast h2
  have hk3 : k = -1 ∨ k = 0 ∨ k = 1 := by omega
  by_contra hn
  have ht : t = 0 ∨ t = 1 := by
    rcases not_and_or.1 hn with h | h
    · left; linarith [not_lt.1 h]
    · right; linarith [not_lt.1 h]
  rcases ht with rfl | rfl <;> rcases ha with rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hk3 with rfl | rfl | rfl <;> push_cast at hk <;> linarith

/-- **The per-coordinate cases.** -/
lemma coord {s t : ℝ} (hs1 : 1 / 4 ≤ s) (hs2 : s ≤ 3 / 4) (ht1 : 0 < t) (ht2 : t < 1)
    (a b k : ℤ) (ha : a = -1 ∨ a = 0 ∨ a = 1) (hb : b = -1 ∨ b = 0 ∨ b = 1)
    (hk : (k : ℝ) = t * b - s * a) :
    (a = 0 ∧ b = 0 ∧ k = 0) ∨ (a ≠ 0 ∧ b = a ∧ k = 0) ∨ (a ≠ 0 ∧ b = -a ∧ k = -a) := by
  have h1 : (k : ℝ) < 2 := by
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> push_cast at hk <;>
      nlinarith
  have h2 : (-2 : ℝ) < k := by
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> push_cast at hk <;>
      nlinarith
  have h1' : k < 2 := by exact_mod_cast h1
  have h2' : -2 < k := by exact_mod_cast h2
  have hk3 : k = -1 ∨ k = 0 ∨ k = 1 := by omega
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hk3 with rfl | rfl | rfl <;> push_cast at hk <;> first | decide | (exfalso; linarith)

/-- The allowed coordinate pattern. -/
def okZ (a b : ℤ) : Prop := (a = 0 ∧ b = 0) ∨ (a ≠ 0 ∧ b = a) ∨ (a ≠ 0 ∧ b = -a)

instance (a b : ℤ) : Decidable (okZ a b) := by unfold okZ; infer_instance

/-- The coordinate difference the pattern forces. -/
def kk (x y : Fin 3) : ℤ := if val x ≠ 0 ∧ val y = -val x then -val x else 0

/-- **Finite check: a mixed reversal has odd difference.** -/
theorem comb : ∀ r r' : Tri, IsRoot r → (∀ i, okZ (val (r i)) (val (r' i))) →
    Even (∑ i, kk (r i) (r' i)) → (r' = r ∨ ∀ i, val (r' i) = -val (r i)) := by
  decide +kernel

/-- Two lattice edges are the same segment. -/
def sameSeg (Y : Fin 4 → ℤ) (r : Tri) (Y' : Fin 4 → ℤ) (r' : Tri) : Prop :=
  (Y = Y' ∧ r' = r) ∨ (Y' = (fun i => Y i + val (r i)) ∧ ∀ i, val (r' i) = -val (r i))

/-- **A middle point of one `D₄` edge on another edge's segment forces the same segment.** -/
theorem separated (Y Y' : Fin 4 → ℤ) (hY : Even (∑ i, Y i)) (hY' : Even (∑ i, Y' i))
    (r r' : Tri) (hr : IsRoot r) {s t : ℝ} (hs : s ∈ Icc (1 / 4 : ℝ) (3 / 4))
    (ht : t ∈ Icc (0 : ℝ) 1) (h : ∀ i, (Y i : ℝ) + s * val (r i) = Y' i + t * val (r' i)) :
    sameSeg Y r Y' r' := by
  obtain ⟨i0, hi0⟩ := root_nonzero hr
  have hk : ∀ i, ((Y i - Y' i : ℤ) : ℝ) = t * (val (r' i) : ℝ) - s * (val (r i) : ℝ) :=
    fun i => by push_cast; linarith [h i]
  have ht' := t_strict hs.1 hs.2 ht.1 ht.2 _ _ _ (val_nonzero _ hi0) (val_cases _) (hk i0)
  have hc := fun i => coord hs.1 hs.2 ht'.1 ht'.2 _ _ _ (val_cases (r i)) (val_cases (r' i)) (hk i)
  have hkk : ∀ i, Y i - Y' i = kk (r i) (r' i) := fun i => by
    unfold kk
    rcases hc i with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> split_ifs <;> omega
  have hev : Even (∑ i, kk (r i) (r' i)) := by
    have h := hY.sub hY'
    rw [← Finset.sum_sub_distrib] at h
    simpa only [hkk] using h
  have hok : ∀ i, okZ (val (r i)) (val (r' i)) := fun i => by
    have := hc i
    unfold okZ
    omega
  rcases comb r r' hr hok hev with h1 | h1
  · left
    refine ⟨funext fun i => ?_, h1⟩
    have := hkk i
    rw [h1] at this
    unfold kk at this
    split_ifs at this <;> omega
  · right
    refine ⟨funext fun i => ?_, h1⟩
    have := hkk i
    have h1i := h1 i
    unfold kk at this
    split_ifs at this <;> omega

/-- The lattice point as a vector. -/
def pt (Y : Fin 4 → ℤ) : V := fun i => (Y i : ℝ)

/-- The root as a direction. -/
def dir (r : Tri) : V := fun i => (val (r i) : ℝ)

/-- **Distinct `D₄` edges: the middle of one misses the other's segment.** -/
theorem d4_disjoint (Y Y' : Fin 4 → ℤ) (hY : Even (∑ i, Y i)) (hY' : Even (∑ i, Y' i))
    (r r' : Tri) (hr : IsRoot r) (hne : ¬ sameSeg Y r Y' r') (e e' : Edge)
    (hey : e.y = pt Y) (hev : e.v = dir r) (hey' : e'.y = pt Y') (hev' : e'.v = dir r') :
    Disjoint (mid e) (seg e') := by
  rw [Set.disjoint_left]
  rintro x ⟨s, hs, rfl⟩ ⟨t, ht, heq⟩
  apply hne
  refine separated Y Y' hY hY' r r' hr hs ht fun i => ?_
  have := congrFun heq i
  simp only [hey, hev, hey', hev', pt, dir, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
  linarith

/-- **A finite configuration of distinct `D₄` edges is realized by C² controls**, each edge
carrying its own root word. -/
theorem d4_configuration_realized {ι : Type*} [Fintype ι] (c : Fin 3) (Y : ι → Fin 4 → ℤ)
    (hY : ∀ e, Even (∑ i, Y e i)) (r : ι → Tri) (hr : ∀ e, IsRoot (r e)) (a : ι → Fin 4 → ℝ)
    (hdist : ∀ e e', e ≠ e' → ¬ sameSeg (Y e) (r e) (Y e') (r e')) :
    ∃ w : NativeCoherentLinks.Controls, (∀ j, ContDiff ℝ 2 (w j)) ∧
      ∀ (R : NativeCoherentLinks.Realization c w) (e : ι),
        R.packet (pt (Y e)) (dir (r e)) 1 = word c (a e) := by
  have hne : ∀ e, dir (r e) ≠ 0 := fun e h => by
    obtain ⟨i, hi⟩ := root_nonzero (hr e)
    have h0 := congrFun h i
    simp only [dir, Pi.zero_apply, Int.cast_eq_zero] at h0
    exact hi ((val_eq_zero _).1 h0)
  choose f hf using fun e => SeparatingDual.exists_eq_one (R := ℝ) (hne e)
  let E : ι → Edge := fun e => ⟨pt (Y e), dir (r e), f e, hf e, a e⟩
  obtain ⟨w, hw, hlink⟩ := configuration_realized c E fun e e' h =>
    d4_disjoint _ _ (hY e) (hY e') _ _ (hr e) (hdist e e' h) (E e) (E e') rfl rfl rfl rfl
  exact ⟨w, hw, fun R e => hlink R e⟩

end PMAction.D4EdgeSeparation
