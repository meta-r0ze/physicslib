import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Basic.Real.Basic

/-!
# Contour counting and the polymer smallness condition

This is the volume-independent counting that a polymer (cluster) expansion needs. It is the first
step of attacking the off-diagonal problem (#2 in the Yang–Mills gap branch) the way quantum
Pirogov–Sinai theory does. Excitations of PM's cost are contours: connected sets, with cost equal
to their size (`DefectGap`: one transition per boundary edge, the Peierls condition). A small
off-diagonal term of strength `q` per site gives each contour a weight `≤ q^|γ|`. The expansion
converges, with bounds that do not depend on the volume, once contours of size `k` through a
point are at most exponentially many in `k`.

* `Animal G v S`: `S` is a connected set grown from the root `v` (a rooted lattice animal).
* `spanning_walk`: every animal of size `k` is the vertex set of a closed walk from `v` of length
  exactly `2(k − 1)` (a doubled spanning tree).
* `walks_from_le`: on a graph of maximum degree `D` there are at most `D^n` walks of length `n`
  starting at a given site.
* `card_animals_le`: at most `D^(2(k − 1))` animals of size `k` contain a given site. The bound
  depends only on the local degree, not on the size of the graph.
* `polymer_sum_le`: with weight `x` per site, `Σ_{k ≤ M} #animals(k) · x^k ≤ x / (1 − D²x)`
  whenever `D²x < 1`, uniformly in `M` and in the volume.
* `kotecky_preiss_condition`: with activity `q` and KP weight `c = e^a` per site, the
  Kotecký–Preiss sum through a site is at most `1` once `q·c·(1 + D²) ≤ 1`.

## What is not here

The Kotecký–Preiss *theorem* itself (the condition implies convergence of the cluster
expansion, hence analyticity of the free energy and exponential clustering) is not formalized.
Neither is the Duhamel/Dyson expansion that turns a quantum off-diagonal term into contour
activities. Both are standard but long. This file proves the combinatorial input that makes
them volume-uniform.
-/

namespace PMAction.MassGap.ContourCount
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A rooted lattice animal: a connected set grown from `v` one neighbour at a time. -/
inductive Animal (v : V) : Finset V → Prop
  | single : Animal v {v}
  | grow {S : Finset V} {t u : V} : Animal v S → t ∈ S → G.Adj t u → u ∉ S →
      Animal v (insert u S)

omit [Fintype V] [DecidableRel G.Adj] in
theorem Animal.root_mem {v : V} {S : Finset V} (h : Animal G v S) : v ∈ S := by
  induction h with
  | single => simp
  | grow _ _ _ _ ih => exact Finset.mem_insert_of_mem ih

omit [Fintype V] [DecidableRel G.Adj] in
/-- **Every animal is spanned by a closed walk of length `2(|S| − 1)`.** -/
theorem spanning_walk {v : V} {S : Finset V} (h : Animal G v S) :
    ∃ p : G.Walk v v, p.support.toFinset = S ∧ p.length = 2 * (S.card - 1) := by
  induction h with
  | single => exact ⟨SimpleGraph.Walk.nil, by simp, by simp⟩
  | @grow S t u _ ht hadj hu ih =>
    obtain ⟨p, hp, hl⟩ := ih
    have htp : t ∈ p.support := by rw [← List.mem_toFinset, hp]; exact ht
    let q : G.Walk v v := (p.takeUntil t htp).append
      (SimpleGraph.Walk.cons hadj (SimpleGraph.Walk.cons hadj.symm (p.dropUntil t htp)))
    have hsplit : ∀ x, x ∈ p.support ↔
        x ∈ (p.takeUntil t htp).support ∨ x ∈ (p.dropUntil t htp).support := by
      intro x
      conv_lhs => rw [← p.take_spec htp]
      exact SimpleGraph.Walk.mem_support_append_iff _ _
    have htd : t ∈ (p.dropUntil t htp).support := SimpleGraph.Walk.start_mem_support _
    refine ⟨q, ?_, ?_⟩
    · ext x
      simp only [q, List.mem_toFinset, SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.support_cons, List.mem_cons, Finset.mem_insert]
      rw [← hp, List.mem_toFinset, hsplit]
      constructor
      · rintro (h | h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (h ▸ htd))
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inr h))
    · have hlen : (p.takeUntil t htp).length + (p.dropUntil t htp).length = p.length := by
        rw [← SimpleGraph.Walk.length_append, p.take_spec htp]
      have hpos : 0 < S.card := Finset.card_pos.mpr ⟨t, ht⟩
      simp only [q, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
        Finset.card_insert_of_notMem hu]
      omega

/-! ### Counting walks -/

/-- Walks of length `n` starting at `u`, over all endpoints. -/
def walksFrom (n : ℕ) (u : V) : ℕ := ∑ w, (G.finsetWalkLength n u w).card

/-- **At most `D^n` walks of length `n` start at any site.** -/
theorem walks_from_le (D : ℕ) (hD : ∀ w, G.degree w ≤ D) (n : ℕ) (u : V) :
    walksFrom G n u ≤ D ^ n := by
  induction n generalizing u with
  | zero =>
    unfold walksFrom
    rw [Finset.sum_eq_single u]
    · simp [SimpleGraph.finsetWalkLength]
    · intro w _ hw
      simp [SimpleGraph.finsetWalkLength, Ne.symm hw]
    · simp
  | succ n ih =>
    unfold walksFrom at ih ⊢
    have hstep : ∀ w, (G.finsetWalkLength (n + 1) u w).card ≤
        ∑ x : G.neighborSet u, (G.finsetWalkLength n x w).card := by
      intro w
      simp only [SimpleGraph.finsetWalkLength]
      refine (Finset.card_biUnion_le).trans ?_
      simp
    calc ∑ w, (G.finsetWalkLength (n + 1) u w).card
        ≤ ∑ w, ∑ x : G.neighborSet u, (G.finsetWalkLength n x w).card :=
          Finset.sum_le_sum fun w _ => hstep w
      _ = ∑ x : G.neighborSet u, ∑ w, (G.finsetWalkLength n x w).card := Finset.sum_comm
      _ ≤ ∑ _x : G.neighborSet u, D ^ n := Finset.sum_le_sum fun x _ => ih x
      _ = Fintype.card (G.neighborSet u) * D ^ n := by simp
      _ ≤ D * D ^ n := by
          apply Nat.mul_le_mul_right
          rw [SimpleGraph.card_neighborSet_eq_degree]; exact hD u
      _ = D ^ (n + 1) := (pow_succ' D n).symm

/-! ### Counting animals -/

/-- Animals of size `k` rooted at `v`. -/
noncomputable def animals (v : V) (k : ℕ) : Finset (Finset V) := by
  classical exact univ.filter fun S => Animal G v S ∧ S.card = k

/-- **Volume-independent contour count.** At most `D^(2(k−1))` animals of size `k` contain `v`. -/
theorem card_animals_le (D : ℕ) (hD : ∀ w, G.degree w ≤ D) (v : V) (k : ℕ) :
    (animals G v k).card ≤ D ^ (2 * (k - 1)) := by
  classical
  have hsub : animals G v k ⊆ (G.finsetWalkLength (2 * (k - 1)) v v).image
      fun p => p.support.toFinset := by
    intro S hS
    simp only [animals, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    obtain ⟨p, hp, hl⟩ := spanning_walk G hS.1
    rw [Finset.mem_image]
    refine ⟨p, ?_, hp⟩
    rw [SimpleGraph.mem_finsetWalkLength_iff, hl, hS.2]
  calc (animals G v k).card
      ≤ ((G.finsetWalkLength (2 * (k - 1)) v v).image fun p => p.support.toFinset).card :=
        Finset.card_le_card hsub
    _ ≤ (G.finsetWalkLength (2 * (k - 1)) v v).card := Finset.card_image_le
    _ ≤ walksFrom G (2 * (k - 1)) v :=
        Finset.single_le_sum (f := fun w => (G.finsetWalkLength (2 * (k - 1)) v w).card)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    _ ≤ D ^ (2 * (k - 1)) := walks_from_le G D hD _ v

/-! ### The polymer sum -/

/-- The weighted sum over animals through `v` with sizes `1, …, M` and weight `x` per site. -/
noncomputable def polymerSum (v : V) (x : ℝ) (M : ℕ) : ℝ :=
  ∑ k ∈ range M, ((animals G v (k + 1)).card : ℝ) * x ^ (k + 1)

/-- **The polymer sum is bounded uniformly in the cutoff and the volume.** -/
theorem polymer_sum_le (D : ℕ) (hD : ∀ w, G.degree w ≤ D) (v : V) {x : ℝ} (hx : 0 ≤ x)
    (hr : (D : ℝ) ^ 2 * x < 1) (M : ℕ) :
    polymerSum G v x M ≤ x / (1 - (D : ℝ) ^ 2 * x) := by
  set r : ℝ := (D : ℝ) ^ 2 * x
  have hr0 : 0 ≤ r := by positivity
  have hterm : ∀ k ∈ range M, ((animals G v (k + 1)).card : ℝ) * x ^ (k + 1) ≤ x * r ^ k := by
    intro k _
    have hc : ((animals G v (k + 1)).card : ℝ) ≤ (D : ℝ) ^ (2 * k) := by
      have := card_animals_le G D hD v (k + 1)
      simp only [Nat.add_sub_cancel] at this
      exact_mod_cast this
    calc ((animals G v (k + 1)).card : ℝ) * x ^ (k + 1)
        ≤ (D : ℝ) ^ (2 * k) * x ^ (k + 1) :=
          mul_le_mul_of_nonneg_right hc (pow_nonneg hx _)
      _ = x * r ^ k := by simp only [r, mul_pow, ← pow_mul]; ring
  have hgeom : (∑ k ∈ range M, r ^ k) * (1 - r) = 1 - r ^ M := geom_sum_mul_neg r M
  have hpos : 0 < 1 - r := by linarith
  have hgs : ∑ k ∈ range M, r ^ k ≤ 1 / (1 - r) := by
    rw [le_div_iff₀ hpos, hgeom]
    linarith [pow_nonneg hr0 M]
  calc polymerSum G v x M ≤ ∑ k ∈ range M, x * r ^ k := Finset.sum_le_sum hterm
    _ = x * ∑ k ∈ range M, r ^ k := by rw [Finset.mul_sum]
    _ ≤ x * (1 / (1 - r)) := mul_le_mul_of_nonneg_left hgs hx
    _ = x / (1 - r) := by ring

/-- **The Kotecký–Preiss condition holds for small activity, uniformly in volume.** With activity
`q ≥ 0` per site and KP weight `c ≥ 0` per site (`c = e^a`, so the KP inequality is
`Σ_{γ ∋ v} q^|γ| e^{a|γ|} ≤ a` with `a = 1` at `c = e`), the sum through any site is at most `1`
once `q·c·(1 + D²) ≤ 1`. -/
theorem kotecky_preiss_condition (D : ℕ) (hD : ∀ w, G.degree w ≤ D) (v : V) {q c : ℝ}
    (hq : 0 ≤ q) (hc : 0 ≤ c) (hsmall : q * c * (1 + (D : ℝ) ^ 2) ≤ 1) (M : ℕ) :
    polymerSum G v (q * c) M ≤ 1 := by
  have hx : 0 ≤ q * c := mul_nonneg hq hc
  by_cases h0 : q * c = 0
  · unfold polymerSum
    rw [h0]
    apply le_trans (le_of_eq _) zero_le_one
    exact Finset.sum_eq_zero fun k _ => by simp
  have hxpos : 0 < q * c := lt_of_le_of_ne hx (Ne.symm h0)
  have hr : (D : ℝ) ^ 2 * (q * c) < 1 := by nlinarith
  have hb := polymer_sum_le G D hD v hx hr M
  have hden : 0 < 1 - (D : ℝ) ^ 2 * (q * c) := by linarith
  have : q * c / (1 - (D : ℝ) ^ 2 * (q * c)) ≤ 1 := by
    rw [div_le_one hden]; nlinarith
  linarith

end PMAction.MassGap.ContourCount
