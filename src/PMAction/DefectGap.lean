import PMSubstrate.Distinctions
import PMAction.GapStability
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# The defect gap: a discrete cost spectrum with a unique vacuum

This is the *gap* half of the Yang–Mills branch, stated for PM's own excitation cost.
The *existence/continuity* half is elsewhere: Paper I prices the defect boundary by a
continuous perimeter (`Z_CAP = πΔ`, Barbier) although the substrate is the discrete `E₈`
lattice, and Paper II builds the finite-volume measure, gauge invariance, reflection
positivity and the classical continuum limit (`LatticeGibbs`, `ReciprocalReflection`,
`OsterwalderSchrader`, `LatticeSiteAction`). Here the same discreteness is read the other way:
the cost of an excitation is a **count of transitions**, so it cannot be arbitrarily small.

Setting: any finite connected graph `G` of sites (any volume, any shape), configurations
`x : V → Bool` (vacuum / defect), and Paper I's cost — one transition per boundary edge
(`PMSubstrate.Distinctions.cost_per_cut_edge`).

* `cost_eq_localCost`: the cost used here is Paper I's local, vacuum-relative,
  relabeling-symmetric cost.
* `cost_eq_zero_iff`: cost zero exactly on the **uniform** configurations — the vacuum and its
  relabeling, which Closure identifies. So the ground state is unique up to that relabeling.
* `cost_ge_one`: every non-uniform configuration costs **at least one transition**.
* `gap_uniform_in_volume`: the same bound, quantified over every finite connected graph. The
  constant `1` does not depend on the number of sites.
* `survival_vacuum`, `survival_excited`: with per-transition survival `p ∈ (0,1)`
  (`PMSubstrate.Vacuum.survival_geometric`: hazard-form survival of `n` transitions is `p ^ n`),
  the vacuum survives with weight `1` and every excitation with weight at most `p`.
* `transfer_contracts_excitations`: the diagonal one-tick transfer operator
  `v ↦ (x ↦ p ^ cost x · v x)` shrinks every vector supported off the vacuum by at least `p`
  in `ℓ²`. In Euclidean language the top eigenvalue is `1` (vacuum) and the rest of the spectrum
  is `≤ p`, so the decay rate of every excitation is at least `m = −log p > 0` per tick,
  uniformly in volume.

## What this does and does not prove

This is a gap for the diagonal (classical) PM cost operator. It is volume-uniform because the
cost is integer-valued and the vacuum is unique; that is the PM content. It is **not** the Clay
statement: that asks for a gap in a continuum quantum Yang–Mills theory on `ℝ⁴`, where the
lattice spacing is sent to zero and the off-diagonal (kinetic/plaquette) part of the transfer
matrix is present. `GapStability` states exactly how much off-diagonal perturbation the gap
survives, which is where the remaining problem sits.
-/

namespace PMAction.DefectGap
open Finset PMSubstrate.Distinctions

variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- PM's excitation cost in transition units: the number of boundary (cut) edges. -/
def cost (x : V → Bool) : ℕ := (cutEdges G x).card

/-- The cost is Paper I's local, vacuum-relative, relabeling-symmetric cost at one transition
per boundary edge. -/
theorem cost_eq_localCost (x : V → Bool) :
    localCost G (fun _ => 0) (fun a b => if a = b then 0 else 1 / 2) x = (cost G x : ℝ) :=
  cost_per_cut_edge G x

/-- A configuration is uniform: every site in the same state (the vacuum or its relabeling). -/
def Uniform (x : V → Bool) : Prop := ∀ u v, x u = x v

omit [Fintype V] [LinearOrder V] [DecidableRel G.Adj] in
/-- Along any walk between two sites in different states some edge joins different states. -/
theorem exists_distinct_adj_of_walk (x : V → Bool) :
    ∀ {u v : V} (_ : G.Walk u v), x u ≠ x v → ∃ a b, G.Adj a b ∧ x a ≠ x b := by
  intro u v p
  induction p with
  | nil => intro h; exact absurd rfl h
  | @cons a b c hab p ih =>
    intro h
    by_cases hb : x a = x b
    · exact ih (fun h' => h (hb.trans h'))
    · exact ⟨a, b, hab, hb⟩

/-- **A non-uniform configuration on a connected graph has a boundary edge.** -/
theorem cutEdges_nonempty (hG : G.Connected) (x : V → Bool) (hx : ¬ Uniform x) :
    (cutEdges G x).Nonempty := by
  simp only [Uniform, not_forall] at hx
  obtain ⟨u, v, huv⟩ := hx
  obtain ⟨p⟩ := hG.preconnected u v
  obtain ⟨a, b, hab, hne⟩ := exists_distinct_adj_of_walk G x p huv
  rcases lt_or_gt_of_ne hab.ne with h | h
  · exact ⟨(a, b), by simp [cutEdges, distinctions, pairs, hab, hne, h]⟩
  · have h' : b < a := h
    exact ⟨(b, a), by simp [cutEdges, distinctions, pairs, G.adj_symm hab, Ne.symm hne, h']⟩

/-- **The gap: every excitation costs at least one transition.** -/
theorem cost_ge_one (hG : G.Connected) (x : V → Bool) (hx : ¬ Uniform x) : 1 ≤ cost G x :=
  Finset.card_pos.mpr (cutEdges_nonempty G hG x hx)

/-- Uniform configurations cost nothing. -/
theorem cost_uniform (x : V → Bool) (hx : Uniform x) : cost G x = 0 := by
  unfold cost cutEdges distinctions
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp _
  exact (Finset.mem_filter.mp hp).2 (hx _ _)

/-- **Unique vacuum.** On a connected graph the zero-cost configurations are exactly the uniform
ones (the vacuum and its Closure relabeling). -/
theorem cost_eq_zero_iff (hG : G.Connected) (x : V → Bool) : cost G x = 0 ↔ Uniform x := by
  constructor
  · intro h
    by_contra hx
    have := cost_ge_one G hG x hx
    omega
  · exact cost_uniform G x

/-- **The gap is uniform in volume.** For every finite connected site graph, of any size,
every excitation costs at least one transition. -/
theorem gap_uniform_in_volume :
    ∀ {W : Type} [Fintype W] [LinearOrder W] (H : SimpleGraph W) [DecidableRel H.Adj],
      H.Connected → ∀ y : W → Bool, ¬ Uniform y → 1 ≤ cost H y := by
  intro W _ _ H _ hH y hy
  exact cost_ge_one H hH y hy

/-! ### Survival weights and the transfer operator -/

/-- Survival weight of a configuration: `p` per transition (hazard form). -/
def survival (p : ℝ) (x : V → Bool) : ℝ := p ^ cost G x

/-- The vacuum survives with weight one. -/
theorem survival_vacuum (p : ℝ) (x : V → Bool) (hx : Uniform x) : survival G p x = 1 := by
  simp [survival, cost_uniform G x hx]

theorem survival_nonneg {p : ℝ} (hp0 : 0 ≤ p) (x : V → Bool) : 0 ≤ survival G p x :=
  pow_nonneg hp0 _

/-- **Every excitation survives with weight at most `p`.** -/
theorem survival_excited (hG : G.Connected) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : V → Bool) (hx : ¬ Uniform x) : survival G p x ≤ p := by
  unfold survival
  calc p ^ cost G x ≤ p ^ 1 := pow_le_pow_of_le_one hp0 hp1 (cost_ge_one G hG x hx)
    _ = p := pow_one p

/-- **The transfer operator contracts the excited sector.** The diagonal one-tick transfer
`v ↦ (x ↦ survival x · v x)` maps any vector vanishing on the vacuum to one whose `ℓ²` norm
squared is at most `p²` times the original. The bound does not depend on the volume. -/
theorem transfer_contracts_excitations (hG : G.Connected) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (v : (V → Bool) → ℝ) (hv : ∀ x, Uniform x → v x = 0) :
    ∑ x, (survival G p x * v x) ^ 2 ≤ p ^ 2 * ∑ x, v x ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : Uniform x
  · simp [hv x hx]
  · have h0 := survival_nonneg G hp0 x
    have h1 := survival_excited G hG hp0 hp1 x hx
    have h2 : survival G p x ^ 2 ≤ p ^ 2 := by nlinarith
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)

/-- On the vacuum the transfer operator acts as the identity. -/
theorem transfer_fixes_vacuum (p : ℝ) (v : (V → Bool) → ℝ) (hv : ∀ x, ¬ Uniform x → v x = 0)
    (x : V → Bool) : survival G p x * v x = v x := by
  by_cases hx : Uniform x
  · rw [survival_vacuum G p x hx, one_mul]
  · rw [hv x hx, mul_zero]

/-! ### The gap under an off-diagonal perturbation

`GapStability` gives the abstract quadratic-form statement; instantiating its gap `m` with the PM
cost gap (`m = 1` transition) and its vacuum predicate with `Uniform` gives the PM-side condition
on the off-diagonal (kinetic/plaquette) part of a transfer matrix. -/

/-- **The PM cost gap survives an off-diagonal perturbation.** With the diagonal gap `m = 1`
(`cost_ge_one`) and `GapStability.gap_pos`, any perturbation form `W` with `|W v| ≤ ε‖v‖²` and
`ε < 1/2` keeps the excited sector strictly above the vacuum. This is the PM-side gap condition;
the open content is a *volume-uniform* bound on `ε` for the actual plaquette/kinetic part, where
`ε` is extensive (see `PMAction` `OVERVIEW.md`, the Yang–Mills scope note). -/
theorem gap_survives_offdiagonal (hG : G.Connected) (ε : ℝ)
    (W : ((V → Bool) → ℝ) → ℝ) (hW : ∀ v, |W v| ≤ ε * GapStability.normSq v)
    (hε : ε < 1 / 2) (v u : (V → Bool) → ℝ)
    (hv : ∀ x, Uniform x → v x = 0) (hu : ∀ x, ¬ Uniform x → u x = 0)
    (hv1 : GapStability.normSq v = 1) (hu1 : GapStability.normSq u = 1) :
    GapStability.diagForm (fun x => (cost G x : ℝ)) u + W u <
      GapStability.diagForm (fun x => (cost G x : ℝ)) v + W v := by
  refine GapStability.gap_pos Uniform 1 ε (fun x => (cost G x : ℝ)) W ?_ ?_ hW hε
    v u hv hu hv1 hu1
  · intro x hx; rw [cost_uniform G x hx]; norm_num
  · intro x hx; exact_mod_cast cost_ge_one G hG x hx

end PMAction.DefectGap
