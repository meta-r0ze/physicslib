import PMAction.MinimalCube
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-!
# 3D nuclear packing: the surface/volume link count

A nucleus that persists in three dimensions is not a line/ring.  The simplest
3D packing is an `n × n × n` simple-cubic block.  Its link count is

`E(n) = 3 n² (n − 1)`,

so the number of links per nucleon is

`E/A = 3 − 3/n = 3 − 3/A^(1/3)`.

This is the missing persistence count: light nuclei are surface-dominated and
have fewer links per nucleon; heavy nuclei are volume-dominated and approach the
bulk coordination.  The count is combinatorial, not a fitted coefficient.
-/

noncomputable section
namespace PMAtoms
open PMAction.MinimalCube


/-- The lower endpoint of a step in the first coordinate. -/
def cubeBase {n : Nat} (i : Fin (n - 1)) : Fin n :=
  ⟨i.val, by omega⟩

/-- The upper endpoint of a step in the first coordinate. -/
def cubeSucc {n : Nat} (i : Fin (n - 1)) : Fin n :=
  ⟨i.val + 1, by omega⟩

/-- An edge in the first coordinate. -/
def xEdge {n : Nat} (i : Fin (n - 1)) (y z : Fin n) :
    CubeVertex n × CubeVertex n :=
  ((cubeBase i, y, z), (cubeSucc i, y, z))

/-- An edge in the second coordinate. -/
def yEdge {n : Nat} (x : Fin n) (i : Fin (n - 1)) (z : Fin n) :
    CubeVertex n × CubeVertex n :=
  ((x, cubeBase i, z), (x, cubeSucc i, z))

/-- An edge in the third coordinate. -/
def zEdge {n : Nat} (x y : Fin n) (i : Fin (n - 1)) :
    CubeVertex n × CubeVertex n :=
  ((x, y, cubeBase i), (x, y, cubeSucc i))

/-- First-coordinate edges. -/
def xEdges (n : Nat) : Finset (CubeVertex n × CubeVertex n) :=
  ((Finset.univ : Finset (Fin (n - 1) × Fin n × Fin n)).image
    (fun p => xEdge p.1 p.2.1 p.2.2))

/-- Second-coordinate edges. -/
def yEdges (n : Nat) : Finset (CubeVertex n × CubeVertex n) :=
  ((Finset.univ : Finset (Fin n × Fin (n - 1) × Fin n)).image
    (fun p => yEdge p.1 p.2.1 p.2.2))

/-- Third-coordinate edges. -/
def zEdges (n : Nat) : Finset (CubeVertex n × CubeVertex n) :=
  ((Finset.univ : Finset (Fin n × Fin n × Fin (n - 1))).image
    (fun p => zEdge p.1 p.2.1 p.2.2))

theorem xEdge_inj (n : Nat) :
    Function.Injective (fun p : Fin (n - 1) × Fin n × Fin n =>
      xEdge p.1 p.2.1 p.2.2) := by
  rintro ⟨i, y, z⟩ ⟨i', y', z'⟩ h
  simp only [xEdge, Prod.mk.injEq] at h
  obtain ⟨⟨hx, hy, hz⟩, _⟩ := h
  have hi : i = i' := by
    apply Fin.ext
    have := congrArg Fin.val hx
    simpa [cubeBase] using this
  subst hi; subst hy; subst hz; rfl

theorem yEdge_inj (n : Nat) :
    Function.Injective (fun p : Fin n × Fin (n - 1) × Fin n =>
      yEdge p.1 p.2.1 p.2.2) := by
  rintro ⟨x, i, z⟩ ⟨x', i', z'⟩ h
  simp only [yEdge, Prod.mk.injEq] at h
  obtain ⟨⟨hx, hy, hz⟩, _⟩ := h
  have hi : i = i' := by
    apply Fin.ext
    have := congrArg Fin.val hy
    simpa [cubeBase] using this
  subst hi; subst hx; subst hz; rfl

theorem zEdge_inj (n : Nat) :
    Function.Injective (fun p : Fin n × Fin n × Fin (n - 1) =>
      zEdge p.1 p.2.1 p.2.2) := by
  rintro ⟨x, y, i⟩ ⟨x', y', i'⟩ h
  simp only [zEdge, Prod.mk.injEq] at h
  obtain ⟨⟨hx, hy, hz⟩, _⟩ := h
  have hi : i = i' := by
    apply Fin.ext
    have := congrArg Fin.val hz
    simpa [cubeBase] using this
  subst hi; subst hx; subst hy; rfl

theorem xEdges_card (n : Nat) : (xEdges n).card = (n - 1) * n * n := by
  rw [xEdges, Finset.card_image_of_injective]
  · simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    ring
  · intro p q h; exact xEdge_inj n h

theorem yEdges_card (n : Nat) : (yEdges n).card = n * (n - 1) * n := by
  rw [yEdges, Finset.card_image_of_injective]
  · simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    ring
  · intro p q h; exact yEdge_inj n h

theorem zEdges_card (n : Nat) : (zEdges n).card = n * n * (n - 1) := by
  rw [zEdges, Finset.card_image_of_injective]
  · simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    ring
  · intro p q h; exact zEdge_inj n h

/-- A first-coordinate edge and a second-coordinate edge are never the same
ordered pair: the first differs in coordinate 1, the second in coordinate 2. -/
theorem xEdges_disjoint_yEdges (n : Nat) : Disjoint (xEdges n) (yEdges n) := by
  rw [Finset.disjoint_left]
  intro e he hf
  simp only [xEdges, yEdges, Finset.mem_image, Finset.mem_univ, true_and] at he hf
  obtain ⟨p, rfl⟩ := he
  obtain ⟨q, hq⟩ := hf
  have h1 := congrArg Prod.fst hq
  have h2 := congrArg Prod.snd hq
  simp only [xEdge, yEdge] at h1 h2
  have hx1 := congrArg (fun v : CubeVertex n => v.1.val) h1
  have hx2 := congrArg (fun v : CubeVertex n => v.1.val) h2
  simp [cubeBase, cubeSucc] at hx1 hx2
  omega

theorem xEdges_disjoint_zEdges (n : Nat) : Disjoint (xEdges n) (zEdges n) := by
  rw [Finset.disjoint_left]
  intro e he hf
  simp only [xEdges, zEdges, Finset.mem_image, Finset.mem_univ, true_and] at he hf
  obtain ⟨p, rfl⟩ := he
  obtain ⟨q, hq⟩ := hf
  have h1 := congrArg Prod.fst hq
  have h2 := congrArg Prod.snd hq
  simp only [xEdge, zEdge] at h1 h2
  have hx1 := congrArg (fun v : CubeVertex n => v.1.val) h1
  have hx2 := congrArg (fun v : CubeVertex n => v.1.val) h2
  simp [cubeBase, cubeSucc] at hx1 hx2
  omega

theorem yEdges_disjoint_zEdges (n : Nat) : Disjoint (yEdges n) (zEdges n) := by
  rw [Finset.disjoint_left]
  intro e he hf
  simp only [yEdges, zEdges, Finset.mem_image, Finset.mem_univ, true_and] at he hf
  obtain ⟨p, rfl⟩ := he
  obtain ⟨q, hq⟩ := hf
  have h1 := congrArg Prod.fst hq
  have h2 := congrArg Prod.snd hq
  simp only [yEdge, zEdge] at h1 h2
  have hy1 := congrArg (fun v : CubeVertex n => v.2.1.val) h1
  have hy2 := congrArg (fun v : CubeVertex n => v.2.1.val) h2
  simp [cubeBase, cubeSucc] at hy1 hy2
  omega

/-- All simple-cubic edges. -/
def cubeEdgeFinset (n : Nat) : Finset (CubeVertex n × CubeVertex n) :=
  xEdges n ∪ yEdges n ∪ zEdges n

theorem cubeEdgeFinset_card (n : Nat) :
    (cubeEdgeFinset n).card = 3 * ((n - 1) * n * n) := by
  rw [cubeEdgeFinset]
  rw [Finset.card_union_of_disjoint]
  · rw [Finset.card_union_of_disjoint]
    · rw [xEdges_card, yEdges_card, zEdges_card]
      ring
    · exact xEdges_disjoint_yEdges n
  · rw [Finset.disjoint_union_left]
    constructor
    · exact xEdges_disjoint_zEdges n
    · exact yEdges_disjoint_zEdges n

/-- The proved 3D link count: `E(n) = 3 n² (n − 1)`. -/
def cubeEdges (n : Nat) : Nat := 3 * n ^ 2 * (n - 1)

theorem cubeEdges_eq_card (n : Nat) : cubeEdges n = (cubeEdgeFinset n).card := by
  rw [cubeEdgeFinset_card, cubeEdges]
  ring

/-- Links per nucleon in the `n × n × n` packing: `E/A = 3 − 3/n`. -/
theorem cubeEdges_per_vertex (n : Nat) (hn : 0 < n) :
    (cubeEdges n : ℝ) / (n ^ 3 : ℝ) = 3 - 3 / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hn1 : 1 ≤ n := hn
  rw [cubeEdges]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hn1]
  field_simp [hn']
  ring

/-- More volume, more links per nucleon: the surface fraction falls. -/
theorem cubeEdges_per_vertex_mono {m n : Nat} (hm : 0 < m) (hmn : m ≤ n) :
    (cubeEdges m : ℝ) / (m ^ 3 : ℝ) ≤ (cubeEdges n : ℝ) / (n ^ 3 : ℝ) := by
  rw [cubeEdges_per_vertex m hm, cubeEdges_per_vertex n (lt_of_lt_of_le hm hmn)]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hm hmn)
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hdiv : 3 / (n : ℝ) ≤ 3 / (m : ℝ) := by
    exact div_le_div_of_nonneg_left (by norm_num) hm' hmn'
  linarith

/-- The continuous surface/volume link count used by the mass ledger:
`L(A) = 3A − 3A^(2/3)`. -/
def packingLinks (a : Nat) : ℝ :=
  3 * (a : ℝ) - 3 * ((a : ℝ) ^ ((2 : ℝ) / 3))

/-- At a cubic size `n³`, the continuous count is exactly `cubeEdges`. -/
theorem packingLinks_cube (n : Nat) (hn : 0 < n) :
    packingLinks (n ^ 3) = (cubeEdges n : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [packingLinks, cubeEdges]
  have hpow : ((n ^ 3 : Nat) : ℝ) ^ ((2 : ℝ) / 3) = (n : ℝ) ^ 2 := by
    rw [Nat.cast_pow]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt hn')]
    norm_num
  rw [hpow]
  have hn1 : 1 ≤ n := hn
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hn1]
  push_cast
  ring


/-! ## Typed channels

A `p/n` labelling splits the cubic edges into `pp`, `pn`, and `nn`.  The
partition is exact for every labelling; the mean-field counts below are the
expected counts for a uniformly mixed labelling with `Z` protons and `N`
neutrons.
-/

/-- Proton–proton edges. -/
def ppEdges (n : Nat) (label : CubeVertex n → Bool) :
    Finset (CubeVertex n × CubeVertex n) :=
  (cubeEdgeFinset n).filter (fun e => label e.1 = true ∧ label e.2 = true)

/-- Proton–neutron edges. -/
def pnEdges (n : Nat) (label : CubeVertex n → Bool) :
    Finset (CubeVertex n × CubeVertex n) :=
  (cubeEdgeFinset n).filter (fun e => label e.1 ≠ label e.2)

/-- Neutron–neutron edges. -/
def nnEdges (n : Nat) (label : CubeVertex n → Bool) :
    Finset (CubeVertex n × CubeVertex n) :=
  (cubeEdgeFinset n).filter (fun e => label e.1 = false ∧ label e.2 = false)

/-- **Channel partition.** Every cubic edge is exactly one of `pp`, `pn`, `nn`. -/
theorem cubeEdges_channel_partition (n : Nat) (label : CubeVertex n → Bool) :
    ppEdges n label ∪ pnEdges n label ∪ nnEdges n label = cubeEdgeFinset n := by
  ext e
  simp only [Finset.mem_union, Finset.mem_filter, ppEdges, pnEdges, nnEdges]
  by_cases h1 : label e.1 = true <;> by_cases h2 : label e.2 = true <;>
    simp [h1, h2]

theorem ppEdges_disjoint_pnEdges (n : Nat) (label : CubeVertex n → Bool) :
    Disjoint (ppEdges n label) (pnEdges n label) := by
  rw [Finset.disjoint_left]
  intro e he hf
  simp only [ppEdges, pnEdges, Finset.mem_filter] at he hf
  exact hf.2 (by rw [he.2.1, he.2.2])

theorem ppEdges_disjoint_nnEdges (n : Nat) (label : CubeVertex n → Bool) :
    Disjoint (ppEdges n label) (nnEdges n label) := by
  rw [Finset.disjoint_left]
  intro e he hf
  simp only [ppEdges, nnEdges, Finset.mem_filter] at he hf
  rw [he.2.1] at hf
  exact Bool.noConfusion hf.2.1

theorem pnEdges_disjoint_nnEdges (n : Nat) (label : CubeVertex n → Bool) :
    Disjoint (pnEdges n label) (nnEdges n label) := by
  rw [Finset.disjoint_left]
  intro e he hf
  simp only [pnEdges, nnEdges, Finset.mem_filter] at he hf
  exact he.2 (by rw [hf.2.1, hf.2.2])

/-- Mean-field `pp` count for `Z` protons out of `A = Z+N` labelled sites. -/
def mixedPP (e : ℝ) (z n : Nat) : ℝ :=
  e * (z : ℝ) * ((z : ℝ) - 1) /
    (((z : ℝ) + (n : ℝ)) * (((z : ℝ) + (n : ℝ)) - 1))

/-- Mean-field `pn` count. -/
def mixedPN (e : ℝ) (z n : Nat) : ℝ :=
  e * (2 * (z : ℝ) * (n : ℝ)) /
    (((z : ℝ) + (n : ℝ)) * (((z : ℝ) + (n : ℝ)) - 1))

/-- Mean-field `nn` count. -/
def mixedNN (e : ℝ) (z n : Nat) : ℝ :=
  e * (n : ℝ) * ((n : ℝ) - 1) /
    (((z : ℝ) + (n : ℝ)) * (((z : ℝ) + (n : ℝ)) - 1))

theorem mixedChannelCounts_sum (e : ℝ) (z n : Nat) (h : 1 < z + n) :
    mixedPP e z n + mixedPN e z n + mixedNN e z n = e := by
  have hA : (1 : ℝ) < (z : ℝ) + (n : ℝ) := by exact_mod_cast h
  have hA0 : ((z : ℝ) + (n : ℝ)) ≠ 0 := by positivity
  have hA1 : ((z : ℝ) + (n : ℝ)) - 1 ≠ 0 := by linarith
  unfold mixedPP mixedPN mixedNN
  field_simp [hA0, hA1]
  ring

theorem mixedChannelCounts_asymmetry (e : ℝ) (z n : Nat) (h : 1 < z + n) :
    mixedNN e z n - mixedPP e z n =
      e * ((n : ℝ) - (z : ℝ)) / ((z : ℝ) + (n : ℝ)) := by
  have hA : (1 : ℝ) < (z : ℝ) + (n : ℝ) := by exact_mod_cast h
  have hA0 : ((z : ℝ) + (n : ℝ)) ≠ 0 := by positivity
  have hA1 : ((z : ℝ) + (n : ℝ)) - 1 ≠ 0 := by linarith
  unfold mixedNN mixedPP
  field_simp [hA0, hA1]
  ring


/-- **Cardinality form of the channel partition**: the three channel counts sum
to the total cubic edge count. -/
theorem cubeEdges_channel_card_sum (n : Nat) (label : CubeVertex n → Bool) :
    (ppEdges n label).card + (pnEdges n label).card + (nnEdges n label).card =
      cubeEdges n := by
  have hpart := cubeEdges_channel_partition n label
  have h1 : Disjoint (ppEdges n label ∪ pnEdges n label) (nnEdges n label) := by
    rw [Finset.disjoint_union_left]
    exact ⟨ppEdges_disjoint_nnEdges n label, pnEdges_disjoint_nnEdges n label⟩
  have hcard := congrArg Finset.card hpart
  rw [Finset.card_union_of_disjoint h1,
      Finset.card_union_of_disjoint (ppEdges_disjoint_pnEdges n label)] at hcard
  rw [cubeEdges_eq_card]
  exact hcard


/-- Continuous cycle rank of a 3D packing: `R(A) = 2A − 3A^(2/3) + 1`. -/
noncomputable def packingClosureRank (a : Nat) : ℝ :=
  2 * (a : ℝ) - 3 * ((a : ℝ) ^ ((2 : ℝ) / 3)) + 1

/-- At a cubic size, the continuous closure rank is `2n³ − 3n² + 1`. -/
theorem packingClosureRank_cube (n : Nat) (hn : 0 < n) :
    packingClosureRank (n ^ 3) = 2 * (n : ℝ) ^ 3 - 3 * (n : ℝ) ^ 2 + 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold packingClosureRank
  have hpow : ((n ^ 3 : Nat) : ℝ) ^ ((2 : ℝ) / 3) = (n : ℝ) ^ 2 := by
    rw [Nat.cast_pow]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt hn')]
    norm_num
  rw [hpow]
  push_cast
  ring


theorem cubeEdges_pos {n : Nat} (hn : 1 < n) : 0 < cubeEdges n := by
  unfold cubeEdges
  have hn0 : 0 < n := lt_trans Nat.zero_lt_one hn
  have h2 : 0 < n - 1 := Nat.sub_pos_of_lt hn
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) (pow_pos hn0 2)) h2

theorem cubeEdges_per_vertex_le_three (n : Nat) (hn : 0 < n) :
    (cubeEdges n : ℝ) / (n ^ 3 : ℝ) ≤ 3 := by
  rw [cubeEdges_per_vertex n hn]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h : 0 ≤ 3 / (n : ℝ) := div_nonneg (by norm_num) (le_of_lt hn')
  linarith

theorem cubeEdges_per_vertex_ge_three_halves (n : Nat) (hn : 2 ≤ n) :
    3 / 2 ≤ (cubeEdges n : ℝ) / (n ^ 3 : ℝ) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  rw [cubeEdges_per_vertex n hn0]
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h : 3 / (n : ℝ) ≤ 3 / 2 := by
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn' 
  linarith

theorem packingLinks_le_three_mul (a : Nat) :
    packingLinks a ≤ 3 * (a : ℝ) := by
  unfold packingLinks
  have h : 0 ≤ 3 * ((a : ℝ) ^ ((2 : ℝ) / 3)) := by positivity
  linarith


theorem cubeEdges_three : cubeEdges 3 = 54 := by
  decide

end PMAtoms
