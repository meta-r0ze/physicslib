import PMFlavor.MixingMatrix
import PMFlavor.KronSeries

/-!
# The eigenvector link and the admittance network are two reductions of one incidence graph

Two pictures of flavour coexist. (A) `SubstrateLink`, `BreakingLink`, `MixingMatrix`: mixing as the
eigenvectors of the link `Y`. (B) `KronSeries`, `VubSeriesPath`: mixing magnitudes as admittances
of a conserving network. This module compares them on the object they share.

**The shared object.** A generation is a pair of glue classes (`GenerationLink.pair_of_missing`),
so there is a bipartite incidence graph: three generation vertices, three class vertices, and a
leg from a generation to each of its two classes. Every class vertex has exactly two legs, the two
generations that contain it (`ExchangeAxis.one_pair_through`).

* `linkOverlap_eq_gram`: picture A's link is the Gram matrix `B Bᵀ` of the incidence `B`. Each
  entry is a sum over classes of a product of two legs with unit denominator.
* `kron_schur`: with leg conductances `a, b, c` for the three classes, eliminating the class
  vertices from the conserving (Laplacian) network is the Schur complement, and gives `kronLink`:
  the pair that shares a class of leg `g` is coupled by `g/2`, two legs in series
  (`pair_is_two_leg_series`). `kronLink_row_sum`: the reduced link still conserves.
* `symmetric_point`: at unit legs the two reductions are affinely related, `1 + J = 4 − 2 L`, so
  they have the same eigenvectors. This is the only point where they agree.

**Where they part.**
* `diagonal_breaking_not_network`: picture A breaks the symmetry on the diagonal alone
  (`brokenLink δ`), leaving every off-diagonal entry `1`. No choice of legs, scale or offset makes
  an affine image of `kronLink` match it unless `δ = 0`: in a network a leg change moves a
  diagonal entry and an off-diagonal entry together. So Kron-reducing the existing broken link does
  not reproduce picture B, for any `δ`.
* `two_leg_from_incidence`: picture B's `2` in `|V_ub| = 1/(2α⁻¹ + π)` is the degree of a class
  vertex. `shared_node_three_legs`: a single reference node joined to all three generations would
  give `g/3`, i.e. `1/(3 α⁻¹)`, which `MixingTests.vub_count_unique` excludes. So the node
  crossings are per class, not one shared vertex.
* The Gram entry for the same class is the leg product `g²` with unit denominator, the reading
  `KronSeries.product_reading_wrong` already excludes for `|V_ub|`.

**What picture A fixes by itself.** `brokenLinkB_antiB`: `(1, 0, −1)` is an eigenvector of the
second-sector link for every `ε`, as `(0, 1, −1)` is of the first for every `δ`. So
`protected_overlap_quarter`: one entry of the mixing matrix has squared modulus exactly `1/4`,
whatever `δ` and `ε` are. `protected_overlap_phase_blind`: the same holds when the two sectors are
rephased on their distinguished generations, so a phase on the link legs does not move it.

Data. No CKM entry is near `1/4` (PDG: off-diagonal `|V|² ≤ 0.051`, diagonal `|V|² ≥ 0.947`), so
picture A is not the quark mixing for any `δ, ε`; the quark mixings are picture B's. For the
leptons `|U| = 1/2` lies inside the NuFIT 6.0 `3σ` ranges of `|U_μ1|`, `|U_μ2|`, `|U_τ1|`,
`|U_τ2|` only (arXiv:2410.05380), so picture A survives there as a candidate with a test; the
resulting `θ₂₃` branches are listed in `REVIEW-AND-NEXT.md` (computed numerically, not in Lean).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
namespace PMFlavor.LinkKronComparison
open Matrix GenerationLink GenerationBreaking SubstrateLink BreakingLink MixingMatrix

/-! ## Picture A's link is the Gram matrix of the incidence -/

/-- Generation–class incidence: generation `i` contains every class except `i`. -/
def incidence : Matrix (Fin 3) (Fin 3) ℂ := of fun i c => if c = i then 0 else 1

theorem incidence_mem (i c : Fin 3) :
    incidence i c = if c ∈ pair_of_missing i then 1 else 0 := by
  by_cases h : c = i <;> simp [incidence, pair_of_missing, h]

/-- **The substrate link is `B Bᵀ`**: a sum over shared classes of a product of two legs. -/
theorem linkOverlap_eq_gram : linkOverlap = incidence * incidenceᵀ := by
  ext i j
  rw [linkOverlap_eq_form i j]
  fin_cases i <;> fin_cases j <;>
    simp [incidence, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

/-! ## The conserving network on the same incidence, and its Kron reduction -/

/-- Generation block of the incidence Laplacian: each generation carries its two legs. Classes
`0, 1, 2` have leg conductances `a, b, c`. -/
def Lgg (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![b + c, 0, 0; 0, a + c, 0; 0, 0, a + b]

/-- Generation–class block: minus the leg conductance where the generation contains the class. -/
def Lgc (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![0, -b, -c; -a, 0, -c; -a, -b, 0]

/-- Class block: each class vertex carries its two equal legs. -/
def Lcc (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![2 * a, 0, 0; 0, 2 * b, 0; 0, 0, 2 * c]

def LccInv (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 / (2 * a), 0, 0; 0, 1 / (2 * b), 0; 0, 0, 1 / (2 * c)]

theorem Lcc_mul_inv (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    Lcc a b c * LccInv a b c = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Lcc, LccInv, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp

/-- The Kron-reduced link: the pair of generations sharing a class of leg `g` is joined by `g/2`. -/
def kronLink (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(b + c) / 2, -(c / 2), -(b / 2);
     -(c / 2), (a + c) / 2, -(a / 2);
     -(b / 2), -(a / 2), (a + b) / 2]

theorem kron_00 (a b c : ℝ) : kronLink a b c 0 0 = (b + c) / 2 := by simp [kronLink]
theorem kron_11 (a b c : ℝ) : kronLink a b c 1 1 = (a + c) / 2 := by simp [kronLink]
theorem kron_02 (a b c : ℝ) : kronLink a b c 0 2 = -(b / 2) := by simp [kronLink]
theorem kron_12 (a b c : ℝ) : kronLink a b c 1 2 = -(a / 2) := by simp [kronLink]

/-- Class–generation block, the transpose of `Lgc`. -/
def Lcg (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![0, -a, -a; -b, 0, -b; -c, -c, 0]

theorem Lcg_eq_transpose (a b c : ℝ) : Lcg a b c = (Lgc a b c)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- `Lgc · Lcc⁻¹`: each leg divided by its class vertex's own conductance is `1/2`. -/
def halfIncidence : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -(1 / 2), -(1 / 2); -(1 / 2), 0, -(1 / 2); -(1 / 2), -(1 / 2), 0]

theorem Lgc_mul_inv (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    Lgc a b c * LccInv a b c = halfIncidence := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Lgc, LccInv, halfIncidence, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp

theorem half_schur (a b c : ℝ) : Lgg a b c - halfIncidence * Lcg a b c = kronLink a b c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Lgg, Lcg, halfIncidence, kronLink, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- **Eliminating the class vertices is the Schur complement, and gives `kronLink`.** -/
theorem kron_schur (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    Lgg a b c - Lgc a b c * LccInv a b c * (Lgc a b c)ᵀ = kronLink a b c := by
  rw [Lgc_mul_inv a b c ha hb hc, ← Lcg_eq_transpose, half_schur]

/-- The reduced link conserves: every row sums to zero. -/
theorem kronLink_row_sum (a b c : ℝ) (i : Fin 3) : ∑ j, kronLink a b c i j = 0 := by
  fin_cases i <;> simp [kronLink, Fin.sum_univ_three] <;> ring

/-- The coupling of the pair sharing class `0` is the series admittance of its two legs
(`KronSeries.kron_two` with `g₁ = g₂ = a`). -/
theorem pair_is_two_leg_series (a b c : ℝ) (ha : 0 < a) :
    kronLink a b c 1 2 = (-a) * (-a) / (0 - (a + a)) := by
  rw [kron_12, eq_div_iff (by intro h; linarith)]
  ring

/-- **The `2` of `1/(2Z)` is the degree of a class vertex.** With leg impedance `Z`, the reduced
coupling through a class is `1/(2Z)`; `VubSeriesPath` adds the unit boundary `π` in series. -/
theorem two_leg_from_incidence (Z b c : ℝ) : -(kronLink (1 / Z) b c 1 2) = 1 / (2 * Z) := by
  rw [kron_12, neg_neg, div_div, mul_comm]

/-- A single node joined to all three generations by equal legs gives `g/3` per pair, not `g/2`. -/
theorem shared_node_three_legs (g : ℝ) (hg : 0 < g) :
    (-g) * (-g) / (0 - (g + g + g)) = -(g / 3) := by
  rw [div_eq_iff (by intro h; linarith)]
  ring

/-! ## Agreement at the symmetric point only -/

/-- **At unit legs the two reductions are affinely related**: `1 + J = 4·1 − 2·L`. The right side
is `SubstrateLink.linkOverlap_as_of`'s form, so the symmetric link and the reduced Laplacian share
eigenvectors. -/
theorem symmetric_point :
    (4 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - (2 : ℝ) • kronLink 1 1 1 =
      of fun i j : Fin 3 => if i = j then (2 : ℝ) else 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kronLink] <;> norm_num

/-- **A diagonal breaking is not a network change.** If an affine image `p·1 − q·L` of the reduced
link matches `brokenLink δ` on the entries `(0,0)`, `(1,1)`, `(0,2)`, `(1,2)` (values `2 + δ`, `2`,
`1`, `1`), then `δ = 0`, whatever the legs `a, b, c` are. -/
theorem diagonal_breaking_not_network (p q a b c δ : ℝ)
    (h00 : p - q * kronLink a b c 0 0 = 2 + δ) (h11 : p - q * kronLink a b c 1 1 = 2)
    (h02 : -(q * kronLink a b c 0 2) = 1) (h12 : -(q * kronLink a b c 1 2) = 1) : δ = 0 := by
  rw [kron_00] at h00
  rw [kron_11] at h11
  rw [kron_02] at h02
  rw [kron_12] at h12
  linear_combination -h00 + h11 + h12 - h02

/-! ## What picture A fixes by itself: one entry of modulus `1/2` -/

/-- `(1, 0, −1)` is an eigenvector of the second-sector link at eigenvalue `1` for **every** `ε`
(`MixingMatrix.brokenLinkB_eigAnti` is the case `ε = 0`). -/
theorem brokenLinkB_antiB (ε : ℝ) : brokenLinkB ε *ᵥ antiB = (1 : ℂ) • antiB := by
  ext i; fin_cases i <;>
    simp [brokenLinkB, antiB, mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply,
      smul_eq_mul] <;> norm_num

theorem ip_anti_anti : ip anti anti = 2 := by
  simp [ip, anti, Fin.sum_univ_three] <;> norm_num

theorem ip_antiB_antiB : ip antiB antiB = 2 := by
  simp [ip, antiB, Fin.sum_univ_three] <;> norm_num

/-- **One mixing entry is exactly `1/4` in squared modulus**, independent of `δ` and `ε`: the two
protected states are fixed vectors, eigenvectors of their links for all values of the breaking
(`BreakingLink.brokenLink_antisym`, `brokenLinkB_antiB`). -/
theorem protected_overlap_quarter :
    (ip anti antiB) ^ 2 / (ip anti anti * ip antiB antiB) = 1 / 4 := by
  rw [ip_anti_antiB, ip_anti_anti, ip_antiB_antiB]
  norm_num

/-- Both protected states, with the fixed overlap, for all `δ, ε`. -/
theorem rigid_entry (δ ε : ℝ) :
    brokenLink δ *ᵥ anti = (1 : ℂ) • anti ∧ brokenLinkB ε *ᵥ antiB = (1 : ℂ) • antiB ∧
      (ip anti antiB) ^ 2 / (ip anti anti * ip antiB antiB) = 1 / 4 :=
  ⟨brokenLink_antisym δ, brokenLinkB_antiB ε, protected_overlap_quarter⟩

/-- **A phase on the link legs does not move it.** Rephasing the first sector on generation `0`
and the second on generation `1` (the generations their breakings distinguish) leaves both
protected states fixed: each has a zero in the rephased slot. So Hermitian links
`D_A (brokenLink δ) D_A⁻¹`, `D_B (brokenLinkB ε) D_B⁻¹` keep the `1/4` entry while their relative
phases enter the rest of the mixing matrix. -/
theorem protected_overlap_phase_blind (u v : ℂ) :
    (Matrix.diagonal ![u, 1, 1] : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ anti = anti ∧
      (Matrix.diagonal ![1, v, 1] : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ antiB = antiB := by
  constructor <;> ext i <;> fin_cases i <;>
    simp [anti, antiB, mulVec, dotProduct, Matrix.diagonal]

end PMFlavor.LinkKronComparison
