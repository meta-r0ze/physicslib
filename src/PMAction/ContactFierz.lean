import PMAction.ContactRunning

/-!
# The tensor identities behind the contact's running (`16` and `4`)

`ContactRunning` uses two Dirac identities for `Γ = γ^μ P_L` contracted over `μ`:

* same orientation: `Σ γ^ργ^σγ^μP_L ⊗ γ_ργ_σγ_μP_L = 16 Σ γ^μP_L ⊗ γ_μP_L`;
* opposite orientation: `Σ γ^ργ^σγ^μP_L ⊗ γ_μγ_σγ_ρP_L = 4 Σ γ^μP_L ⊗ γ_μP_L`.

In Paper II's representation `γ⁵ = Γ = diag(1,1,−1,−1)` is diagonal, so each `γ^μ` is
off-diagonal in 2×2 blocks: `γ^μ = [[0, s^μ], [s̄^μ, 0]]` (`s_block`, `sb_block`). Then
`γ^ργ^σγ^μ(1−γ⁵)` is `2 s^ρ s̄^σ s^μ` in the upper-right block and zero elsewhere
(`triple_blk`), and both identities reduce to 2×2 Kronecker statements.

* `same_eq`: the same-orientation sum is `F F̄ F`, with `F = Σ η_μ s^μ ⊗ s^μ` and
  `F̄ = Σ η_μ s̄^μ ⊗ s̄^μ` (mixed product).
* `F_apply`, `Fbar_apply`: `F = F̄ = 2 ε ⊗ ε` (Fierz: the contracted `s ⊗ s` is the
  antisymmetric pairing).
* `same_identity`: `F F̄ F = 16 F`.
* `opp_eq`: the opposite-orientation sum is the partial transpose `T2` of `G Ḡ G`, with
  `G = Σ η_μ s^μ ⊗ (s^μ)ᵀ`; `T2_G`: `T2 G = F`.
* `G_apply`, `Gbar_apply`: `G = Ḡ = 2(δ_ac δ_bd − δ_ab δ_cd)`.
* `opp_identity`: the opposite-orientation sum is `4 F`.
-/

noncomputable section
namespace PMAction.ContactFierz
open Matrix VATrace ConcreteFermion
open scoped Kronecker

abbrev W2 := Matrix (Fin 2) (Fin 2) ℂ
abbrev W4 := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- Upper-right blocks of `γ^μ`. -/
def s : Fin 4 → W2 := ![
  !![1, 0; 0, 1],
  !![0, -1; -1, 0],
  !![0, Complex.I; -Complex.I, 0],
  !![-1, 0; 0, 1]]

/-- Lower-left blocks of `γ^μ`. -/
def sb : Fin 4 → W2 := ![
  !![1, 0; 0, 1],
  !![0, 1; 1, 0],
  !![0, -Complex.I; Complex.I, 0],
  !![1, 0; 0, -1]]

theorem s_block (μ : Fin 4) (i j : Fin 2) :
    g μ (Fin.castAdd 2 i) (Fin.natAdd 2 j) = s μ i j := by
  fin_cases μ <;> fin_cases i <;> fin_cases j <;>
    rfl

theorem sb_block (μ : Fin 4) (i j : Fin 2) :
    g μ (Fin.natAdd 2 i) (Fin.castAdd 2 j) = sb μ i j := by
  fin_cases μ <;> fin_cases i <;> fin_cases j <;>
    rfl

/-! ## The block reduction -/

/-- Fin 4 as two 2-dim blocks: `0, 1` (chirality `+1`) and `2, 3` (chirality `−1`). -/
def e4 : Fin 2 ⊕ Fin 2 ≃ Fin 4 := finSumFinEquiv

/-- A 4×4 matrix in 2+2 block form. -/
def blk (M : Spin) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ := M.submatrix e4 e4

theorem blk_mul (A B : Spin) : blk (A * B) = blk A * blk B :=
  (Matrix.submatrix_mul_equiv A B e4 e4 e4).symm

theorem g_e_ll (μ : Fin 4) (i j : Fin 2) :
    g μ (e4 (Sum.inl i)) (e4 (Sum.inl j)) = 0 := by
  fin_cases μ <;> fin_cases i <;> fin_cases j <;> rfl

theorem g_e_lr (μ : Fin 4) (i j : Fin 2) :
    g μ (e4 (Sum.inl i)) (e4 (Sum.inr j)) = s μ i j := by
  fin_cases μ <;> fin_cases i <;> fin_cases j <;> rfl

theorem g_e_rl (μ : Fin 4) (i j : Fin 2) :
    g μ (e4 (Sum.inr i)) (e4 (Sum.inl j)) = sb μ i j := by
  fin_cases μ <;> fin_cases i <;> fin_cases j <;> rfl

theorem g_e_rr (μ : Fin 4) (i j : Fin 2) :
    g μ (e4 (Sum.inr i)) (e4 (Sum.inr j)) = 0 := by
  fin_cases μ <;> fin_cases i <;> fin_cases j <;> rfl

/-- Each `γ^μ` is block off-diagonal: `[[0, s^μ], [s̄^μ, 0]]`. -/
theorem g_blk (μ : Fin 4) : blk (g μ) = fromBlocks 0 (s μ) (sb μ) 0 := by
  ext (i | i) (j | j) <;> simp [blk, g_e_ll, g_e_lr, g_e_rl, g_e_rr]

theorem L_e_ll (i j : Fin 2) :
    L (e4 (Sum.inl i)) (e4 (Sum.inl j)) = 0 := by
  fin_cases i <;> fin_cases j <;> rfl

theorem L_e_lr (i j : Fin 2) :
    L (e4 (Sum.inl i)) (e4 (Sum.inr j)) = 0 := by
  fin_cases i <;> fin_cases j <;> rfl

theorem L_e_rl (i j : Fin 2) :
    L (e4 (Sum.inr i)) (e4 (Sum.inl j)) = 0 := by
  fin_cases i <;> fin_cases j <;> rfl

theorem L_e_rr (i j : Fin 2) :
    L (e4 (Sum.inr i)) (e4 (Sum.inr j)) = if i = j then 2 else 0 := by
  fin_cases i <;> fin_cases j <;> rfl

/-- `1 − γ⁵` (`VATrace.L_eq`) is `2` on the chirality `−1` block and zero elsewhere. -/
theorem L_blk : blk L = fromBlocks 0 0 0 (Matrix.diagonal fun _ => (2 : ℂ)) := by
  ext (i | i) (j | j) <;>
    simp [blk, L_e_ll, L_e_lr, L_e_rl, L_e_rr, Matrix.diagonal_apply]

/-- **The block reduction.** `γ^ργ^σγ^μ(1 − γ⁵)` has only its upper-right block, which is
`s^ρ s̄^σ s^μ · 2`. So every contraction of two such factors is a contraction of the 2×2 blocks
`s^ρ s̄^σ s^μ`, which is what `same_identity'` and `opp_identity` compute. -/
theorem triple_blk (ρ σ μ : Fin 4) :
    blk (g ρ * g σ * g μ * L) =
      fromBlocks 0 (s ρ * sb σ * s μ * Matrix.diagonal fun _ => (2 : ℂ)) 0 0 := by
  rw [blk_mul, blk_mul, blk_mul, g_blk, g_blk, g_blk, L_blk]
  simp [fromBlocks_multiply]

def F : W4 := ∑ μ, η μ • (s μ ⊗ₖ s μ)
def Fbar : W4 := ∑ μ, η μ • (sb μ ⊗ₖ sb μ)
def G : W4 := ∑ μ, η μ • (s μ ⊗ₖ (s μ)ᵀ)
def Gbar : W4 := ∑ μ, η μ • (sb μ ⊗ₖ (sb μ)ᵀ)

/-- The antisymmetric symbol on two indices. -/
def eps : Fin 2 → Fin 2 → ℂ := ![![0, 1], ![-1, 0]]

/-- Kronecker delta. -/
def kd (i j : Fin 2) : ℂ := if i = j then 1 else 0

set_option maxHeartbeats 2000000 in
theorem F_apply (a b c d : Fin 2) : F (a, b) (c, d) = 2 * eps a b * eps c d := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [F, s, η, eps, Fin.sum_univ_four, Matrix.sum_apply] <;> norm_num

set_option maxHeartbeats 2000000 in
theorem Fbar_apply (a b c d : Fin 2) : Fbar (a, b) (c, d) = 2 * eps a b * eps c d := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [Fbar, sb, η, eps, Fin.sum_univ_four, Matrix.sum_apply] <;> norm_num

set_option maxHeartbeats 2000000 in
theorem G_apply (a b c d : Fin 2) :
    G (a, b) (c, d) = 2 * (kd a c * kd b d - kd a b * kd c d) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [G, s, η, kd, Fin.sum_univ_four, transpose_apply,
      Matrix.sum_apply] <;> norm_num

set_option maxHeartbeats 2000000 in
theorem Gbar_apply (a b c d : Fin 2) :
    Gbar (a, b) (c, d) = 2 * (kd a c * kd b d - kd a b * kd c d) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [Gbar, sb, η, kd, Fin.sum_univ_four, transpose_apply,
      Matrix.sum_apply] <;> norm_num

/-- **Same orientation, as a product.** -/
theorem triple_sum (X Y Z : Fin 4 → W4) :
    (∑ ρ, X ρ) * (∑ σ, Y σ) * (∑ μ, Z μ) = ∑ ρ, ∑ σ, ∑ μ, X ρ * Y σ * Z μ := by
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]

theorem same_eq :
    (∑ ρ, ∑ σ, ∑ μ, (η ρ * η σ * η μ) •
        ((s ρ * sb σ * s μ) ⊗ₖ (s ρ * sb σ * s μ))) = F * Fbar * F := by
  unfold F Fbar
  rw [triple_sum]
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun σ _ =>
    Finset.sum_congr rfl fun μ _ => ?_
  simp only [smul_mul_smul_comm, ← mul_kronecker_mul]

set_option maxHeartbeats 2000000 in
theorem same_identity : F * Fbar * F = (16 : ℂ) • F := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [Matrix.mul_apply, Matrix.smul_apply, F_apply, Fbar_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, smul_eq_mul]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp [eps] <;> norm_num

/-- Partial transpose on the second factor: `T2 M (a,b) (c,d) = M (a,d) (c,b)`. -/
def T2 (M : W4) : W4 := Matrix.of fun x y => M (x.1, y.2) (y.1, x.2)

theorem T2_kron (A B : W2) : T2 (A ⊗ₖ B) = A ⊗ₖ Bᵀ := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [T2, transpose_apply]

theorem T2_smul (c : ℂ) (M : W4) : T2 (c • M) = c • T2 M := by
  ext ⟨a, b⟩ ⟨c', d⟩
  simp [T2]

theorem T2_sum {ι : Type*} (t : Finset ι) (f : ι → W4) :
    T2 (∑ i ∈ t, f i) = ∑ i ∈ t, T2 (f i) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [T2, Matrix.sum_apply]

theorem T2_G : T2 G = F := by
  unfold G F
  simp only [T2_sum, T2_smul, T2_kron, transpose_transpose]

/-- **Opposite orientation, as a partial transpose.** -/
theorem opp_eq :
    (∑ ρ, ∑ σ, ∑ μ, (η ρ * η σ * η μ) •
        ((s ρ * sb σ * s μ) ⊗ₖ (s μ * sb σ * s ρ))) = T2 (G * Gbar * G) := by
  unfold G Gbar
  rw [triple_sum, T2_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [T2_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [T2_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [smul_mul_smul_comm, ← mul_kronecker_mul, T2_smul, T2_kron, ← transpose_mul,
    transpose_transpose, Matrix.mul_assoc]

set_option maxHeartbeats 2000000 in
theorem GGG : G * Gbar * G = (4 : ℂ) • G := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [Matrix.mul_apply, Matrix.smul_apply, G_apply, Gbar_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, smul_eq_mul]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp [kd] <;> norm_num

/-- **The same-orientation identity:** `16`. -/
theorem same_identity' :
    (∑ ρ, ∑ σ, ∑ μ, (η ρ * η σ * η μ) •
        ((s ρ * sb σ * s μ) ⊗ₖ (s ρ * sb σ * s μ))) = (16 : ℂ) • F := by
  rw [same_eq, same_identity]

/-- **The opposite-orientation identity:** `4`. -/
theorem opp_identity :
    (∑ ρ, ∑ σ, ∑ μ, (η ρ * η σ * η μ) •
        ((s ρ * sb σ * s μ) ⊗ₖ (s μ * sb σ * s ρ))) = (4 : ℂ) • F := by
  rw [opp_eq, GGG, T2_smul, T2_G]

end PMAction.ContactFierz
