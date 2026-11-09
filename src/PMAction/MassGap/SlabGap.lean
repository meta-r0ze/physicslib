import PMAction.MassGap.SlabObservables
import PMAction.MassGap.SpectralBounds
import PMAction.MassGap.Walsh
import PMAction.MassGap.GapFromCorrelation

/-!
# The slab transfer matrix has a gap in the flip-even sector

Assembly of the Yang–Mills-gap chain for discrete distinctions on a slab `G □ [0, L]`.

`T` is the PM transfer matrix of `TransferSlab` and `S = T²` (so the spectrum is nonnegative).
`v₀` is the free end. In the low-cost regime `Regime` (the same numerical conditions as
`slab_clustering`, with the plaquette degree bounded uniformly in `L`):

* `Z_bounds`: there are `Λ > 0`, `κ > 0`, `K` with `κ Λᴸ ≤ ⟨v₀, Sᴸ v₀⟩ ≤ K Λᴸ`
  (`SpectralBounds.visible_top`).
* `trunc_bound`: for every flip-even `ψ`, the truncated correlation
  `⟨ψ,Sᴸψ⟩⟨v₀,Sᴸv₀⟩ - ⟨ψ,Sᴸv₀⟩²` is at most `C (μ²)ᴸ ⟨v₀,Sᴸv₀⟩²`. This uses the Walsh
  expansion of `ψ / v₀` in even characters and `transfer_clustering` for each pair.
* `slab_gap`: every flip-even eigenvalue `λ` of `S` satisfies **either `λ ≤ μ² Λ`, or `λ = Λ`
  with an eigenvector that overlaps `v₀`**. The even `Λ`-eigenspace is one-dimensional
  (`top_simple`).

Since `μ < 1` is fixed by `q` and the degree bound `D` alone, the relative gap `1 - μ²` holds
uniformly in the spatial volume `V` and in the slab length.

Scope: discrete (`ℤ/2`) distinctions only. `PeierlsDichotomy` shows the continuous `U(1)`
case has no Peierls condition. The odd sector, the tunnelling between the two vacua, is
not claimed.
-/

namespace PMAction.MassGap.SlabGap
open Finset Matrix SimpleGraph ContourRepresentation SlabGeometry ParitySigns TransferSlab
  SlabObservables SpectralBounds ContourGas
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (plaqG : Finset (Finset (Sym2 V)))

/-- The low-cost regime (geometry and the numerical conditions of `slab_clustering`). -/
structure Regime (q μ : ℝ) (D : ℕ) : Prop where
  connG : G.Connected
  plaqE : ∀ P ∈ plaqG, P ⊆ G.edgeFinset
  plaqP : ∀ P ∈ plaqG, IsPlaquette G P
  genG : PlaquettesGenerate G plaqG
  degree : ∀ (L : ℕ) e, (plaqGraph (slabPlaq G L plaqG)).degree e ≤ D
  q_pos : 0 < q
  μ_pos : 0 < μ
  μ_lt : μ < 1
  y1 : 2 * q ≤ 1 / 2
  Dy : (D : ℝ) ^ 2 * (2 * q) < 1
  s1 : 2 * ((2 * q) / (1 - (D : ℝ) ^ 2 * (2 * q))) ≤ 1
  K1 : 1 ≤ 2 * (1 - 2 * ((2 * q) / (1 - (D : ℝ) ^ 2 * (2 * q)))) ^ (D + 1)
  z : 2 * (D : ℝ) ^ 2 * ((2 * q) / μ) < 1
  cond : 2 * (D + 1) * (((2 * q) / μ) / (1 - 2 * (D : ℝ) ^ 2 * ((2 * q) / μ))) ≤
    (1 - 2 * q) ^ 2

/-- Flip-even slice functions. -/
def Even' (ψ : (V → Bool) → ℝ) : Prop := ∀ s, ψ (fun v => !s v) = ψ s

/-- `ψ_A = v₀ · χ_A`. -/
noncomputable def psi (q : ℝ) (A : Finset V) : (V → Bool) → ℝ :=
  fun s => TransferSlab.v₀ G q s * chi A s

omit [DecidableEq V] in
lemma transfer_herm (q : ℝ) : (transfer G q).IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
  exact transfer_symm G q

lemma S_symm (q : ℝ) : (transfer G q * transfer G q).IsSymm := by
  rw [IsSymm, transpose_mul, (transfer_symm G q).eq]

omit [DecidableEq V] in
lemma v₀_pos {q : ℝ} (hq : 0 < q) (s : V → Bool) : 0 < TransferSlab.v₀ G q s :=
  pow_pos (Real.sqrt_pos.mpr hq) _

omit [DecidableEq V] in
lemma v₀_even (q : ℝ) : Even' (TransferSlab.v₀ G q) := fun s => by
  simp only [TransferSlab.v₀, cost]; rw [cutSet_flip]

omit [DecidableEq V] in
lemma psi_empty (q : ℝ) : psi G q ∅ = TransferSlab.v₀ G q := by
  funext s; simp [psi, chi]

lemma iterate_lin {n : Type*} [Fintype n] (M : Matrix n n ℝ) {ι : Type*} (I : Finset ι)
    (c : ι → ℝ) (f : ι → n → ℝ) :
    ∀ L : ℕ, (M.mulVec)^[L] (∑ i ∈ I, c i • f i) = ∑ i ∈ I, c i • (M.mulVec)^[L] (f i) := by
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
    simp only [Function.iterate_succ_apply', ih, mulVec_sum, mulVec_smul]

/-- The Walsh coefficients of `ψ / v₀`. -/
noncomputable def wc' (q : ℝ) (ψ : (V → Bool) → ℝ) (A : Finset V) : ℝ :=
  Walsh.coef (fun s => ψ s / TransferSlab.v₀ G q s) A

lemma expand {q : ℝ} (hq : 0 < q) (ψ : (V → Bool) → ℝ) :
    ψ = ∑ A : Finset V, wc' G q ψ A • psi G q A := by
  funext s
  rw [Finset.sum_apply]
  have hv := (v₀_pos G hq s).ne'
  have hw := Walsh.walsh (fun s => ψ s / TransferSlab.v₀ G q s) s
  rw [div_eq_iff hv] at hw
  rw [hw, sum_mul]
  refine sum_congr rfl fun A _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, psi, chi, wc']
  ring

lemma coef_even {q : ℝ} (_hq : 0 < q) {ψ : (V → Bool) → ℝ} (hψ : Even' ψ) {A : Finset V}
    (hA : wc' G q ψ A ≠ 0) : Even A.card := by
  by_contra h
  apply hA
  refine Walsh.coef_odd _ (fun s => ?_) (Nat.not_even_iff_odd.mp h)
  rw [hψ, v₀_even G q s]

lemma S_eq_corr (q : ℝ) (x y : (V → Bool) → ℝ) (L : ℕ) :
    x ⬝ᵥ ((transfer G q * transfer G q).mulVec)^[L] y =
      x ⬝ᵥ ((transfer G q).mulVec)^[2 * L] y := by
  rw [iterate_sq]

/-- `⟨ψ, Sᴸ φ⟩` in Walsh coordinates. -/
lemma dot_expand {q : ℝ} (hq : 0 < q) (ψ φ : (V → Bool) → ℝ) (L : ℕ) :
    ψ ⬝ᵥ ((transfer G q * transfer G q).mulVec)^[L] φ =
      ∑ A : Finset V, ∑ B : Finset V, wc' G q ψ A * wc' G q φ B * corr G (2 * L) q A B := by
  rw [S_eq_corr]
  conv_lhs => rw [expand G hq ψ, expand G hq φ]
  rw [iterate_lin, sum_dotProduct]
  refine sum_congr rfl fun A _ => ?_
  rw [smul_dotProduct, dotProduct_sum, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun B _ => ?_
  rw [dotProduct_smul, smul_eq_mul]
  simp only [corr, ← mul_assoc]
  rfl

/-- The clustering constant of an observable. -/
noncomputable def Cf (q μ : ℝ) (D : ℕ) (b : V) (π : ∀ a, G.Walk b a) (A : Finset V) : ℝ :=
  4 * (∑ a ∈ A, ((π a).length : ℝ)) *
    (((2 * q) / μ) / (1 - 2 * (D : ℝ) ^ 2 * ((2 * q) / μ))) / (1 - 2 * q) ^ 3

variable {G plaqG}

lemma Cf_nonneg {q μ : ℝ} {D : ℕ} (R : Regime G plaqG q μ D) (b : V) (π : ∀ a, G.Walk b a)
    (A : Finset V) : 0 ≤ Cf G q μ D b π A := by
  have hq := R.q_pos; have hμ := R.μ_pos; have hz := R.z; have hy := R.y1
  unfold Cf
  have h1 : 0 ≤ (2 * q) / μ := div_nonneg (by linarith) hμ.le
  have h2 : 0 ≤ ((2 * q) / μ) / (1 - 2 * (D : ℝ) ^ 2 * ((2 * q) / μ)) := div_nonneg h1 (by linarith)
  have h3 : 0 ≤ ∑ a ∈ A, ((π a).length : ℝ) := sum_nonneg fun _ _ => Nat.cast_nonneg _
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) h3) h2) (pow_nonneg (by linarith) _)

lemma Z_pos {q μ : ℝ} {D : ℕ} (R : Regime G plaqG q μ D) (L : ℕ) :
    0 < TransferSlab.v₀ G q ⬝ᵥ ((transfer G q * transfer G q).mulVec)^[L] (TransferSlab.v₀ G q) := by
  rw [S_eq_corr, ← psi_empty]
  show 0 < corr G (2 * L) q ∅ ∅
  rw [corr_eq_sum G (2 * L) R.q_pos.le]
  simp only [chi, prod_empty, one_mul]
  exact sum_pos (fun σ _ => pow_pos R.q_pos _) univ_nonempty

lemma dot_left {q : ℝ} (hq : 0 < q) (ψ : (V → Bool) → ℝ) (B : Finset V) (L : ℕ) :
    ψ ⬝ᵥ ((transfer G q * transfer G q).mulVec)^[L] (psi G q B) =
      ∑ A : Finset V, wc' G q ψ A * corr G (2 * L) q A B := by
  rw [S_eq_corr]
  conv_lhs => rw [expand G hq ψ]
  rw [sum_dotProduct]
  refine sum_congr rfl fun A _ => ?_
  rw [smul_dotProduct, smul_eq_mul]
  simp only [corr]
  rfl

lemma dot_right {q : ℝ} (hq : 0 < q) (A : Finset V) (ψ : (V → Bool) → ℝ) (L : ℕ) :
    psi G q A ⬝ᵥ ((transfer G q * transfer G q).mulVec)^[L] ψ =
      ∑ B : Finset V, wc' G q ψ B * corr G (2 * L) q A B := by
  rw [S_eq_corr]
  conv_lhs => rw [expand G hq ψ]
  rw [iterate_lin, dotProduct_sum]
  refine sum_congr rfl fun B _ => ?_
  rw [dotProduct_smul, smul_eq_mul]
  simp only [corr]
  rfl

lemma Z_eq_corr (q : ℝ) (L : ℕ) :
    TransferSlab.v₀ G q ⬝ᵥ ((transfer G q * transfer G q).mulVec)^[L] (TransferSlab.v₀ G q) =
      corr G (2 * L) q ∅ ∅ := by
  rw [S_eq_corr, ← psi_empty]; rfl

/-- **Truncated decay in the even sector.** -/
theorem trunc_bound {q μ : ℝ} {D : ℕ} (R : Regime G plaqG q μ D) {ψ : (V → Bool) → ℝ}
    (hψ : Even' ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℕ,
      (ψ ⬝ᵥ ((transfer G q * transfer G q).mulVec)^[L] ψ) *
          (TransferSlab.v₀ G q ⬝ᵥ ((transfer G q * transfer G q).mulVec)^[L] (TransferSlab.v₀ G q)) -
        (ψ ⬝ᵥ ((transfer G q * transfer G q).mulVec)^[L] (TransferSlab.v₀ G q)) ^ 2 ≤
      C * (μ ^ 2) ^ L *
        (TransferSlab.v₀ G q ⬝ᵥ ((transfer G q * transfer G q).mulVec)^[L] (TransferSlab.v₀ G q)) ^ 2 := by
  have hq := R.q_pos
  set b : V := (R.connG.nonempty).some
  set π : ∀ a, G.Walk b a := fun a => (R.connG.preconnected b a).some
  set c := wc' G q ψ
  set F : Finset V → ℝ := fun A => Cf G q μ D b π A * Real.exp (Cf G q μ D b π A)
  have hF : ∀ A, 0 ≤ F A := fun A => mul_nonneg (Cf_nonneg R b π A) (Real.exp_pos _).le
  refine ⟨∑ A : Finset V, ∑ B : Finset V, |c A| * |c B| * F A,
    sum_nonneg fun A _ => sum_nonneg fun B _ =>
      mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (hF A), fun L => ?_⟩
  set S := transfer G q * transfer G q
  set v := TransferSlab.v₀ G q
  have hZ : v ⬝ᵥ (S.mulVec)^[L] v = corr G (2 * L) q ∅ ∅ := Z_eq_corr q L
  have hP : ψ ⬝ᵥ (S.mulVec)^[L] ψ =
      ∑ A : Finset V, ∑ B : Finset V, c A * c B * corr G (2 * L) q A B := dot_expand G hq ψ ψ L
  have hQ : ψ ⬝ᵥ (S.mulVec)^[L] v = ∑ A : Finset V, c A * corr G (2 * L) q A ∅ := by
    rw [show v = psi G q ∅ from (psi_empty G q).symm]; exact dot_left hq ψ ∅ L
  have hQ' : ψ ⬝ᵥ (S.mulVec)^[L] v = ∑ B : Finset V, c B * corr G (2 * L) q ∅ B := by
    rw [dot_iterate_comm S (S_symm G q) ψ v L, show v = psi G q ∅ from (psi_empty G q).symm]
    exact dot_right hq ∅ ψ L
  have hsq : (ψ ⬝ᵥ (S.mulVec)^[L] v) ^ 2 =
      (∑ A : Finset V, c A * corr G (2 * L) q A ∅) *
        ∑ B : Finset V, c B * corr G (2 * L) q ∅ B := by
    rw [sq]; nth_rw 1 [hQ]; rw [hQ']
  rw [hsq, hP, hZ, sum_mul_sum, sum_mul, ← sum_sub_distrib, sum_mul, sum_mul]
  refine sum_le_sum fun A _ => ?_
  rw [sum_mul, ← sum_sub_distrib, sum_mul, sum_mul]
  refine sum_le_sum fun B _ => ?_
  set Z := corr G (2 * L) q ∅ ∅
  have hRHS : 0 ≤ |c A| * |c B| * F A * (μ ^ 2) ^ L * Z ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (hF A))
      (pow_nonneg (sq_nonneg _) _)) (sq_nonneg _)
  by_cases h0 : c A = 0 ∨ c B = 0
  · rcases h0 with h | h <;> simp [h] at hRHS ⊢
  push Not at h0
  have hA := coef_even G hq hψ h0.1
  have hB := coef_even G hq hψ h0.2
  have hcl := transfer_clustering G (2 * L) plaqG R.connG R.plaqE R.plaqP R.genG b π hA hB D
    (R.degree (2 * L)) q μ hq.le R.μ_pos R.μ_lt.le R.y1 R.Dy R.s1 R.K1 R.z R.cond
  dsimp only at hcl
  have hcl' : |corr G (2 * L) q A B * Z - corr G (2 * L) q A ∅ * corr G (2 * L) q ∅ B| ≤
      F A * (μ ^ 2) ^ L * Z ^ 2 := by
    rw [← pow_mul]; exact hcl
  calc c A * c B * corr G (2 * L) q A B * Z - c A * corr G (2 * L) q A ∅ * (c B * corr G (2 * L) q ∅ B)
      = (c A * c B) * (corr G (2 * L) q A B * Z - corr G (2 * L) q A ∅ * corr G (2 * L) q ∅ B) := by
        ring
    _ ≤ |c A * c B| * |corr G (2 * L) q A B * Z - corr G (2 * L) q A ∅ * corr G (2 * L) q ∅ B| := by
        rw [← abs_mul]; exact le_abs_self _
    _ ≤ |c A * c B| * (F A * (μ ^ 2) ^ L * Z ^ 2) :=
        mul_le_mul_of_nonneg_left hcl' (abs_nonneg _)
    _ = |c A| * |c B| * F A * (μ ^ 2) ^ L * Z ^ 2 := by rw [abs_mul]; ring

lemma dot_self_pos {n : Type*} [Fintype n] {x : n → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ x := by
  have hnn : 0 ≤ x ⬝ᵥ x := sum_nonneg fun i _ => mul_self_nonneg (x i)
  rcases hnn.lt_or_eq with h | h
  · exact h
  · exfalso; apply hx; funext i
    have := (sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (x i)).mp h.symm i (mem_univ _)
    simpa using this

lemma eigen_nonneg (q : ℝ) {ψ : (V → Bool) → ℝ} (hψ0 : ψ ≠ 0) {lam : ℝ}
    (h : (transfer G q * transfer G q) *ᵥ ψ = lam • ψ) : 0 ≤ lam := by
  have h1 : ψ ⬝ᵥ ((transfer G q * transfer G q) *ᵥ ψ) =
      (transfer G q *ᵥ ψ) ⬝ᵥ (transfer G q *ᵥ ψ) := by
    rw [← mulVec_mulVec, dot_mulVec_comm _ (transfer_symm G q)]
  rw [h, dotProduct_smul, smul_eq_mul] at h1
  have h2 : 0 ≤ (transfer G q *ᵥ ψ) ⬝ᵥ (transfer G q *ᵥ ψ) :=
    sum_nonneg fun i _ => mul_self_nonneg _
  have h3 := dot_self_pos hψ0
  by_contra hl; push Not at hl
  have : lam * (ψ ⬝ᵥ ψ) < 0 := mul_neg_of_neg_of_pos hl h3
  linarith

/-- **The gap.** In the flip-even sector of `S = T²`: there is a visible top `Λ > 0` with
`κ Λᴸ ≤ Z_L ≤ K Λᴸ`; every even eigenvalue is either `≤ μ² Λ` or equal to `Λ` with an
eigenvector seen by `v₀`; and the even `Λ`-eigenspace is one-dimensional. -/
theorem slab_gap {q μ : ℝ} {D : ℕ} (R : Regime G plaqG q μ D) :
    ∃ Λ κ K : ℝ, 0 < Λ ∧ 0 < κ ∧ 0 ≤ K ∧
      (∀ L : ℕ,
        κ * Λ ^ L ≤ TransferSlab.v₀ G q ⬝ᵥ
            ((transfer G q * transfer G q).mulVec)^[L] (TransferSlab.v₀ G q) ∧
        TransferSlab.v₀ G q ⬝ᵥ ((transfer G q * transfer G q).mulVec)^[L] (TransferSlab.v₀ G q)
          ≤ K * Λ ^ L) ∧
      (∀ (ψ : (V → Bool) → ℝ) (lam : ℝ), ψ ≠ 0 → Even' ψ →
        (transfer G q * transfer G q) *ᵥ ψ = lam • ψ →
        lam ≤ μ ^ 2 * Λ ∨ (lam = Λ ∧ ψ ⬝ᵥ TransferSlab.v₀ G q ≠ 0)) ∧
      (∀ ψ₁ ψ₂ : (V → Bool) → ℝ, Even' ψ₁ → Even' ψ₂ →
        (transfer G q * transfer G q) *ᵥ ψ₁ = Λ • ψ₁ →
        (transfer G q * transfer G q) *ᵥ ψ₂ = Λ • ψ₂ →
        (ψ₂ ⬝ᵥ TransferSlab.v₀ G q) • ψ₁ = (ψ₁ ⬝ᵥ TransferSlab.v₀ G q) • ψ₂) := by
  have hq := R.q_pos
  set S := transfer G q * transfer G q
  set v := TransferSlab.v₀ G q
  have hv0 : v ≠ 0 := fun h => by
    have h1 : v (fun _ => false) = 0 := by rw [h]; rfl
    exact (v₀_pos G hq (fun _ => false)).ne' h1
  obtain ⟨Λ, κ, K, hΛ0, hκ, hK, hb⟩ := visible_top (transfer G q) (transfer_herm G q) v hv0
  have hZpos : ∀ L, 0 < v ⬝ᵥ (S.mulVec)^[L] v := Z_pos R
  have hΛ : 0 < Λ := by
    rcases hΛ0.lt_or_eq with h | h
    · exact h
    · exfalso; have := (hb 1).2; rw [← h] at this; have := hZpos 1; simp at *; linarith
  have hμ2 : μ ^ 2 < 1 := by
    have := R.μ_lt; have := R.μ_pos; nlinarith
  have hρΛ : 0 ≤ μ ^ 2 * Λ := mul_nonneg (sq_nonneg _) hΛ.le
  -- eigenvectors under iteration
  have hit : ∀ {ψ : (V → Bool) → ℝ} {lam : ℝ}, S *ᵥ ψ = lam • ψ → ∀ L,
      (S.mulVec)^[L] ψ = lam ^ L • ψ := fun h L => iterate_eig S _ _ h L
  have hQ : ∀ {ψ : (V → Bool) → ℝ} {lam : ℝ}, S *ᵥ ψ = lam • ψ → ∀ L,
      ψ ⬝ᵥ (S.mulVec)^[L] v = lam ^ L * (ψ ⬝ᵥ v) := fun h L => by
    rw [dot_iterate_comm S (S_symm G q), hit h, dotProduct_smul, smul_eq_mul, dotProduct_comm]
  -- vectors not seen by `v₀`
  have hperp : ∀ (ψ : (V → Bool) → ℝ) (lam : ℝ), ψ ≠ 0 → Even' ψ → S *ᵥ ψ = lam • ψ →
      ψ ⬝ᵥ v = 0 → lam ≤ μ ^ 2 * Λ := by
    intro ψ lam hψ0 hψ h hpv
    obtain ⟨C, hC, hcor⟩ := trunc_bound R hψ
    have hN := dot_self_pos hψ0
    refine rate_le (eigen_nonneg q hψ0 h) hρΛ hN (C := C * K) fun L => ?_
    have h1 := hcor L
    rw [hQ h L, hpv, mul_zero, hit h L, dotProduct_smul, smul_eq_mul] at h1
    have hZ := hZpos L
    have h2 : lam ^ L * (ψ ⬝ᵥ ψ) ≤ C * (μ ^ 2) ^ L * (v ⬝ᵥ (S.mulVec)^[L] v) := by
      have : lam ^ L * (ψ ⬝ᵥ ψ) * (v ⬝ᵥ (S.mulVec)^[L] v) ≤
          (C * (μ ^ 2) ^ L * (v ⬝ᵥ (S.mulVec)^[L] v)) * (v ⬝ᵥ (S.mulVec)^[L] v) := by
        nlinarith
      exact le_of_mul_le_mul_right this hZ
    calc lam ^ L * (ψ ⬝ᵥ ψ) ≤ C * (μ ^ 2) ^ L * (v ⬝ᵥ (S.mulVec)^[L] v) := h2
      _ ≤ C * (μ ^ 2) ^ L * (K * Λ ^ L) :=
          mul_le_mul_of_nonneg_left (hb L).2 (mul_nonneg hC (pow_nonneg (sq_nonneg _) _))
      _ = C * K * (μ ^ 2 * Λ) ^ L := by rw [mul_pow]; ring
  -- nothing even lies above the visible top
  have habove : ∀ (ψ : (V → Bool) → ℝ) (lam : ℝ), ψ ≠ 0 → Even' ψ → S *ᵥ ψ = lam • ψ →
      lam ≤ Λ := by
    intro ψ lam hψ0 hψ h
    by_contra hl; push Not at hl
    have hlam0 := eigen_nonneg q hψ0 h
    have hpv : ψ ⬝ᵥ v = 0 := by
      by_contra hpv
      set M := ∑ A : Finset V, |wc' G q ψ A|
      have hbound : ∀ L : ℕ, lam ^ L * |ψ ⬝ᵥ v| ≤ (M * K) * Λ ^ L := by
        intro L
        have e1 : |ψ ⬝ᵥ (S.mulVec)^[L] v| = lam ^ L * |ψ ⬝ᵥ v| := by
          rw [hQ h L, abs_mul, abs_of_nonneg (pow_nonneg hlam0 _)]
        rw [← e1]
        have e2 : ψ ⬝ᵥ (S.mulVec)^[L] v = ∑ A : Finset V, wc' G q ψ A * corr G (2 * L) q A ∅ := by
          rw [show v = psi G q ∅ from (psi_empty G q).symm]; exact dot_left hq ψ ∅ L
        rw [e2]
        calc |∑ A : Finset V, wc' G q ψ A * corr G (2 * L) q A ∅|
            ≤ ∑ A : Finset V, |wc' G q ψ A| * corr G (2 * L) q ∅ ∅ := by
              refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun A _ => ?_)
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (abs_corr_le G (2 * L) hq.le A ∅) (abs_nonneg _)
          _ = M * (v ⬝ᵥ (S.mulVec)^[L] v) := by rw [← sum_mul, Z_eq_corr q L]
          _ ≤ M * (K * Λ ^ L) := mul_le_mul_of_nonneg_left (hb L).2
              (sum_nonneg fun _ _ => abs_nonneg _)
          _ = M * K * Λ ^ L := by ring
      have := rate_le hlam0 hΛ.le (abs_pos.mpr hpv) hbound
      linarith
    have := hperp ψ lam hψ0 hψ h hpv
    nlinarith
  refine ⟨Λ, κ, K, hΛ, hκ, hK, hb, ?_, ?_⟩
  · intro ψ lam hψ0 hψ h
    have hle := habove ψ lam hψ0 hψ h
    rcases hle.lt_or_eq with hlt | heq
    · left
      obtain ⟨C, hC, hcor⟩ := trunc_bound R hψ
      exact GapFromCorrelation.gap_of_truncated_decay S (S_symm G q) v ψ hψ0 lam Λ h
        (eigen_nonneg q hψ0 h) hlt κ K hκ hK (fun L => (hb L).1) (fun L => (hb L).2)
        (μ ^ 2) C (pow_pos R.μ_pos 2) hC hcor
    · by_cases hpv : ψ ⬝ᵥ v = 0
      · exact Or.inl (hperp ψ lam hψ0 hψ h hpv)
      · exact Or.inr ⟨heq, hpv⟩
  · intro ψ₁ ψ₂ h₁ h₂ e₁ e₂
    set χ := (ψ₂ ⬝ᵥ v) • ψ₁ - (ψ₁ ⬝ᵥ v) • ψ₂
    by_contra hne
    have hχ0 : χ ≠ 0 := fun h => hne (sub_eq_zero.mp h)
    have hχe : Even' χ := fun s => by simp only [χ, Pi.sub_apply, Pi.smul_apply, h₁ s, h₂ s]
    have hχS : S *ᵥ χ = Λ • χ := by
      simp only [χ, mulVec_sub, mulVec_smul, e₁, e₂, smul_sub, smul_comm Λ]
    have hχv : χ ⬝ᵥ v = 0 := by
      simp only [χ, sub_dotProduct, smul_dotProduct, smul_eq_mul]; ring
    have := hperp χ Λ hχ0 hχe hχS hχv
    nlinarith

end PMAction.MassGap.SlabGap
