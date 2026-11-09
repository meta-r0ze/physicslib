import PMAction.MassGap.TransferSlab
import PMAction.MassGap.ParitySigns
import PMAction.MassGap.SlabClustering

/-!
# Slice parity observables in the transfer picture

For an even set of sites `A ⊆ V`, the slice observable `χ_A(s) = Π_{a ∈ A} sgn(s a)` is
invariant under the global flip. It is a product of relative spins `sgn(s b)·sgn(s a)`, and
each relative spin is a product over boundary edges crossed by a walk from `b` to `a`
*inside the slice*. So `χ_A` at tick `t` is a sign twist `sw ε` of the edge weights, with
the sign edges `ε` lying in slice `t`.

* `rel_spin`: `sgn(σ x)·sgn(σ p) = Π_{e ∈ ∂σ} (-1)^{count e π}` for any walk `π : x → p`.
* `slice_obs`: `χ_A(σ_t)·Π_{∂σ} ω = Π_{∂σ} sw ε ω`, with `ε` the edges crossed an odd
  number of times by the lifted walks; `tau e = t` on every such edge.
* `flip_sum`: flip-invariant sums over all configurations are twice the pinned sum.
* `corr_eq_Z`: `H(A,B) = Σ_σ χ_A(σ_0) χ_B(σ_L) q^{|∂σ|} = 2 · Z(sw εA (sw εB q))`.
* `transfer_clustering`: `slab_clustering` read through the transfer matrix:
  `|⟨ψ_A, Tᴸ ψ_B⟩⟨v₀, Tᴸ v₀⟩ - ⟨ψ_A, Tᴸ v₀⟩⟨v₀, Tᴸ ψ_B⟩| ≤ C e^C μᴸ ⟨ψ_A, Tᴸ v₀⟩⟨v₀, Tᴸ ψ_B⟩`
  with `ψ_A = v₀ · χ_A`.
-/

namespace PMAction.MassGap.SlabObservables
open Finset SimpleGraph ContourRepresentation HistorySum SlabGeometry ParitySigns TransferSlab
  SlabTime SlabClustering PolymerConvergence ContourGas
open Classical

/-- **Relative spin along a walk.** -/
theorem rel_spin {X : Type*} [Fintype X] [DecidableEq X] (Γ : SimpleGraph X) [DecidableRel Γ.Adj]
    (σ : X → Bool) {x p : X} (π : Γ.Walk x p) :
    sgn (σ x) * sgn (σ p) = ∏ e ∈ cutSet Γ σ, (-1 : ℝ) ^ π.edges.count e := by
  rw [← neg_one_pow_hits]
  have h := cut_parity (cutSet_isCut Γ σ) π
  rcases Nat.even_or_odd (hits (cutSet Γ σ) π) with he | ho
  · have : σ x = σ p := by
      by_contra hc
      exact (Nat.not_even_iff_odd.mpr (h.mpr hc)) he
    rw [this, he.neg_one_pow]; cases σ p <;> simp [sgn]
  · have := h.mp ho
    rw [ho.neg_one_pow]
    cases hx : σ x <;> cases hp : σ p <;> simp_all [sgn]

/-- Twisting by a sign pattern on the boundary. -/
lemma sign_twist {X : Type*} (C : Finset (Sym2 X)) (m : Sym2 X → ℕ) (ω : Sym2 X → ℝ) :
    (∏ e ∈ C, (-1 : ℝ) ^ m e) * ∏ e ∈ C, ω e =
      ∏ e ∈ C, ((if decide (Odd (m e)) = true then -1 else 1) * ω e) := by
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun e _ => ?_
  rcases Nat.even_or_odd (m e) with h | h
  · rw [h.neg_one_pow]; simp [Nat.not_odd_iff_even.mpr h]
  · rw [h.neg_one_pow]; simp [h]

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (L : ℕ)

/-- The slice parity observable. -/
def chi (A : Finset V) (s : V → Bool) : ℝ := ∏ a ∈ A, sgn (s a)

lemma sgn_sq (b : Bool) : sgn b * sgn b = 1 := by cases b <;> simp [sgn]

omit [Fintype V] [DecidableEq V] in
lemma abs_chi_le (A : Finset V) (s : V → Bool) : |chi A s| ≤ 1 := by
  rw [chi, abs_prod]
  exact prod_le_one₀ (fun _ _ => abs_nonneg _) fun a _ => by cases s a <;> simp [sgn]

omit [Fintype V] [DecidableEq V] in
lemma chi_flip {A : Finset V} (hA : Even A.card) (s : V → Bool) :
    chi A (fun v => !s v) = chi A s := by
  unfold chi
  have : ∀ a, sgn (!s a) = -1 * sgn (s a) := fun a => by cases s a <;> simp [sgn]
  simp only [this, prod_mul_distrib, prod_const, hA.neg_one_pow, one_mul]

/-- The walk-multiplicity of a slice observable, lifted to slice `t`. -/
noncomputable def multT (b : V) (A : Finset V) (π : ∀ a, G.Walk b a) (t : Fin (L + 1))
    (e : Sym2 (V × Fin (L + 1))) : ℕ :=
  ∑ a ∈ A, ((π a).boxProdLeft (pathGraph (L + 1)) t).edges.count e

/-- Its odd edges. -/
noncomputable def epsT (b : V) (A : Finset V) (π : ∀ a, G.Walk b a) (t : Fin (L + 1))
    (e : Sym2 (V × Fin (L + 1))) : Bool :=
  decide (Odd (multT G L b A π t e))

omit [Fintype V] [DecidableRel G.Adj] in
lemma epsT_tau {b : V} {A : Finset V} {π : ∀ a, G.Walk b a} {t : Fin (L + 1)}
    {e : Sym2 (V × Fin (L + 1))} (he : epsT G L b A π t e = true) : tau L e = t := by
  have hpos : multT G L b A π t e ≠ 0 := by
    intro h0; rw [epsT, h0] at he; simp at he
  obtain ⟨a, -, ha⟩ := exists_ne_zero_of_sum_ne_zero hpos
  have hmem : e ∈ ((π a).boxProdLeft (pathGraph (L + 1)) t).edges :=
    List.count_pos_iff.mp (Nat.pos_of_ne_zero ha)
  have key : ∀ e ∈ ((π a).map (G.boxProdLeft (pathGraph (L + 1)) t).toHom).edges,
      tau L e = t := by
    intro e he
    rw [Walk.edges_map, List.mem_map] at he
    obtain ⟨e', -, rfl⟩ := he
    induction e' using Sym2.ind with
    | h x y => simp [Sym2.map_mk, boxProdLeft]
  exact key e hmem

omit [DecidableRel G.Adj] in
/-- **A slice observable is a sign twist.** -/
theorem slice_obs (σ : V × Fin (L + 1) → Bool) {b : V} {A : Finset V} (hA : Even A.card)
    (π : ∀ a, G.Walk b a) (t : Fin (L + 1)) (ω : Sym2 (V × Fin (L + 1)) → ℝ) :
    chi A (slice σ t) * ∏ e ∈ cutSet (slab G L) σ, ω e =
      ∏ e ∈ cutSet (slab G L) σ, sw L (epsT G L b A π t) ω e := by
  have hchi : chi A (slice σ t) =
      ∏ a ∈ A, (sgn (σ (b, t)) * sgn (σ (a, t))) := by
    have h1 : sgn (σ (b, t)) ^ A.card = 1 := by
      cases σ (b, t) <;> simp [sgn, hA.neg_one_pow]
    rw [prod_mul_distrib, prod_const, h1, one_mul]
    rfl
  rw [hchi]
  have hrel : ∀ a ∈ A, sgn (σ (b, t)) * sgn (σ (a, t)) =
      ∏ e ∈ cutSet (slab G L) σ,
        (-1 : ℝ) ^ ((π a).boxProdLeft (pathGraph (L + 1)) t).edges.count e :=
    fun a _ => rel_spin (slab G L) σ _
  rw [prod_congr rfl hrel, prod_comm]
  have : ∀ e ∈ cutSet (slab G L) σ,
      ∏ a ∈ A, (-1 : ℝ) ^ ((π a).boxProdLeft (pathGraph (L + 1)) t).edges.count e =
        (-1 : ℝ) ^ multT G L b A π t e := fun e _ => by rw [prod_pow_eq_pow_sum, multT]
  rw [prod_congr rfl this, sign_twist]
  rfl

/-- **Flip symmetry.** -/
theorem flip_sum {X : Type*} [Fintype X] [DecidableEq X] (r : X) (F : (X → Bool) → ℝ)
    (hF : ∀ σ, F (fun x => !σ x) = F σ) :
    ∑ σ, F σ = 2 * ∑ σ ∈ univ.filter (fun σ : X → Bool => σ r = false), F σ := by
  rw [← sum_filter_add_sum_filter_not univ (fun σ : X → Bool => σ r = false), two_mul]
  congr 1
  refine sum_nbij' (fun σ x => !σ x) (fun σ x => !σ x) ?_ ?_ ?_ ?_ ?_
  · intro σ hσ; simp only [mem_filter, mem_univ, true_and] at hσ ⊢; simp [hσ]
  · intro σ hσ; simp only [mem_filter, mem_univ, true_and] at hσ ⊢; simpa using hσ
  · intro σ _; simp
  · intro σ _; simp
  · intro σ _; exact (hF σ).symm

lemma cutSet_flip {X : Type*} [Fintype X] (Γ : SimpleGraph X) [DecidableRel Γ.Adj]
    (σ : X → Bool) : cutSet Γ (fun x => !σ x) = cutSet Γ σ := by
  ext e
  induction e using Sym2.ind with
  | h x y => rw [mem_cutSet_iff, mem_cutSet_iff]; cases σ x <;> cases σ y <;> simp

variable (plaqG : Finset (Finset (Sym2 V)))

/-- **Slice correlations are twisted contour partition functions.** -/
theorem corr_eq_Z (hconnG : G.Connected) (hplaqE : ∀ P ∈ plaqG, P ⊆ G.edgeFinset)
    (hplaqP : ∀ P ∈ plaqG, IsPlaquette G P) (hgenG : PlaquettesGenerate G plaqG)
    (b : V) (π : ∀ a, G.Walk b a) {A B : Finset V} (hA : Even A.card) (hB : Even B.card)
    (q : ℝ) :
    (∑ σ : V × Fin (L + 1) → Bool,
        chi A (slice σ 0) * chi B (slice σ (Fin.last L)) * q ^ (cutSet (slab G L) σ).card) =
      2 * Z (Incompat (slab G L) (slabPlaq G L plaqG))
        (wc G L plaqG (sw L (epsT G L b A π 0) (sw L (epsT G L b B π (Fin.last L))
          (fun _ => q)))) univ := by
  have hconn : (slab G L).Connected := hconnG.boxProd (pathGraph_connected L)
  have hgen := slab_generate G L plaqG hconnG b hplaqE hgenG
  have hplaq := slabPlaq_isPlaquette G L plaqG hplaqP
  -- rewrite the integrand as a product over the boundary
  have hint : ∀ σ : V × Fin (L + 1) → Bool,
      chi A (slice σ 0) * chi B (slice σ (Fin.last L)) * q ^ (cutSet (slab G L) σ).card =
        ∏ e ∈ cutSet (slab G L) σ, sw L (epsT G L b A π 0)
          (sw L (epsT G L b B π (Fin.last L)) fun _ => q) e := by
    intro σ
    rw [← slice_obs G L σ hA π 0, ← slice_obs G L σ hB π (Fin.last L), prod_const]
    ring
  simp only [hint]
  rw [flip_sum ((b, 0) : V × Fin (L + 1)) _ (fun σ => by rw [cutSet_flip])]
  congr 1
  rw [history_sum (slab G L) hconn (b, 0)
    (fun C => ∏ e ∈ C, sw L (epsT G L b A π 0) (sw L (epsT G L b B π (Fin.last L)) fun _ => q) e)]
  exact contour_gas_weighted (slab G L) (slabPlaq G L plaqG) hconn (b, 0) hgen hplaq _

omit [Fintype V] [DecidableRel G.Adj] in
lemma epsT_empty (b : V) (π : ∀ a, G.Walk b a) (t : Fin (L + 1)) :
    epsT G L b ∅ π t = fun _ => false := by
  funext e; simp [epsT, multT]

omit [Fintype V] [DecidableEq V] in
lemma sw_false (ω : Sym2 (V × Fin (L + 1)) → ℝ) : sw L (fun _ => false) ω = ω := by
  funext e; simp [sw]

omit [DecidableRel G.Adj] in
lemma card_epsT_le (b : V) (A : Finset V) (π : ∀ a, G.Walk b a) (t : Fin (L + 1)) :
    ((univ.filter fun e => epsT G L b A π t e = true).card : ℝ) ≤
      ∑ a ∈ A, ((π a).length : ℝ) := by
  have hsub : (univ.filter fun e => epsT G L b A π t e = true) ⊆
      A.biUnion fun a => ((π a).boxProdLeft (pathGraph (L + 1)) t).edges.toFinset := by
    intro e he
    simp only [mem_filter, mem_univ, true_and] at he
    have hpos : multT G L b A π t e ≠ 0 := by
      intro h0; rw [epsT, h0] at he; simp at he
    obtain ⟨a, ha, hne⟩ := exists_ne_zero_of_sum_ne_zero hpos
    exact mem_biUnion.mpr ⟨a, ha, List.mem_toFinset.mpr
      (List.count_pos_iff.mp (Nat.pos_of_ne_zero hne))⟩
  have h1 := card_le_card hsub
  have h2 := card_biUnion_le (s := A)
    (t := fun a => ((π a).boxProdLeft (pathGraph (L + 1)) t).edges.toFinset)
  have h3 : ∀ a ∈ A, (((π a).boxProdLeft (pathGraph (L + 1)) t).edges.toFinset).card ≤
      (π a).length := fun a _ => by
    refine (List.toFinset_card_le _).trans ?_
    rw [Walk.length_edges]; exact le_of_eq (Walk.length_map _ _)
  have h4 := sum_le_sum h3
  exact_mod_cast h1.trans (h2.trans h4)

/-- The slab correlation in the transfer picture. -/
noncomputable def corr (q : ℝ) (A B : Finset V) : ℝ :=
  (fun s => TransferSlab.v₀ G q s * chi A s) ⬝ᵥ
    ((transfer G q).mulVec)^[L] (fun s => TransferSlab.v₀ G q s * chi B s)

lemma corr_eq_sum {q : ℝ} (hq : 0 ≤ q) (A B : Finset V) :
    corr G L q A B = ∑ σ : V × Fin (L + 1) → Bool,
      chi A (slice σ 0) * chi B (slice σ (Fin.last L)) * q ^ (cutSet (slab G L) σ).card :=
  (slab_transfer G L hq _ _).symm

lemma abs_corr_le {q : ℝ} (hq : 0 ≤ q) (A B : Finset V) :
    |corr G L q A B| ≤ corr G L q ∅ ∅ := by
  rw [corr_eq_sum G L hq, corr_eq_sum G L hq]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun σ _ => ?_)
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hq _)]
  simp only [chi, prod_empty, one_mul]
  have h1 := abs_chi_le A (slice σ 0)
  have h2 := abs_chi_le B (slice σ (Fin.last L))
  have h3 : 0 ≤ q ^ (cutSet (slab G L) σ).card := pow_nonneg hq _
  calc |chi A (slice σ 0)| * |chi B (slice σ (Fin.last L))| * q ^ (cutSet (slab G L) σ).card
      ≤ 1 * 1 * q ^ (cutSet (slab G L) σ).card := by gcongr
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
/-- **Transfer clustering.** For even slice observables, the transfer-matrix correlations
cluster at rate `μ` per tick, with a constant independent of the slab length. -/
theorem transfer_clustering (hconnG : G.Connected) (hplaqE : ∀ P ∈ plaqG, P ⊆ G.edgeFinset)
    (hplaqP : ∀ P ∈ plaqG, IsPlaquette G P) (hgenG : PlaquettesGenerate G plaqG)
    (b : V) (π : ∀ a, G.Walk b a) {A B : Finset V} (hA : Even A.card) (hB : Even B.card)
    (D : ℕ) (hD : ∀ e, (plaqGraph (slabPlaq G L plaqG)).degree e ≤ D)
    (q μ : ℝ) (hq : 0 ≤ q) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (hy1 : 2 * q ≤ 1 / 2) (hDy : (D : ℝ) ^ 2 * (2 * q) < 1)
    (hs1 : 2 * ((2 * q) / (1 - (D : ℝ) ^ 2 * (2 * q))) ≤ 1)
    (hK : 1 ≤ 2 * (1 - 2 * ((2 * q) / (1 - (D : ℝ) ^ 2 * (2 * q)))) ^ (D + 1))
    (hz : 2 * (D : ℝ) ^ 2 * ((2 * q) / μ) < 1)
    (hcond : 2 * (D + 1) * (((2 * q) / μ) / (1 - 2 * (D : ℝ) ^ 2 * ((2 * q) / μ))) ≤
      (1 - 2 * q) ^ 2) :
    let CA := 4 * (∑ a ∈ A, ((π a).length : ℝ)) *
      (((2 * q) / μ) / (1 - 2 * (D : ℝ) ^ 2 * ((2 * q) / μ))) / (1 - 2 * q) ^ 3
    |corr G L q A B * corr G L q ∅ ∅ - corr G L q A ∅ * corr G L q ∅ B| ≤
      CA * Real.exp CA * μ ^ L * corr G L q ∅ ∅ ^ 2 := by
  intro CA
  set εA := epsT G L b A π 0
  set εB := epsT G L b B π (Fin.last L)
  set ω : Sym2 (V × Fin (L + 1)) → ℝ := fun _ => q
  have hA0 : ∀ e, εA e = true → tau L e = 0 := fun e he => by
    have := epsT_tau G L he; simpa using this
  have hBL : ∀ e, εB e = true → tau L e = L := fun e he => by
    have := epsT_tau G L he; simpa using this
  have hc := slab_clustering G L plaqG D hD ω q μ hq (fun _ => by simp [ω, abs_of_nonneg hq])
    hμ0 hμ1 εA εB hA0 hBL hy1 hDy hs1 hK hz hcond
  dsimp only at hc
  set ZAB := Z (Incompat (slab G L) (slabPlaq G L plaqG)) (wc G L plaqG (sw L εA (sw L εB ω))) univ
  set ZA := Z (Incompat (slab G L) (slabPlaq G L plaqG)) (wc G L plaqG (sw L εA ω)) univ
  set ZB := Z (Incompat (slab G L) (slabPlaq G L plaqG)) (wc G L plaqG (sw L εB ω)) univ
  set Z0 := Z (Incompat (slab G L) (slabPlaq G L plaqG)) (wc G L plaqG ω) univ
  have he0 : Even (∅ : Finset V).card := by simp
  have hAB : corr G L q A B = 2 * ZAB := by
    rw [corr_eq_sum G L hq, corr_eq_Z G L plaqG hconnG hplaqE hplaqP hgenG b π hA hB q]
  have hA' : corr G L q A ∅ = 2 * ZA := by
    rw [corr_eq_sum G L hq, corr_eq_Z G L plaqG hconnG hplaqE hplaqP hgenG b π hA he0 q,
      epsT_empty, sw_false]
  have hB' : corr G L q ∅ B = 2 * ZB := by
    rw [corr_eq_sum G L hq, corr_eq_Z G L plaqG hconnG hplaqE hplaqP hgenG b π he0 hB q,
      epsT_empty, sw_false]
  have h0 : corr G L q ∅ ∅ = 2 * Z0 := by
    rw [corr_eq_sum G L hq, corr_eq_Z G L plaqG hconnG hplaqE hplaqP hgenG b π he0 he0 q,
      epsT_empty, epsT_empty, sw_false, sw_false]
  -- the constant
  set C₁ := 4 * ((univ.filter fun e => εA e = true).card : ℝ) *
      (((2 * q) / μ) / (1 - 2 * (D : ℝ) ^ 2 * ((2 * q) / μ))) / (1 - 2 * q) ^ 3 with hC₁
  have hz0 : 0 ≤ (2 * q) / μ := div_nonneg (by linarith) hμ0.le
  have hsz : 0 ≤ ((2 * q) / μ) / (1 - 2 * (D : ℝ) ^ 2 * ((2 * q) / μ)) :=
    div_nonneg hz0 (by linarith)
  have hden : 0 < (1 - 2 * q) ^ 3 := pow_pos (by linarith) _
  have hC₁0 : 0 ≤ C₁ := by
    rw [hC₁]; exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hsz)
      hden.le
  have hC₁A : C₁ ≤ CA := by
    rw [hC₁]
    have := card_epsT_le G L b A π 0
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (by norm_num)) hsz) hden.le
  have hmono : C₁ * Real.exp C₁ ≤ CA * Real.exp CA :=
    mul_le_mul hC₁A (Real.exp_le_exp.mpr hC₁A) (Real.exp_pos _).le (hC₁0.trans hC₁A)
  have hμL : 0 ≤ μ ^ L := pow_nonneg hμ0.le _
  have habs : |ZA * ZB| ≤ Z0 ^ 2 := by
    have h1 := abs_corr_le G L hq A ∅
    have h2 := abs_corr_le G L hq ∅ B
    rw [hA', h0, abs_mul] at h1
    rw [hB', h0, abs_mul] at h2
    rw [abs_mul, sq]
    have hZ0 : 0 ≤ Z0 := by
      have := abs_nonneg (corr G L q A ∅)
      have h3 := abs_corr_le G L hq A ∅
      rw [h0] at h3; linarith
    norm_num at h1 h2
    exact mul_le_mul h1 h2 (abs_nonneg _) hZ0
  rw [hAB, hA', hB', h0]
  calc |2 * ZAB * (2 * Z0) - 2 * ZA * (2 * ZB)| = 4 * |ZAB * Z0 - ZA * ZB| := by
        rw [show 2 * ZAB * (2 * Z0) - 2 * ZA * (2 * ZB) = 4 * (ZAB * Z0 - ZA * ZB) by ring,
          abs_mul]; norm_num
    _ ≤ 4 * (C₁ * Real.exp C₁ * μ ^ L * |ZA * ZB|) := by
        gcongr
        exact hc.trans (mul_le_mul_of_nonneg_left (le_abs_self _)
          (mul_nonneg (mul_nonneg hC₁0 (Real.exp_pos _).le) hμL))
    _ ≤ 4 * (CA * Real.exp CA * μ ^ L * Z0 ^ 2) := by
        gcongr
    _ = CA * Real.exp CA * μ ^ L * (2 * Z0) ^ 2 := by ring

end PMAction.MassGap.SlabObservables
