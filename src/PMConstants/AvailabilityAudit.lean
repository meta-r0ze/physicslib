import PMConstants.General.ReferenceCapacity
import PMSubstrate.Sectors
import Mathlib.Tactic

/-!
# Availability measures and event semantics on the actual phase grid

Integrated from Claude's availability audit. Counterexamples
concern the stated measure/encoding models, not all substrate postulates.

Uses `Grid`, `gridTick`, `gridUpdate` from `PMConstants.General.ReferenceCapacity` and `cD4`
from `PMSubstrate.Sectors`. Nothing here assumes a uniform measure on `Grid`.
-/

noncomputable section
namespace PMConstants.AvailabilityAudit
open Finset Function PMConstants.General.ReferenceCapacity
open Fin.NatCast

abbrev Mass := Grid → ℝ

def TickInvariant (μ : Mass) : Prop := ∀ x, μ (gridTick x) = μ x
def Normalized (μ : Mass) : Prop := (∀ x, 0 ≤ μ x) ∧ ∑ x, μ x = 1

lemma rot_add (k : ℕ) (t : Fin 43) : (finRotate 43)^[k] t = t + (k : Fin 43) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply', ih, finRotate_apply, Nat.cast_succ, add_assoc]

lemma tick_iter (k : ℕ) (x : Grid) : gridTick^[k] x = (x.1, (finRotate 43)^[k] x.2) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ_apply', ih, iterate_succ_apply']; rfl

/-! ## 1. Classification of tick-invariant masses -/

theorem tick_invariant_iff (μ : Mass) : TickInvariant μ ↔ ∀ d t, μ (d, t) = μ (d, 0) := by
  constructor
  · intro h d t
    have hit : ∀ k : ℕ, μ (gridTick^[k] (d, 0)) = μ (d, 0) := by
      intro k; induction k with
      | zero => rfl
      | succ k ih => rw [iterate_succ_apply', h, ih]
    have := hit t.val
    rwa [tick_iter, rot_add, Fin.cast_val_eq_self, zero_add] at this
  · intro h x
    obtain ⟨d, t⟩ := x
    show μ (d, finRotate 43 t) = μ (d, t)
    rw [h, h d t]

/-- The invariant masses with direction weights `w`. -/
def dirMass (w : Fin 4 → ℝ) : Mass := fun x => w x.1 / 43

theorem dirMass_invariant (w : Fin 4 → ℝ) : TickInvariant (dirMass w) := fun _ => rfl

theorem dirMass_normalized (w : Fin 4 → ℝ) (hw : ∀ d, 0 ≤ w d) (hs : ∑ d, w d = 1) :
    Normalized (dirMass w) := by
  refine ⟨fun x => div_nonneg (hw _) (by norm_num), ?_⟩
  simp only [dirMass, Fintype.sum_prod_type, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [← hs]; refine Finset.sum_congr rfl fun d _ => ?_
  push_cast; field_simp


lemma sum_grid (μ : Mass) : ∑ x, μ x = ∑ d, ∑ t, μ (d, t) := Fintype.sum_prod_type _

/-- Classification: every tick-invariant normalized mass is `dirMass w` for a probability
vector `w` on the four directions. Nothing fixes `w`. -/
theorem invariant_classification (μ : Mass) (hi : TickInvariant μ) (hn : Normalized μ) :
    ∃ w : Fin 4 → ℝ, (∀ d, 0 ≤ w d) ∧ ∑ d, w d = 1 ∧ μ = dirMass w := by
  have hc := (tick_invariant_iff μ).mp hi
  refine ⟨fun d => 43 * μ (d, 0), fun d => by have := hn.1 (d, 0); positivity, ?_, ?_⟩
  · have h := hn.2
    rw [sum_grid] at h
    simp_rw [hc, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    simpa using h
  · funext x; obtain ⟨d, t⟩ := x; simp [dirMass, hc d t]

/-- An excluded cell has mass `1 − μ c`. -/
def excluded (μ : Mass) (c : Grid) : ℝ := ∑ x ∈ univ.erase c, μ x

theorem excluded_eq (μ : Mass) (hn : Normalized μ) (c : Grid) : excluded μ c = 1 - μ c := by
  rw [excluded, Finset.sum_erase_eq_sub (mem_univ c), hn.2]

/-- Countermodel: all mass on one direction row. -/
def rowW : Fin 4 → ℝ := fun d => if d = 0 then 1 else 0

theorem rowW_prob : (∀ d, 0 ≤ rowW d) ∧ ∑ d, rowW d = 1 := by
  refine ⟨fun d => by unfold rowW; split_ifs <;> norm_num, ?_⟩
  simp [rowW]

theorem row_excluded :
    excluded (dirMass rowW) (0, 0) = 42/43 ∧ excluded (dirMass rowW) (1, 0) = 1 := by
  have hn := dirMass_normalized rowW rowW_prob.1 rowW_prob.2
  rw [excluded_eq _ hn, excluded_eq _ hn]
  simp [dirMass, rowW]; norm_num

/-! ## 2. Uniformity needs an added direction symmetry -/

def dirTick (x : Grid) : Grid := (finRotate 4 x.1, x.2)

lemma rot4_to : ∀ d : Fin 4, (finRotate 4)^[d.val] 0 = d := by decide +kernel

/-- **Conditional.** Tick invariance plus invariance under a transitive direction relabeling
gives the uniform mass. The second hypothesis is not supplied by the existing modules. -/
theorem uniform_of_dir_invariant (μ : Mass) (hi : TickInvariant μ) (hd : ∀ x, μ (dirTick x) = μ x)
    (hs : ∑ x, μ x = 1) (x : Grid) : μ x = 1/172 := by
  have hc := (tick_invariant_iff μ).mp hi
  have hdir : ∀ d, μ (d, 0) = μ (0, 0) := by
    have hit : ∀ k : ℕ, μ ((finRotate 4)^[k] 0, 0) = μ (0, 0) := by
      intro k; induction k with
      | zero => rfl
      | succ k ih => rw [iterate_succ_apply']; exact (hd ((finRotate 4)^[k] 0, 0)).trans ih
    intro d; simpa [rot4_to] using hit d.val
  have hall : ∀ y : Grid, μ y = μ (0, 0) := fun y => (hc y.1 y.2).trans (hdir y.1)
  rw [sum_grid] at hs
  simp_rw [hall, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  push_cast at hs
  rw [hall x]; linarith

theorem uniform_excluded (c : Grid) : excluded (fun _ => 1/172) c = 171/172 := by
  rw [excluded_eq]
  · norm_num
  · exact ⟨fun _ => by norm_num, by simp [Grid]⟩

/-- The derived `D₄` sector basis: Gram-preserving relabelings of the four basis directions
fix the central node, so they are not transitive. -/
theorem d4_relabel_fixes_center : ∀ σ : Equiv.Perm (Fin 4),
    (∀ i j, PMSubstrate.Sectors.cD4 (σ i) (σ j) = PMSubstrate.Sectors.cD4 i j) → σ 1 = 1 := by
  decide +kernel

def centerW : Fin 4 → ℝ := fun d => if d = 1 then 1 else 0

theorem centerW_symmetric (σ : Equiv.Perm (Fin 4))
    (hσ : ∀ i j, PMSubstrate.Sectors.cD4 (σ i) (σ j) = PMSubstrate.Sectors.cD4 i j) (d : Fin 4) :
    centerW (σ d) = centerW d := by
  have h1 := d4_relabel_fixes_center σ hσ
  have : σ d = 1 ↔ d = 1 := by
    constructor
    · intro h; exact σ.injective (h.trans h1.symm)
    · rintro rfl; exact h1
  unfold centerW; simp only [this]

theorem center_excluded :
    excluded (dirMass centerW) (1, 0) = 42/43 ∧ excluded (dirMass centerW) (0, 0) = 1 := by
  have hn : Normalized (dirMass centerW) := dirMass_normalized centerW
    (fun d => by unfold centerW; split_ifs <;> norm_num) (by simp [centerW])
  rw [excluded_eq _ hn, excluded_eq _ hn]
  simp [dirMass, centerW]; norm_num

/-! ## 3. One deterministic trajectory versus the stationary ensemble -/

lemma orbit_reindex (o : Grid) (f : Grid → ℝ) :
    ∑ k : Fin 43, f (gridTick^[k.val] o) = ∑ t, f (o.1, t) := by
  simp_rw [tick_iter, rot_add, Fin.cast_val_eq_self]
  exact Fintype.sum_equiv (Equiv.addLeft o.2) _ _ (fun _ => rfl)

/-- Visits of cell `c` in one period of the reference started at `o`. -/
def hits (o c : Grid) : ℝ := ∑ k : Fin 43, if gridTick^[k.val] o = c then 1 else 0

theorem hits_eq (o c : Grid) : hits o c = if c.1 = o.1 then 1 else 0 := by
  unfold hits
  rw [orbit_reindex o (fun y => if y = c then 1 else 0)]
  obtain ⟨d, s⟩ := c
  by_cases h : d = o.1
  · subst h; simp
  · rw [ite_eq_right h]
    exact Finset.sum_eq_zero fun t _ => by
      rw [ite_eq_right]; intro he; exact h (congrArg Prod.fst he).symm

/-- Time-averaged availability along one trajectory: `42/43` or `1`, never `171/172`. -/
theorem trajectory_availability (o c : Grid) :
    1 - hits o c / 43 = if c.1 = o.1 then 42/43 else 1 := by
  rw [hits_eq]; split_ifs <;> norm_num

theorem trajectory_ne (o c : Grid) : 1 - hits o c / 43 ≠ 171/172 := by
  rw [trajectory_availability]; split_ifs <;> norm_num

/-- `171/172` is the uniform mixture over the four ergodic rows. -/
theorem direction_average (t : Fin 43) (c : Grid) :
    (∑ d : Fin 4, (1 - hits (d, t) c / 43)) / 4 = 171/172 := by
  simp_rw [hits_eq]
  obtain ⟨e, s⟩ := c
  fin_cases e <;> simp [Fin.sum_univ_four] <;> norm_num

/-! ## 4. Event semantics -/

/-- Collision semantics (an added premise): channel `j` with fixed target cell is
suppressed when the moving reference occupies that cell. The per-channel rate is `0`
or `1/43`, never `1/172`. -/
theorem collision_channel_rate (o c : Grid) : hits o c / 43 ≠ 1/172 := by
  rw [hits_eq]; split_ifs <;> norm_num

/-- The aggregate payload deficit equals `16/172` iff exactly four of the sixteen channel
targets lie in the reference's direction row. -/
theorem collision_aggregate (o : Grid) (tgt : Fin 16 → Grid) :
    (∑ j, hits o (tgt j)) / 43 = 16/172 ↔
      (univ.filter (fun j => (tgt j).1 = o.1)).card = 4 := by
  simp_rw [hits_eq]
  rw [← Finset.sum_filter, sum_const, nsmul_eq_mul, mul_one]
  constructor
  · intro h
    have : ((univ.filter (fun j => (tgt j).1 = o.1)).card : ℝ) = 4 := by linarith
    exact_mod_cast this
  · intro h; rw [h]; norm_num

/-! A full-alphabet code with one reserved cell (a checksum) in which a payload write is
never suppressed: it changes its own cell and the reserved cell. -/

section Checksum
variable {a : ℕ} [NeZero a] (ha : 172 ≤ a)

def label : Grid → Fin a :=
  fun x => Fin.castLE (by norm_num; omega) (finProdFinEquiv x)

omit [NeZero a] in
lemma label_injective : Injective (label ha) :=
  (Fin.castLE_injective _).comp finProdFinEquiv.injective

lemma card_others (o : Grid) : Fintype.card {c : Grid // c ≠ o} = 171 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]; simp [Grid]

def place (o : Grid) : {c : Grid // c ≠ o} ≃ Fin 171 :=
  Fintype.equivFinOfCardEq (card_others o)

def payloadSum (o : Grid) (p : Fin 171 → Fin a) : Fin a :=
  ∑ c : {c : Grid // c ≠ o}, p (place o c)

def csEnc (op : Grid × (Fin 171 → Fin a)) : Grid → Fin a := fun c =>
  if h : c = op.1 then label ha op.1 - payloadSum op.1 op.2 else op.2 (place op.1 ⟨c, h⟩)

lemma csEnc_sum (op : Grid × (Fin 171 → Fin a)) : ∑ c, csEnc ha op c = label ha op.1 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ op.1]
  simp only [csEnc]
  have : ∑ c : {c : Grid // c ≠ op.1}, (if h : c.1 = op.1 then label ha op.1 -
      payloadSum op.1 op.2 else op.2 (place op.1 ⟨c.1, h⟩)) = payloadSum op.1 op.2 := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [dite_eq_right c.2]
  rw [this]
  exact sub_add_cancel _ _

theorem csEnc_injective : Injective (csEnc ha) := by
  rintro ⟨o, p⟩ ⟨o', p'⟩ h
  have ho : o = o' := label_injective ha (by
    have := congrArg (fun w => ∑ c, w c) h
    simpa only [csEnc_sum] using this)
  subst ho
  refine Prod.ext rfl (funext fun j => ?_)
  have hj := congrFun h ((place o).symm j).1
  simp only [csEnc, dite_eq_right ((place o).symm j).2, Subtype.coe_eta, Equiv.apply_symm_apply] at hj
  exact hj

lemma payloadSum_eq (o : Grid) (p : Fin 171 → Fin a) : payloadSum o p = ∑ i, p i :=
  Fintype.sum_equiv (place o) _ _ (fun _ => rfl)

/-- A one-register payload write changes exactly its own cell and the reserved cell. -/
theorem csEnc_write (o : Grid) (p p' : Fin 171 → Fin a) (j : Fin 171)
    (hrest : ∀ i, i ≠ j → p i = p' i) :
    (∀ c, c ≠ o → c ≠ ((place o).symm j).1 → csEnc ha (o, p) c = csEnc ha (o, p') c) ∧
      (p j ≠ p' j → csEnc ha (o, p) o ≠ csEnc ha (o, p') o) := by
  constructor
  · intro c hco hcj
    simp only [csEnc, dite_eq_right hco]
    apply hrest
    intro he; apply hcj
    rw [← he]; simp
  · intro hne heq
    simp only [csEnc, payloadSum_eq] at heq
    have hs : ∑ i, p i = ∑ i, p' i := by
      have := congrArg (fun z => label ha o - z) heq; simpa using this
    rw [Fintype.sum_eq_add_sum_subtype_ne _ j, Fintype.sum_eq_add_sum_subtype_ne _ j] at hs
    have hr : ∑ i : {i : Fin 171 // i ≠ j}, p i = ∑ i : {i : Fin 171 // i ≠ j}, p' i :=
      Finset.sum_congr rfl fun i _ => hrest i i.2
    rw [hr] at hs
    exact hne (add_right_cancel hs)

/-- A nontrivial write changes the payload cell itself as well as the checksum.
Interpreting each changed cell as a primitive transition is a further cost model. -/
theorem csEnc_write_exact (o : Grid) (p p' : Fin 171 → Fin a) (j : Fin 171)
    (hrest : ∀ i, i ≠ j → p i = p' i) (hne : p j ≠ p' j) (c : Grid) :
    csEnc ha (o, p) c ≠ csEnc ha (o, p') c ↔
      c = o ∨ c = ((place o).symm j).1 := by
  have hw := csEnc_write ha o p p' j hrest
  constructor
  · intro hc
    by_contra h
    push Not at h
    exact hc (hw.1 c h.1 h.2)
  · rintro (rfl | rfl)
    · exact hw.2 hne
    · simpa only [csEnc, dite_eq_right ((place o).symm j).2, Subtype.coe_eta,
        Equiv.apply_symm_apply] using hne

lemma update_sum (w : Grid → Fin a) : ∑ c, gridUpdate w c = ∑ c, w c :=
  Fintype.sum_equiv ((Equiv.refl _).prodCongr (finRotate 43).symm) _ _ (fun _ => rfl)

/-- The checksum code is not tick-equivariant (the sum is tick-invariant, the label is not). -/
theorem csEnc_not_equivariant (o : Grid) (p : Fin 171 → Fin a) :
    gridUpdate (csEnc ha (o, p)) ≠ csEnc ha (gridTick o, p) := by
  intro h
  have := congrArg (fun w => ∑ c, w c) h
  simp only [update_sum, csEnc_sum] at this
  exact gridTick_moves o (label_injective ha this).symm

end Checksum

end PMConstants.AvailabilityAudit
