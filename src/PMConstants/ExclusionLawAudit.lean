import PMConstants.General.ReferenceCapacity
import PMSubstrate.FinalPremises
import PMSubstrate.Distinctions
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-!
# Exact-update omission and conditional relational-load contracts

Integrated from Claude's exclusion-law audit. Load arithmetic and constant
backlog do not by themselves prove a conservative physical operation model.

1. Skipping a job inside a reversible cycle preserves every outcome iff the job is the identity.
2. Paper I's channel fields are each required (`description_minimal`): dropping one erases a
   distinction.
3. Relational (star) maintenance from a reference has no self-edge: 171 jobs on 172 cells.
4. Supplied intensive and extensive load definitions give different totals.
-/

noncomputable section
namespace PMConstants.ExclusionLawAudit
open Finset Function PMConstants.General.ReferenceCapacity

/-! ## 1. Omission preserves the exact all-state update only for null jobs -/

theorem skip_preserves_iff_null {S : Type*} (A B g : S → S) (hA : Injective A)
    (hB : Surjective B) : (A ∘ g ∘ B = A ∘ B) ↔ g = id := by
  constructor
  · intro h; funext s
    obtain ⟨t, rfl⟩ := hB s
    exact hA (congrFun h t)
  · rintro rfl; rfl

/-- A nonidentity reversible update can preserve every distinction. Thus the
exact-outcome omission criterion must not be read as a uniqueness-of-persistence
or information-loss theorem. -/
theorem nonnull_reversible_job :
    ∃ g : Bool → Bool, Injective g ∧ g ≠ id := by
  exact ⟨fun b => !b, by decide +kernel, by decide +kernel⟩

/-! ## 2. The sixteen channel fields of Paper I's description are each required -/

theorem channel_field_required (j : Fin 16) :
    ¬ Injective (fun (x : Fin 16 → Bool) (i : {i : Fin 16 // i ≠ j}) => x i) := by
  intro h
  have := (PMSubstrate.FinalPremises.description_minimal (F := fun _ : Fin 16 => Bool)
    {i | i ≠ j}).mp h j
  exact this rfl

/-! ## 3. Relational maintenance from a reference: the star has no self-edge -/

def star (o : Grid) : SimpleGraph Grid := SimpleGraph.fromRel fun x _ => x = o

theorem star_adj (o x : Grid) : (star o).Adj o x ↔ x ≠ o := by
  simp [star, SimpleGraph.fromRel_adj, ne_comm]

instance (o : Grid) : DecidableRel (star o).Adj := fun x y => by
  unfold star; rw [SimpleGraph.fromRel_adj]; infer_instance

theorem star_degree (o : Grid) : (star o).degree o = 171 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have : (star o).neighborFinset o = univ.erase o := by
    ext x; simp [star_adj]
  rw [this, card_erase_of_mem (mem_univ _)]; simp [Grid]

/-- Relational jobs: one maintenance edge from the reference to each other cell. -/
def relJob (o x : Grid) : ℝ := if (star o).Adj o x then 1 else 0

theorem relJob_self (o : Grid) : relJob o o = 0 := by simp [relJob]

/-! ## 4. Two supplied load contracts with different totals -/

/-- **Intensive contract.** Load is a per-cell density fixed by the substrate: direction row
totals `L d` per phase spread uniformly over its 43 phases (the tick-invariant form), and each
cell's load is maintained along its relational edge. -/
def intensiveRequired (L : Fin 4 → ℝ) (o : Grid) : ℝ := ∑ x : Grid, relJob o x * (L x.1 / 43)

theorem intensive_required_balanced (L : Fin 4 → ℝ) (hL : ∀ d, L d = 4) (o : Grid) :
    intensiveRequired L o = 16 * (171/172) := by
  unfold intensiveRequired
  have h : ∀ x : Grid, relJob o x * (L x.1 / 43) = (if x = o then 0 else 4/43) := by
    intro x; unfold relJob; rw [hL]
    by_cases hx : x = o
    · subst hx; simp
    · simp [star_adj, hx]
  simp_rw [h]
  rw [Finset.sum_ite, sum_const_zero, zero_add, sum_const]
  have : (univ.filter (fun x : Grid => ¬ x = o)).card = 171 := by
    rw [Finset.filter_ne' univ o]; rw [card_erase_of_mem (mem_univ _)]; simp [Grid]
  rw [this]; norm_num

/-- **Extensive contract.** The sixteen channel fields are the required work (a workload contract,
not a consequence of description injectivity). Relational maintenance moves load onto the 171 edges but conserves it. -/
def extensiveRequired (o : Grid) : ℝ := ∑ x : Grid, relJob o x * (16 / 171)

theorem extensive_required (o : Grid) : extensiveRequired o = 16 := by
  unfold extensiveRequired relJob
  simp_rw [star_adj]
  rw [← Finset.sum_mul]
  have : (∑ x : Grid, if x ≠ o then (1 : ℝ) else 0) = 171 := by
    rw [Finset.sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
    rw [Finset.filter_ne' univ o, card_erase_of_mem (mem_univ _)]; simp [Grid]
  rw [this]; norm_num

/-- The two load definitions give different numerical totals. Neither a state
encoding nor a physical conservation proof is part of this arithmetic claim. -/
theorem contracts_differ (o : Grid) :
    intensiveRequired (fun _ => 4) o ≠ extensiveRequired o := by
  rw [intensive_required_balanced _ (fun _ => rfl), extensive_required]; norm_num

theorem exact_service_persists (r : ℝ) (q : ℕ → ℝ) (q0 : ℝ) (hq0 : q 0 = q0)
    (hstep : ∀ n, q (n+1) = q n + r - r) : ∀ n, q n = q0 := by
  intro n; induction n with
  | zero => exact hq0
  | succ n ih => rw [hstep, ih]; ring

/-- Paper I's distinctions are differences of state values, not address labels.
A homogeneous configuration has zero state-distinction cost even on a star. -/
theorem homogeneous_distinction_cost (o : Grid) (b : Bool) :
    PMSubstrate.Distinctions.localCost (star o) (fun _ => 0)
      (fun a b => if a = b then 0 else 1) (fun _ => b) = 0 := by
  simp [PMSubstrate.Distinctions.localCost]

/-- Counting every nonself edge at fixed positive density is not automatically
Paper I's state-distinction cost: the two disagree on homogeneous states. -/
theorem edge_density_not_distinction_cost (o : Grid) (b : Bool) :
    PMSubstrate.Distinctions.localCost (star o) (fun _ => 0)
      (fun a b => if a = b then 0 else 1) (fun _ => b) ≠
        intensiveRequired (fun _ => 4) o := by
  rw [homogeneous_distinction_cost, intensive_required_balanced _ (fun _ => rfl)]
  norm_num

end PMConstants.ExclusionLawAudit
