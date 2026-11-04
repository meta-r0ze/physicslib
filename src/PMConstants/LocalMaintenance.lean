import PMSubstrate.Distinctions
import PMSubstrate.NetCost
import PMSubstrate.Lattices
import Mathlib.Tactic

/-!
# A concrete local conservative transition and its measured cost

On two binary sites, a reversible population-preserving update is identity or
swap. Thus nontriviality selects swap within this explicitly stated local model.
The sites are embedded as actual E8 nearest neighbours. This does not derive
the binary state model, its occupation statistics, or a global vacuum update.

Paper I's ordered boundary count is twice the activation indicator of the
single undirected swap event. Its expected primitive cost is then computed with
NetCost, with no fitted coefficient. Symmetric invariant ensembles with the
same one-site marginals can still have different activation frequencies.
-/
noncomputable section
namespace PMConstants.LocalMaintenance
open Finset Matrix

abbrev State := Bool × Bool

def population (s : State) : ℕ := s.1.toNat+s.2.toNat

def swap : Equiv.Perm State := Equiv.prodComm Bool Bool

/-- The local update menu is classified, not chosen to match a workload. -/
theorem conservative_updates : ∀ e : Equiv.Perm State,
    (∀ s, population (e s) = population s) → e = Equiv.refl State ∨ e = swap := by
  decide +kernel

theorem nontrivial_conservative_update (e : Equiv.Perm State)
    (hc : ∀ s, population (e s) = population s) (hn : e ≠ Equiv.refl State) : e = swap :=
  (conservative_updates e hc).resolve_left hn

theorem swap_preserves_population (s : State) : population (swap s) = population s := by
  simp [population, swap, Nat.add_comm]

theorem swap_active_iff (s : State) : swap s ≠ s ↔ s.1 ≠ s.2 := by
  rcases s with ⟨a,b⟩
  cases a <;> cases b <;> decide

/-- An actual nearest-neighbour displacement in Paper I's integral E8 basis. -/
def rootStep : Fin 8 → ℤ := Pi.single 0 1

theorem step_is_root : rootStep ⬝ᵥ (PMSubstrate.Lattices.gram *ᵥ rootStep) = 2 := by decide +kernel

def site (b : Bool) : Fin 8 → ℤ := if b then rootStep else 0

theorem sites_distinct : Function.Injective site := by decide +kernel

theorem sites_are_neighbours :
    (site true-site false) ⬝ᵥ (PMSubstrate.Lattices.gram *ᵥ (site true-site false)) = 2 := by
  simpa [site] using step_is_root

def config (s : State) (b : Bool) : Bool := if b then s.2 else s.1

/-- Unit toll for one undirected primitive transition, when the swap is active. -/
def activeCost (s : State) : ℝ := if s.1 = s.2 then 0 else 1

/-- Paper I counts ordered neighbour pairs, so each cut edge occurs twice. -/
theorem boundary_count (s : State) :
    (PMSubstrate.Distinctions.distinctions (⊤ : SimpleGraph Bool) (config s)).card =
      if s.1 = s.2 then 0 else 2 := by
  rcases s with ⟨a,b⟩
  cases a <;> cases b <;> decide +kernel

theorem boundary_cost (s : State) :
    PMSubstrate.Distinctions.localCost (⊤ : SimpleGraph Bool) (fun _ => 0)
      (fun a b => if a = b then 0 else 1) (config s) = 2*activeCost s := by
  rw [PMSubstrate.Distinctions.only_distinctions_cost]
  · rw [boundary_count]
    rcases s with ⟨a,b⟩
    cases a <;> cases b <;> norm_num [activeCost]
  · rfl
  · rfl
  · intro a; rfl
  · intro a b; cases a <;> cases b <;> rfl

/-- A finite sample of local configurations specifies an event law; geometry
and the update classification alone do not supply this sample. -/
def event (sample : Bool → State) : Finset Bool :=
  univ.filter fun w => (sample w).1 ≠ (sample w).2

def expectedPrimitiveCost (sample : Bool → State) : ℝ :=
  PMSubstrate.NetCost.expectedCost 1 (fun _ : Fin 1 => event sample)

theorem event_cost (sample : Bool → State) :
    expectedPrimitiveCost sample = PMSubstrate.NetCost.prob (event sample) := by
  rw [expectedPrimitiveCost, PMSubstrate.NetCost.expected_count_linear]
  simp

def aligned (b : Bool) : State := (b,b)
def opposed (b : Bool) : State := (b,!b)

/-- Both equally weighted samples have the same one-site marginals. -/
theorem same_marginals : ∀ i : Bool,
    (univ.filter (fun b => config (aligned b) i = true)).card = 1 ∧
    (univ.filter (fun b => config (opposed b) i = true)).card = 1 := by decide +kernel

/-- Both ensembles are invariant under the local dynamics (identity sample
reindexing for aligned states, a bijective flip for opposed states). -/
theorem aligned_invariant (b : Bool) : swap (aligned b) = aligned b := rfl

theorem opposed_invariant (b : Bool) : swap (opposed b) = opposed (!b) := by
  cases b <;> rfl

/-- Both samples also respect simultaneous relabeling of the two state names. -/
theorem relabel_invariant (b : Bool) :
    ((!((aligned b).1),!((aligned b).2)) = aligned (!b)) ∧
    ((!((opposed b).1),!((opposed b).2)) = opposed (!b)) := by
  cases b <;> decide

/-- Same geometry, conservative primitive and marginal occupations; distinct
correlations give distinct expected transition costs. -/
theorem different_costs : expectedPrimitiveCost aligned = 0 ∧ expectedPrimitiveCost opposed = 1 := by
  rw [event_cost, event_cost]
  have ha : (event aligned).card = 0 := by decide +kernel
  have ho : (event opposed).card = 2 := by decide +kernel
  simp [PMSubstrate.NetCost.prob, ha, ho]

/-! The ambiguity need not be attributed to different total particle counts.
Two pairs suffice to fix the total population while retaining correlation freedom.
The update menu here is the two pairwise swaps; a full E8 dynamics is not assumed. -/
abbrev FourState := State × State

def alignedFour (b : Bool × Bool) : FourState := (aligned b.1, aligned (!b.1))
def opposedFour (b : Bool × Bool) : FourState := (opposed b.1, opposed b.2)

def firstSwap (s : FourState) : FourState := (swap s.1,s.2)
def secondSwap (s : FourState) : FourState := (s.1,swap s.2)

theorem fixed_population : ∀ b,
    population (alignedFour b).1 + population (alignedFour b).2 = 2 ∧
    population (opposedFour b).1 + population (opposedFour b).2 = 2 := by decide +kernel

/-- Reindexing the equally weighted finite samples proves invariance under
both allowed primitives. All four reindexings below are bijections. -/
theorem four_invariant (b : Bool × Bool) :
    firstSwap (alignedFour b) = alignedFour b ∧
    secondSwap (alignedFour b) = alignedFour b ∧
    firstSwap (opposedFour b) = opposedFour (!b.1,b.2) ∧
    secondSwap (opposedFour b) = opposedFour (b.1,!b.2) := by
  rcases b with ⟨b,c⟩
  cases b <;> cases c <;> decide

def fourConfig (s : FourState) (i : Bool × Bool) : Bool :=
  config (if i.1 then s.2 else s.1) i.2

theorem four_same_marginals : ∀ i : Bool × Bool,
    (univ.filter (fun b => fourConfig (alignedFour b) i = true)).card = 2 ∧
    (univ.filter (fun b => fourConfig (opposedFour b) i = true)).card = 2 := by decide +kernel

/-- Total pair-activation events at a unit toll. -/
def fourExpectedCost (sample : (Bool × Bool) → FourState) : ℝ :=
  PMSubstrate.NetCost.expectedCost 1 (fun i : Fin 2 =>
    univ.filter fun b => if i = 0 then (sample b).1.1 ≠ (sample b).1.2
      else (sample b).2.1 ≠ (sample b).2.2)

theorem fixed_population_different_costs :
    fourExpectedCost alignedFour = 0 ∧ fourExpectedCost opposedFour = 2 := by
  have ha : ∀ i : Fin 2,
      (univ.filter fun b => if i = 0 then (alignedFour b).1.1 ≠ (alignedFour b).1.2
        else (alignedFour b).2.1 ≠ (alignedFour b).2.2).card = 0 := by decide +kernel
  have ho : ∀ i : Fin 2,
      (univ.filter fun b => if i = 0 then (opposedFour b).1.1 ≠ (opposedFour b).1.2
        else (opposedFour b).2.1 ≠ (opposedFour b).2.2).card = 4 := by decide +kernel
  simp only [fourExpectedCost, PMSubstrate.NetCost.expected_count_linear, PMSubstrate.NetCost.prob,
    ha, ho, Nat.cast_zero, Fintype.card_prod, Fintype.card_bool, one_mul]
  norm_num

end PMConstants.LocalMaintenance
