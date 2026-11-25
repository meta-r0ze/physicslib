import PMSubstrate.Impedance
import Mathlib.Analysis.Real.Cardinality

/-!
# Occupancy cost

This is the only mass reading in the tree.

A footprint counts the clock events and full cells a configuration holds in
one period. Each event has unit price. Each full cell has the baseline
impedance price. Extra pillar charges have signed whole counts.

The residual records charges without a whole count. Fix the residual before
testing the cost. A free residual can make the cost equal any real value.
-/

noncomputable section

namespace PMSubstrate.OccupancyCost

/-- Whole event and cell counts with signed extra pillar charges. -/
structure Footprint where
  events : ℕ := 0
  cells : ℕ := 0
  capacity : ℤ := 0
  map : ℤ := 0
  protocol : ℤ := 0
  governor : ℤ := 0
  toll : ℤ := 0
  margin : ℤ := 0
  residual : ℝ := 0

/-- Price the event and cell counts, then add the extra charges and residual. -/
def cost (f : Footprint) : ℝ :=
  (f.events : ℝ) + (f.cells : ℝ) * impedance baseline +
    (f.capacity : ℝ) * capacityTerm baseline + (f.map : ℝ) * mapTerm baseline +
    (f.protocol : ℝ) * protocolTerm baseline + (f.governor : ℝ) * governorTerm baseline +
    (f.toll : ℝ) * tollTerm baseline + (f.margin : ℝ) * marginTerm baseline + f.residual

theorem cost_oneEvent : cost { events := 1 } = 1 := by simp [cost]

/-- An account with full cells and a residual. -/
def cells (n : ℕ) (residual : ℝ) : Footprint :=
  { cells := n, residual := residual }

def oneCell : Footprint := cells 1 0

theorem cost_cells (n : ℕ) (residual : ℝ) :
    cost (cells n residual) = (n : ℝ) * impedance baseline + residual := by
  simp [cost, cells]

theorem cost_oneCell : cost oneCell = impedance baseline := by
  simp [oneCell, cost_cells]

theorem cost_oneCell_eq_inverse_coupling : cost oneCell = causalCoupling⁻¹ := by
  rw [cost_oneCell, causalCoupling, one_div, inv_inv]
  rfl

/-- Combine two disjoint accounts. Each resource must occur in one account. -/
def Footprint.add (a b : Footprint) : Footprint :=
  ⟨a.events + b.events, a.cells + b.cells, a.capacity + b.capacity,
    a.map + b.map, a.protocol + b.protocol, a.governor + b.governor,
    a.toll + b.toll, a.margin + b.margin, a.residual + b.residual⟩

@[simp] theorem cost_add (a b : Footprint) : cost (a.add b) = cost a + cost b := by
  simp only [cost, Footprint.add, Nat.cast_add, Int.cast_add]
  ring

/-- Multiply a footprint by a whole number of copies. -/
def Footprint.scale (n : ℕ) (f : Footprint) : Footprint :=
  ⟨n * f.events, n * f.cells, n * f.capacity, n * f.map, n * f.protocol,
    n * f.governor, n * f.toll, n * f.margin, n * f.residual⟩

@[simp] theorem cost_scale (n : ℕ) (f : Footprint) :
    cost (f.scale n) = (n : ℝ) * cost f := by
  simp only [cost, Footprint.scale, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
  ring

/-- Combine the footprints of all levels. -/
def tower (levels : List Footprint) : Footprint := levels.foldr Footprint.add {}

theorem cost_tower (levels : List Footprint) :
    cost (tower levels) = (levels.map cost).sum := by
  induction levels with
  | nil => simp [tower, cost]
  | cons f fs ih => simpa only [tower, List.foldr_cons, List.map_cons, List.sum_cons, cost_add]
      using congrArg (cost f + ·) ih

/-- A fixed residual permits only countably many costs. -/
theorem countable_costs_at_residual (r : ℝ) :
    {x : ℝ | ∃ f : Footprint, f.residual = r ∧ cost f = x}.Countable := by
  let read : ℕ × ℕ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ → ℝ :=
    fun ⟨e, c, cap, m, p, g, t, d⟩ => cost ⟨e, c, cap, m, p, g, t, d, r⟩
  apply (Set.countable_range read).mono
  rintro x ⟨⟨e, c, cap, m, p, g, t, d, _⟩, rfl, rfl⟩
  exact ⟨⟨e, c, cap, m, p, g, t, d⟩, rfl⟩

/-- Some real values cannot be produced when the residual is fixed. -/
theorem exists_not_cost_at_residual (r : ℝ) :
    ∃ x : ℝ, ¬ ∃ f : Footprint, f.residual = r ∧ cost f = x := by
  by_contra! h
  apply Set.not_countable_univ (α := ℝ)
  exact (countable_costs_at_residual r).mono (fun x _ => h x)

end PMSubstrate.OccupancyCost
