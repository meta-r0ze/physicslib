import PMSubstrate.Impedance

/-!
# Occupancy cost

This is the only mass reading in the tree.

A footprint gives the room a persistent configuration holds in one clock
period. Each pillar has a count and a fixed baseline price. The residual
holds the terms that still need a count and a price.

The old ledgers can give signed or fractional counts in the baseline units.
These counts record the old values. A physical footprint needs a separate
proof of its counts. The electron unit is a premise.
-/

noncomputable section

namespace PMSubstrate.OccupancyCost

/-- Signed counts in the baseline price units. -/
structure Footprint where
  capacity : ℝ := 0
  map : ℝ := 0
  protocol : ℝ := 0
  governor : ℝ := 0
  toll : ℝ := 0
  margin : ℝ := 0
  residual : ℝ := 0

/-- Add the six priced counts and the residual. -/
def cost (f : Footprint) : ℝ :=
  f.capacity * capacityTerm baseline + f.map * mapTerm baseline +
    f.protocol * protocolTerm baseline + f.governor * governorTerm baseline +
    f.toll * tollTerm baseline + f.margin * marginTerm baseline + f.residual

/-- Named normalization premise for the physical electron footprint. -/
def ElectronUnit (electron : Footprint) : Prop := cost electron = 1

/-- Full cells hold one unit of each pillar per cell. -/
def cells (n residual : ℝ) : Footprint :=
  ⟨n, n, n, n, n, n, residual⟩

def oneCell : Footprint := cells 1 0

theorem cost_cells (n residual : ℝ) : cost (cells n residual) = n * impedance baseline + residual := by
  unfold cost cells impedance
  simp only
  ring

theorem cost_oneCell : cost oneCell = impedance baseline := by
  simp [oneCell, cost_cells]

theorem cost_oneCell_eq_inverse_coupling : cost oneCell = causalCoupling⁻¹ := by
  rw [cost_oneCell, causalCoupling, one_div, inv_inv]
  rfl

/-- Combine two disjoint accounts. Each resource must occur in one account. -/
def Footprint.add (a b : Footprint) : Footprint :=
  ⟨a.capacity + b.capacity, a.map + b.map, a.protocol + b.protocol, a.governor + b.governor,
    a.toll + b.toll, a.margin + b.margin, a.residual + b.residual⟩

@[simp] theorem cost_add (a b : Footprint) : cost (a.add b) = cost a + cost b := by
  unfold cost Footprint.add
  simp only
  ring

/-- Multiply a footprint by its ledger multiplicity. -/
def Footprint.scale (n : ℝ) (f : Footprint) : Footprint :=
  ⟨n * f.capacity, n * f.map, n * f.protocol, n * f.governor,
    n * f.toll, n * f.margin, n * f.residual⟩

@[simp] theorem cost_scale (n : ℝ) (f : Footprint) : cost (f.scale n) = n * cost f := by
  unfold cost Footprint.scale
  simp only
  ring

/-- Combine the footprints of all levels. A binding correction has a signed footprint. -/
def tower (levels : List Footprint) : Footprint := levels.foldr Footprint.add {}

theorem cost_tower (levels : List Footprint) :
    cost (tower levels) = (levels.map cost).sum := by
  induction levels with
  | nil => simp [tower, cost]
  | cons f fs ih => simpa only [tower, List.foldr_cons, List.map_cons, List.sum_cons, cost_add]
      using congrArg (cost f + ·) ih

/-- Normalize a Capacity amount in the baseline price units. -/
def capacityCount (amount : ℝ) : ℝ := amount / capacityTerm baseline

/-- Normalize a Map amount in the baseline price units. -/
def mapCount (amount : ℝ) : ℝ := amount / mapTerm baseline

/-- Normalize a Protocol amount in the baseline price units. -/
def protocolCount (amount : ℝ) : ℝ := amount / protocolTerm baseline

/-- Normalize a Toll amount in the baseline price units. -/
def tollCount (amount : ℝ) : ℝ := amount / tollTerm baseline

/-- Normalize a Margin amount in the baseline price units. -/
def marginCount (amount : ℝ) : ℝ := amount / marginTerm baseline

@[simp] theorem capacityCount_price (amount : ℝ) :
    capacityCount amount * capacityTerm baseline = amount := by
  have h : capacityTerm baseline ≠ 0 := by unfold capacityTerm; positivity
  exact div_mul_cancel₀ _ h

@[simp] theorem mapCount_price (amount : ℝ) :
    mapCount amount * mapTerm baseline = amount :=
  div_mul_cancel₀ _ (by norm_num [mapTerm, baseline])

@[simp] theorem protocolCount_price (amount : ℝ) :
    protocolCount amount * protocolTerm baseline = amount :=
  div_mul_cancel₀ _ (by norm_num [protocolTerm, baseline, Parameters.resolution])

@[simp] theorem tollCount_price (amount : ℝ) :
    tollCount amount * tollTerm baseline = amount :=
  div_mul_cancel₀ _ (by norm_num [tollTerm, baseline, Parameters.nodeCapacity, Parameters.resolution])

@[simp] theorem marginCount_price (amount : ℝ) :
    marginCount amount * marginTerm baseline = amount :=
  div_mul_cancel₀ _ (by
    norm_num [marginTerm, baseline, Parameters.embeddingLoad, Parameters.intrinsicLoad])

end PMSubstrate.OccupancyCost
