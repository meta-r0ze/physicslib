import PMConstants.RootRepairRule
import PMConstants.ReflectionCharge

/-!
# Do the gauge, scalar and fermion sectors share one repair length?

`CommonResponse` prices every sector by one readout (`stateFlag`, `linkFlag`) at one toll; what
is left open is that the repair length `m` is the same in each sector. Across carrier types it is
not (`TypedRepairWork.common_repair_cannot_match`); `RootRepairRule` gives the typed lengths from
one root event per non-abelian factor, at least one for a gauge-charged object. This module asks
what the same rule says about the three sectors.

* `repairsOf`: the rule as a function of an object's colour and weak dimensions.
* `types_match`: on the fermion carrier types it is `RootRepairRule.repairs`.
* **Gauge.** A link holonomy lies in one factor (colour, weak or hypercharge), so its repair is one
  event (`gauge_link_one`: the adjoint of one factor, or a U(1) phase, gives `1`).
* **Scalar.** The scalar is a weak doublet and a colour singlet, so its repair is one event
  (`scalar_one`). So `scalar_matches_gauge`: the scalar and the gauge link share `m`, which is
  the premise `ScalarNormalization` uses for `m_W² = (3/344)·v_sub²`.
* **Fermion.** Fermion types differ (`Q` costs two). `fermion_absorbed`: a repair of `k·m` events
  on a fermion amplitude `ψ` costs the same as `m` events on `√k · ψ`, so a type-dependent count is
  a rescaling of that type's field and changes no gauge or scalar normalization. It moves only
  the field's normalization, which the Yukawa couplings absorb.

* `sector_least`: for any object displaced in the non-abelian factors it is charged under, and
  gauge-charged, the least repair has `repairsOf c w` events (`PMAction.FactorRepair`). So the
  gauge link's and the scalar's single event are Economy's minimum, not a reading.

Status: the sector sharing that the gauge and scalar normalizations need follows from the same
derivation as the typed repair lengths (`RootRepairRule`, `PMAction.FactorRepair`), with the same
premises: a disturbance displaces an object in the factors it is charged under, each undone by one
event; a phase-only displacement costs one event.
-/

noncomputable section
namespace PMConstants.SectorRepair
open RequirementTable PMAction CommonResponse

/-- **The rule** on an object with colour dimension `c` and weak dimension `w`: one event per
non-abelian factor it is charged under, at least one. -/
def repairsOf (c w : ℕ) : ℕ :=
  max 1 ((if 1 < c then 1 else 0) + (if 1 < w then 1 else 0))

/-- On the gauge-charged fermion types the rule is `RootRepairRule.repairs`. -/
theorem types_match (t : Ty) (ht : t ≠ .n) :
    RootRepairRule.repairs t = repairsOf (colourDim t) (isoDim t) := by
  cases t <;> first | rfl | exact absurd rfl ht

/-- **A gauge link is repaired by one event.** Its holonomy lies in one factor: the colour
adjoint (`8`, no weak index), the weak adjoint (`3`, no colour index) or a U(1) phase. -/
theorem gauge_link_one :
    repairsOf 8 1 = 1 ∧ repairsOf 1 3 = 1 ∧ repairsOf 1 1 = 1 := by decide

/-- **The scalar doublet is repaired by one event.** -/
theorem scalar_one : repairsOf 1 2 = 1 := by decide

/-- **Scalar and gauge share the repair length.** -/
theorem scalar_matches_gauge :
    repairsOf 1 2 = repairsOf 8 1 ∧ repairsOf 1 2 = repairsOf 1 3 := by decide

/-- **A fermion's repair count is a field rescaling.** `k·m` events on `ψ` cost what `m` events
cost on `√k · ψ`. -/
theorem fermion_absorbed {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (ψ : ι → ℂ) (toll : ℝ) (m k : ℕ) :
    responseCost toll (k * m) (stateFlag U ψ) =
      responseCost toll m (stateFlag U (((Real.sqrt k : ℝ) : ℂ) • ψ)) := by
  rw [ReflectionCharge.reflected_response U ψ k (Nat.cast_nonneg k)]
  unfold responseCost
  push_cast
  ring

/-- **The rule is Economy's minimum for any gauge-charged object.** -/
theorem sector_least {Gc Gw P : Type*} [Group Gc] [Group Gw] [CommGroup P]
    [DecidableEq Gc] [DecidableEq Gw] [DecidableEq P] (c w : ℕ) (g : Gc × Gw × P)
    (hc : g.1 ≠ 1 ↔ 1 < c) (hw : g.2.1 ≠ 1 ↔ 1 < w) (hch : 1 < c ∨ 1 < w ∨ g.2.2 ≠ 1) :
    IsLeast {n | ∃ L : List (Gc × Gw × P), (∀ e ∈ L, PMAction.FactorRepair.IsEvent e) ∧
      L.prod = g ∧ L.length = n} (repairsOf c w) := by
  have h : PMAction.FactorRepair.need g = repairsOf c w := by
    unfold PMAction.FactorRepair.need PMAction.FactorRepair.displaced repairsOf
    simp only [hc, hw]
    by_cases h1 : 1 < c <;> by_cases h2 : 1 < w <;> by_cases h3 : g.2.2 = 1 <;>
      simp [h1, h2, h3] at hch ⊢
  rw [← h]
  exact PMAction.FactorRepair.repair_least g

end PMConstants.SectorRepair
