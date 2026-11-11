import PMAtoms.NuclearShells
import PMAtoms.SingleParticle
import PMHadrons.MesonMasses
import Mathlib.Tactic

/-!
# The shell system as an E8 occupancy system

`SingleParticle` records the standard `nlj` orbital sequence with schematic level
energies. This module lays the E8 foundation the shell level needs, separating what
is **derived** from what is still a model input.

**Derived here**

* each orbital's capacity is `2j+1 = j2+1` (spin degeneracy only);
* the shell order is the oscillator order `2n+l` — the Capacity count — nondecreasing;
* the E8 closure ladder is exactly the cumulative occupation of that order, and the
  spherical magic numbers `2, 8, 20, 28, 50, 82, 126` sit on it.

**Six-pillar roles at the shell level**

| pillar | shell role |
| --- | --- |
| Capacity `πΔ` | the `2n+l` oscillator count — the primary shell order |
| Map `χ` | the `l` angular structure of an orbital |
| Protocol `−1/167` | candidate spin–orbit coupling |
| Governor `−χ/Δ` | per-slot level spacing |
| Toll | the closure boundary (a magic number) |
| Margin | the smooth background (Strutinsky) |

**Open — the derivation target.** The *spacings* (oscillator scale, spin–orbit,
`l²`) are model inputs in `SingleParticle` (`kappa`, `mu`, `delta`). Turning them
into pillar ratios (`spinOrbitCoupling` is a candidate) would make the
shell-correction energy an E8 prediction instead of a schematic one. See
`REVIEW-AND-NEXT.md` §1 (Q2).
-/

noncomputable section
namespace PMAtoms

/-! ## The orbital occupancy -/

/-- Oscillator index `2n+l`: the Capacity order of the shell ladder. -/
def oscIndex (o : NuclearOrbital) : Nat := 2 * o.n + o.l

/-- Every orbital's capacity is `2j+1 = j2+1`. -/
theorem orbital_capacity :
    nuclearOrbitals126.all (fun o => o.occupation == o.j2 + 1) = true := by decide

/-- The shell order is the oscillator (`2n+l`) order: nondecreasing down the ladder. -/
theorem oscillator_order :
    (nuclearOrbitals126.zip (nuclearOrbitals126.drop 1)).all
      (fun p => oscIndex p.1 ≤ oscIndex p.2) = true := by decide

/-- Cumulative occupation: `0` followed by the running sum of capacities. -/
def cumulativeOccupations (xs : List NuclearOrbital) : List Nat :=
  (xs.map (fun o => o.occupation)).scanl (· + ·) 0

theorem cumulativeOccupations_126 :
    cumulativeOccupations nuclearOrbitals126 =
      [0, 2, 6, 8, 14, 16, 20, 28, 32, 38, 40, 50, 58, 64, 68, 70, 82, 92, 100,
        106, 110, 112, 126] := by
  decide

/-- The spherical magic numbers are cumulative occupations of the E8 ladder. -/
theorem closures_on_ladder :
    ∀ m ∈ [2, 8, 20, 28, 50, 82, 126], m ∈ cumulativeOccupations nuclearOrbitals126 := by
  decide

/-! ## The six-pillar budget per orbital -/

theorem cellBudget_pos : (0 : ℝ) < PMHadrons.MesonMasses.cellBudget := by
  rw [show PMHadrons.MesonMasses.cellBudget = PMSubstrate.geometricIndex from rfl]
  linarith [PMSubstrate.geometricIndex_bounds.1]

/-- Six-pillar cost of a filled orbital: `capacity` cells, each paying `cellBudget`. -/
noncomputable def orbitalBudget (o : NuclearOrbital) : ℝ :=
  (o.occupation : ℝ) * PMHadrons.MesonMasses.cellBudget

theorem orbitalBudget_pos (o : NuclearOrbital) (h : 1 ≤ o.occupation) : 0 < orbitalBudget o := by
  unfold orbitalBudget
  exact mul_pos (by exact_mod_cast h) cellBudget_pos

/-- Each orbital's budget is `capacity × cellBudget` — all six pillars paid per cell. -/
theorem orbitalBudget_eq (o : NuclearOrbital) :
    orbitalBudget o = (o.occupation : ℝ) * PMHadrons.MesonMasses.cellBudget := rfl

/-! ## Candidate E8 spacings -/

/-- Candidate spin–orbit coupling from the pillars: the Governor credit `χ/Δ`. -/
noncomputable def spinOrbitCoupling : ℝ := -(PMSubstrate.governorTerm PMSubstrate.baseline)

theorem spinOrbitCoupling_eq : spinOrbitCoupling = 2 / 43 := by
  unfold spinOrbitCoupling PMSubstrate.governorTerm PMSubstrate.baseline
  norm_num

end PMAtoms
