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
| Map `χ` | the **shell boundary** (a closure is a capacity-saturation edge) — *label only* |
| Protocol `−1/167` | **unassigned** |
| Governor `−χ/Δ` | candidate spin–orbit coupling `κ`; level spacing (the scale is free) |
| Toll | **emission** (de-excitation), *not* closure: `ValidToll = Fin 2 × Fin 167` is the shedding boundary |
| Margin | the smooth background (Strutinsky) — *label only* |

**Result — the `l²`/spin–orbit ratio is forced.**  The recorded shell order is
reproducible **iff** the `l²` coefficient is exactly `κ/D` (`l2_ratio_forced`; the
equal-`2n+l` ties `2s½ ≤ 1d₃/₂` and `1g₇/₂ ≤ 2d₅/₂` bracket it). With
`κ = χ/Δ`, `κ₂ = κ/D` the E8 orbital cost is nondecreasing down the ladder
(`e8OrbitalOrder`). So the *shape* of the shell spectrum is E8; only the overall
**scale** `κ` is free — the order bounds it to `(0, 1/14]` but does not single it
out, so it needs an E8 energy scale (the mass gap / ℏω), not a fit. See
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

/-- A shell closure: an occupation that is an E8 magic number. -/
def isClosure (n : Nat) : Prop := n ∈ nuclearMagic

/-- Every spherical closure is a **capacity-saturation boundary**: an E8 magic number *and* a
cumulative capacity of the ladder. (The closure *value* — why `Dχ`, `Dσ`, … — is the Capacity
pillar's open derivation; the boundary *structure* is Capacity saturation.) -/
theorem closure_eq_saturation :
    ∀ m ∈ [2, 8, 20, 28, 50, 82, 126],
      m ∈ nuclearMagic ∧ m ∈ cumulativeOccupations nuclearOrbitals126 := by decide

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

/-- Rational `l·s` expectation (the `ℚ` mirror of `SingleParticle.spinOrbit`). -/
def spinOrbitQ (o : NuclearOrbital) : ℚ :=
  (((o.j2 : ℚ) * ((o.j2 : ℚ) + 2) / 4) - ((o.l : ℚ) * ((o.l : ℚ) + 1)) - 3 / 4) / 2

theorem spinOrbit_eq_Q (o : NuclearOrbital) : spinOrbit o = (spinOrbitQ o : ℝ) := by
  unfold spinOrbit spinOrbitQ; push_cast; ring

/-- Orbital cost `2n+l − κ·l·s − κ₂·l(l+1)`: the Capacity order plus the two splittings. -/
noncomputable def orbitalCost (k k2 : ℝ) (o : NuclearOrbital) : ℝ :=
  (oscIndex o : ℝ) - k * spinOrbit o - k2 * ((o.l : ℝ) * ((o.l : ℝ) + 1))

/-- **The `l²` coefficient is forced to `κ/D` by the shell order.**  The two equal-`2n+l`
ties `2s½ ≤ 1d₃/₂` and `1g₇/₂ ≤ 2d₅/₂` bracket it to `κ₂ = κ/4`. -/
theorem l2_ratio_forced {k k2 : ℝ}
    (h1 : orbitalCost k k2 ⟨2, 0, 1, 2⟩ ≤ orbitalCost k k2 ⟨1, 2, 3, 4⟩)
    (h2 : orbitalCost k k2 ⟨1, 4, 7, 8⟩ ≤ orbitalCost k k2 ⟨2, 2, 5, 6⟩) :
    k2 = k / 4 := by
  unfold orbitalCost oscIndex spinOrbit at h1 h2
  push_cast at h1 h2
  nlinarith [h1, h2]

/-- The E8 orbital cost `κ=χ/Δ`, `κ₂=κ/D` scaled by `172 = D·Δ`, as an integer:
`172·(2n+l) − (j2(j2+2) − 4l(l+1) − 3) − 2·l(l+1)`. -/
def orbitalCostZ (o : NuclearOrbital) : ℤ :=
  172 * (oscIndex o : ℤ)
    - ((o.j2 : ℤ) * ((o.j2 : ℤ) + 2) - 4 * ((o.l : ℤ) * ((o.l : ℤ) + 1)) - 3)
    - 2 * ((o.l : ℤ) * ((o.l : ℤ) + 1))

/-- `orbitalCostZ` is `172 = D·Δ` times the real E8 cost `κ = χ/Δ`, `κ₂ = κ/D`. -/
theorem orbitalCostZ_eq (o : NuclearOrbital) :
    (orbitalCostZ o : ℝ) = 172 * orbitalCost (2 / 43) (1 / 86) o := by
  unfold orbitalCostZ orbitalCost oscIndex spinOrbit
  push_cast
  ring

/-- **The E8 spacings reproduce the recorded shell order.**  With `κ = χ/Δ` and
`κ₂ = κ/D` (scaled by `172`), the orbital cost is nondecreasing down
`nuclearOrbitals126`; ties at the E8 ratio are the degenerate pairs the recorded
order resolves. -/
theorem e8OrbitalOrder :
    (nuclearOrbitals126.zip (nuclearOrbitals126.drop 1)).all
      (fun p => orbitalCostZ p.1 ≤ orbitalCostZ p.2) = true := by
  decide

/-! ## The shell energy unit (Q2 item 4) -/

/-- Candidate shell oscillator spacing `ℏω`: the nucleon mass times the Governor credit `χ/Δ`.
In `m_e`: `m_p·χ/Δ ≈ 85.4 m_e ≈ 43.6 MeV`, against the empirical oscillator `ℏω ≈ 41 A^{-1/3}`
MeV.  Pinning this from an E8 *spectral* scale (rather than the empirical value) is the open
item. -/
noncomputable def shellEnergyUnit : ℝ := PMHadrons.CompositeMasses.proton * spinOrbitCoupling

theorem shellEnergyUnit_eq : shellEnergyUnit = PMHadrons.CompositeMasses.proton * (2 / 43) := by
  unfold shellEnergyUnit; rw [spinOrbitCoupling_eq]

/-- The spin–orbit splitting `κ·ℏω = m_p·(χ/Δ)²`. -/
noncomputable def spinOrbitEnergy : ℝ := shellEnergyUnit * spinOrbitCoupling

theorem spinOrbitEnergy_eq :
    spinOrbitEnergy = PMHadrons.CompositeMasses.proton * (2 / 43) ^ 2 := by
  unfold spinOrbitEnergy; rw [shellEnergyUnit_eq, spinOrbitCoupling_eq]; ring

end PMAtoms
