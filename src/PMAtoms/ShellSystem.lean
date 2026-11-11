import PMAtoms.NuclearShells
import PMAtoms.SingleParticle
import PMHadrons.MesonMasses
import PMHadrons.Emission
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
| Map `χ` | the **closure boundary**: `mapTerm = eulerCharacteristic = χ = 2` (two-sided edge) |
| Protocol `−1/167` | the **successor map** — the orbital ladder order (`protocol_deterministic`) |
| Governor `−χ/Δ` | the level **spacing** `ℏω(A) = χ·m_p/(Δ·A^{1/3})`. As a spin–orbit strength `χ/Δ` orders the levels and gives the closures `2, 8, 20, 40, 70`; `1/ν` with `μ = χ/σ` gives `2, 8, 20, 28, 50, 82, 126` (`ShellGaps`) |
| Toll | **emission** (de-excitation): the boundary `ValidToll`, weight `tollTerm` |
| Margin | the **reference cone** (smooth background): `marginTerm = 1/(L_embed(σ+1)Δ²)` |

**Result — the `l²`/spin–orbit ratio is forced.**  The recorded shell order is
reproducible **iff** the `l²` coefficient is exactly `κ/D` (`l2_ratio_forced`; the
equal-`2n+l` ties `2s½ ≤ 1d₃/₂` and `1g₇/₂ ≤ 2d₅/₂` bracket it). With
`κ = χ/Δ`, `κ₂ = κ/D` the E8 orbital cost is nondecreasing down the ladder
(`e8OrbitalOrder`). So the *shape* of the shell spectrum is E8; only the overall
**scale** `κ` is free — the order bounds it to `(0, 1/14]` but does not single it
out, so it needs an E8 energy scale (the mass gap / ℏω), not a fit. The energy scale is
`ℏω(A) = χ·m_p/(Δ·A^{1/3})` (`shellQuantum`): the Governor budget over the packing-cube side. See
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

/-! ## Map: the closure boundary -/

/-- The **Map pillar is the Euler characteristic** `χ = 2` (`mapTerm = eulerCharacteristic`). -/
theorem mapTerm_eq : PMSubstrate.mapTerm PMSubstrate.baseline = 2 := by
  unfold PMSubstrate.mapTerm PMSubstrate.baseline
  norm_num

/-- The spherical shell blocks: the ladder partitioned by its closures. -/
def sphericalShellSizes : List Nat := [2, 6, 12, 8, 22, 32, 44]

theorem sphericalShellSizes_sum : sphericalShellSizes.sum = 126 := by decide

/-- **The closures are the Map boundaries of the ladder**: the partial sums of the spherical
shell sizes are exactly the spherical magic numbers `2, 8, 20, 28, 50, 82, 126`. So the ladder is
partitioned into shells whose edges are the closures — the closure *is* a boundary (`χ = 2`
sides: inside/outside). -/
theorem closure_is_mapBoundary :
    (sphericalShellSizes.scanl (· + ·) 0).drop 1 = [2, 8, 20, 28, 50, 82, 126] := by decide

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

/-- The Governor credit `χ/Δ`. It sets the shell spacing (`shellEnergyUnit`, `shellQuantum`).
Used as the spin–orbit strength it reproduces the recorded order (`e8OrbitalOrder`) but makes the
oscillator numbers `20, 40, 70` the closures instead of `28, 50, 82`
(`ShellGaps.shellSystem_oscillator_closures_dominate`); the spin–orbit strength that gives the
observed closures is `κ = 1/ν` with `μ = χ/σ` (`ShellGaps.nilssonE8_gaps`). -/
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

/-- Shell energy budget per nucleon: the nucleon mass times the Governor credit `χ/Δ`.
With Protocol identified as the *ordering* (successor) and Capacity as the *room* (`2j+1`),
Governor is the *spacing* — the spectral gap `χ` per clock step `m_p/Δ`.
In `m_e`: `m_p·χ/Δ ≈ 85.4 m_e ≈ 43.6 MeV`. The Protocol assignment (1/167) and Capacity (πΔ)
give the wrong scales (5.6, 69 MeV), which is what fixes Governor as the spacing.

This is the **size-independent coefficient**, i.e. `ℏω` of a one-cell system (`A = 1`). The
oscillator quantum of a nucleus is `shellQuantum A = shellEnergyUnit / A^{1/3}`; see below. -/
noncomputable def shellEnergyUnit : ℝ := PMHadrons.CompositeMasses.proton * spinOrbitCoupling

theorem shellEnergyUnit_eq : shellEnergyUnit = PMHadrons.CompositeMasses.proton * (2 / 43) := by
  unfold shellEnergyUnit; rw [spinOrbitCoupling_eq]

/-- `χ/Δ · ℏω` at the one-cell scale. Superseded as the spin–orbit splitting by the E8 Nilsson
strength `2κ·ℏω`, `κ = 1/ν` (`ShellGaps`). -/
noncomputable def spinOrbitEnergy : ℝ := shellEnergyUnit * spinOrbitCoupling

theorem spinOrbitEnergy_eq :
    spinOrbitEnergy = PMHadrons.CompositeMasses.proton * (2 / 43) ^ 2 := by
  unfold spinOrbitEnergy; rw [shellEnergyUnit_eq, spinOrbitCoupling_eq]; ring

/-! ## The shell quantum scales with the cube side (Q2 item 4, step 1)

`shellEnergyUnit` has no size dependence, but the measured oscillator spacing falls as
`A^{-1/3}` (`≈ 41 A^{-1/3}` MeV). The size enters through the packing complex: the nucleus is a
cube of side `A^{1/3}` (`shellSide`), and the continuous packing counts are exact at
`A = n³` (`NuclearPacking3D.packingLinks_cube`, `shellSide_cube`). The Governor's clock step
`m_p/Δ` belongs to one cell; across a cube of side `s` the same credit `χ` is spread over `s`
cells along each axis, so

  `ℏω(A) = χ·m_p / (Δ·A^{1/3})`   (`shellQuantum`).

Comparison (MeV; not an input): `A = 16, 40, 90, 208` give `17.3, 12.8, 9.7, 7.4`, against
`41 A^{-1/3}` = `16.3, 12.0, 9.2, 6.9` (E8 about 6% high at every `A`). The two-term fit
`45 A^{-1/3} − 25 A^{-2/3}` = `13.9, 11.0, 8.8, 6.9` is lower for light nuclei; that
`A^{-2/3}` surface correction is not derived here. The other natural reading, the budget over the
number of filled oscillator shells `(3A)^{1/3}`, gives `5.1` MeV at `A = 208` (26% low) and is not
used. Nothing here is fitted: the coefficient is `χ·m_p/Δ` and the exponent is the cube side. -/

/-- Linear size of the packing cube, `A^{1/3}`. -/
noncomputable def shellSide (a : Nat) : ℝ := (a : ℝ) ^ ((1 : ℝ) / 3)

/-- At a cubic size `n³` the side is exactly `n`. -/
theorem shellSide_cube (n : Nat) : shellSide (n ^ 3) = n := by
  unfold shellSide
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
  norm_num

theorem shellSide_pos {a : Nat} (ha : 0 < a) : 0 < shellSide a := by
  unfold shellSide
  exact Real.rpow_pos_of_pos (by exact_mod_cast ha) _

theorem shellSide_mono {a b : Nat} (hab : a ≤ b) : shellSide a ≤ shellSide b := by
  unfold shellSide
  exact Real.rpow_le_rpow (Nat.cast_nonneg a) (by exact_mod_cast hab) (by norm_num)

theorem shellEnergyUnit_pos : 0 < shellEnergyUnit := by
  rw [shellEnergyUnit_eq]
  have hp := PMHadrons.CompositeMasses.proton_value
  nlinarith [hp.1]

/-- **The shell quantum** `ℏω(A) = χ·m_p/(Δ·A^{1/3})`, in `m_e`. -/
noncomputable def shellQuantum (a : Nat) : ℝ := shellEnergyUnit / shellSide a

theorem shellQuantum_eq (a : Nat) :
    shellQuantum a = PMHadrons.CompositeMasses.proton * (2 / 43) / (a : ℝ) ^ ((1 : ℝ) / 3) := by
  unfold shellQuantum shellSide; rw [shellEnergyUnit_eq]

/-- At a cubic size the quantum is the per-cell budget divided by the side. -/
theorem shellQuantum_cube (n : Nat) : shellQuantum (n ^ 3) = shellEnergyUnit / n := by
  unfold shellQuantum; rw [shellSide_cube]

/-- A one-cell system has the full budget as its quantum. -/
theorem shellQuantum_one : shellQuantum 1 = shellEnergyUnit := by
  simpa using shellQuantum_cube 1

theorem shellQuantum_pos {a : Nat} (ha : 0 < a) : 0 < shellQuantum a :=
  div_pos shellEnergyUnit_pos (shellSide_pos ha)

/-- Larger nuclei have smaller shell spacings. -/
theorem shellQuantum_antitone {a b : Nat} (ha : 0 < a) (hab : a ≤ b) :
    shellQuantum b ≤ shellQuantum a := by
  unfold shellQuantum
  exact div_le_div_of_nonneg_left (le_of_lt shellEnergyUnit_pos) (shellSide_pos ha)
    (shellSide_mono hab)

/-- `χ/Δ · ℏω(A)`. The spin–orbit splitting uses `2κ·ℏω(A)` with `κ = 1/ν` (`ShellGaps`). -/
noncomputable def spinOrbitEnergyAt (a : Nat) : ℝ := shellQuantum a * spinOrbitCoupling

/-! ## Protocol: the orbital successor (coordinates the next level)

`PMSubstrate.PersistenceEvents.protocol_persistence` gives the Protocol as a **function**
`X → Fin 167`: exactly one successor per state, reached with probability
`1/(R_M − σ) = 1/167`. At the shell level the successor is the **next orbital** — the ladder
order is the Protocol's orbit. -/

/-- The Protocol's transitions at the shell level: consecutive orbitals of the ladder. -/
def protocolSteps : List (NuclearOrbital × NuclearOrbital) :=
  nuclearOrbitals126.zip (nuclearOrbitals126.drop 1)

theorem protocolSteps_length : protocolSteps.length = 21 := by decide

/-- **The successor is deterministic**: each orbital has exactly one successor (the Protocol is
a function, not a relation), matching `protocol_persistence`. -/
theorem protocol_deterministic : (protocolSteps.map Prod.fst).Nodup := by decide

/-- **The Protocol credit** is one successor among the `R_M − σ = 167` residual addresses,
`−(protocolTerm) = 1/167`. -/
theorem protocol_credit :
    -(PMSubstrate.protocolTerm PMSubstrate.baseline) = 1 / 167 := by
  unfold PMSubstrate.protocolTerm PMSubstrate.baseline PMSubstrate.Parameters.resolution
  norm_num

/-! ## Toll: the shell emission boundary

A single-particle **de-excitation** (a nucleon dropping between orbitals) is a boundary
transition, exactly as in `PMHadrons.Emission`: `Γ = Toll × |overlap|² × phase space`, with the
Toll boundary weight `tollTerm` (`χ = 2` exposed-leg orientations × the `R_M − σ = 167` non-aliased
addresses, card 334). -/

/-- The shell emission overlap: the initial and final single-particle configurations. -/
def shellEmissionOverlap {ι : Type*} [Fintype ι] (ψ φ : PMHadrons.BoundStateOverlap.Wavefunction ι) : ℂ :=
  PMHadrons.BoundStateOverlap.overlap ψ φ

/-- **The shell emission boundary is the Toll**: weight `emissionWeight = tollTerm`. -/
theorem shellEmissionWeight_eq :
    PMHadrons.TollGovernor.emissionWeight = PMSubstrate.tollTerm PMSubstrate.baseline := rfl

theorem shellEmissionWeight_pos : 0 < PMHadrons.TollGovernor.emissionWeight :=
  PMHadrons.TollGovernor.emissionWeight_pos

theorem shellEmissionBoundary_card :
    Fintype.card PMHadrons.TollGovernor.EmissionBoundary = 334 :=
  PMHadrons.TollGovernor.emissionBoundary_card

/-- The shell emission width: `Toll × |overlap|² × phase` — a single-particle de-excitation. -/
noncomputable def shellEmissionWidth {ι : Type*} [Fintype ι]
    (ψ φ : PMHadrons.BoundStateOverlap.Wavefunction ι) (phase : ℝ) : ℝ :=
  PMHadrons.TollGovernor.emissionWeight * Complex.normSq (shellEmissionOverlap ψ φ) * phase

theorem shellEmissionWidth_nonneg {ι : Type*} [Fintype ι]
    (ψ φ : PMHadrons.BoundStateOverlap.Wavefunction ι) {phase : ℝ} (hphase : 0 ≤ phase) :
    0 ≤ shellEmissionWidth ψ φ phase := by
  unfold shellEmissionWidth shellEmissionOverlap
  exact mul_nonneg
    (mul_nonneg shellEmissionWeight_pos.le (Complex.normSq_nonneg _)) hphase

/-- **The shell de-excitation is the general rate form** `|T|²·phase` with `T = √Toll · overlap`. -/
theorem shellEmissionWidth_eq_partialWidth {ι : Type*} [Fintype ι]
    (ψ φ : PMHadrons.BoundStateOverlap.Wavefunction ι) (phase : ℝ) :
    shellEmissionWidth ψ φ phase =
      Complex.normSq ((Real.sqrt PMHadrons.TollGovernor.emissionWeight : ℂ) *
        shellEmissionOverlap ψ φ) * phase := by
  unfold shellEmissionWidth
  rw [Complex.normSq_mul, Complex.normSq_ofReal,
    Real.mul_self_sqrt shellEmissionWeight_pos.le]

/-- The shell transition gap between two orbitals, in oscillator units (`orbitalCostZ` is `× 172`). -/
noncomputable def shellTransitionGap (hi lo : NuclearOrbital) : ℝ :=
  ((orbitalCostZ hi - orbitalCostZ lo : ℤ) : ℝ) / 172

/-- The shell transition energy at the one-cell scale `shellEnergyUnit` (`A = 1`). -/
noncomputable def shellTransitionEnergy (hi lo : NuclearOrbital) : ℝ :=
  shellTransitionGap hi lo * shellEnergyUnit

/-- The shell transition energy in a nucleus of `A` nucleons: the gap in `ℏω(A)`. -/
noncomputable def shellTransitionEnergyAt (a : Nat) (hi lo : NuclearOrbital) : ℝ :=
  shellTransitionGap hi lo * shellQuantum a

theorem shellTransitionEnergyAt_one (hi lo : NuclearOrbital) :
    shellTransitionEnergyAt 1 hi lo = shellTransitionEnergy hi lo := by
  unfold shellTransitionEnergyAt shellTransitionEnergy; rw [shellQuantum_one]

/-! ## Margin: the reference cone (smooth background)

The Margin pillar is the **reference cone**: `marginTerm = 1/(L_embed·(σ+1)·Δ²)`, a state space of
`31·6·43·43 = 343914`. At the shell level it is the **smooth background** a shell correction is
measured against (Strutinsky). -/

/-- The Margin pillar is the reference-cone weight `1/(L_embed(σ+1)Δ²) = 1/343914`. -/
theorem marginTerm_eq : PMSubstrate.marginTerm PMSubstrate.baseline = 1 / 343914 := by
  unfold PMSubstrate.marginTerm PMSubstrate.baseline
  norm_num [PMSubstrate.Parameters.embeddingLoad, PMSubstrate.Parameters.intrinsicLoad]

/-- The reference cone has `L_embed·(σ+1)·Δ² = 343914` states. -/
theorem marginSpace_card : Fintype.card PMSubstrate.MarginSpace = 343914 := by
  simp [PMSubstrate.MarginSpace]

/-- The shell smooth background — the Margin role: the reference cone against which the shell
correction is measured (`SingleParticle.smoothEnergy`). -/
noncomputable def shellBackground (xs : List NuclearOrbital) (N w : Nat) : ℝ :=
  PMAtoms.smoothEnergy xs N w

theorem shellBackground_eq (xs : List NuclearOrbital) (N w : Nat) :
    shellBackground xs N w = PMAtoms.smoothEnergy xs N w := rfl

/-- The shell correction is the difference from the Margin background. -/
noncomputable def shellStrutinskyCorrection (xs : List NuclearOrbital) (N w : Nat) : ℝ :=
  PMAtoms.strutinskyCorrection xs N w

end PMAtoms
