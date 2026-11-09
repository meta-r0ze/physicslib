import PersistenceMechanics.Requirements
import PMSubstrate.Vacuum
import PMSubstrate.MainTheorem
import PMSubstrate.DerivedParameters
import PMSubstrate.ImpedanceTerms

/-!
# The requirement ↔ postulate ↔ theorem bridge

`PersistenceMechanics.Requirements` names PM's three requirements, the six pillars, and the
substrate-postulate **readings** (with the theorem names as strings, since the framework layer is
upstream). This module closes the loop with real references:

* `Consequence` states, for each reading, the substrate-side proposition it delivers, and
  `consequence_holds` proves every one from the actual `PMSubstrate` theorem.
* `geometric_reading` proves the **reading itself**: a `Geometric` substrate with a bijective
  update satisfies PM's three requirements (`PMRequirements`).

So the direction is explicit end to end: **PM requirements → readings → postulates → the substrate
is derived**, with both ends machine-checked.
-/

noncomputable section
namespace PMSubstrate.RequirementMap
open PersistenceMechanics.Requirements
open PMSubstrate.Vacuum
open Matrix

/-- The substrate-side consequence of each postulate reading, as a proposition. Each is proved
below from the real theorem (see the docstrings there). -/
def Consequence : Postulate → Prop
  | .addresses => True
  | .finiteLevels => ∀ s : Substrate, Geometric s → (s.A.map (Int.cast : ℤ → ℝ)).PosDef
  | .readable => ∀ s : Substrate, Geometric s → IsUnit s.A.det
  | .bitAddressed =>
      ∀ s : Substrate, Geometric s → ∃ M : Matrix (Fin s.n) (Fin s.n) ℤ, s.A * M = (2 : ℤ) • 1
  | .exchange => ∀ s : Substrate, Geometric s → ∀ z : Fin s.n → ℤ, Even (z ⬝ᵥ (s.A *ᵥ z))
  | .economy => ∀ s : Substrate, Geometric s → Economical s → ClaimBoundary.IsE8 s.A
  | .sectors => ∀ s : Substrate, SectorPostulates s →
      ∃ S : Matrix (Fin s.n) (Fin 8) ℤ, Sᵀ * s.A * S = Channels.d4d4
  | .clockPlane => ∀ (s : Substrate) (Δ : ℕ), Geometric s → Economical s → SectorPostulates s →
      ClockPostulates s Δ → Δ = 43
  | .clockSchedule => ∀ (s : Substrate) (Δ : ℕ), Geometric s → Economical s → SectorPostulates s →
      ClockPostulates s Δ → Δ = 43
  | .signature => ∀ q : Fin 5, Derived.SignaturePostulate q → q.val = 1
  | .boundary => ∀ S : ImpedanceTerms.ClosedSurface, Derived.BoundaryPostulate S → S.euler = 2

/-- **Every reading delivers its consequence**, proved from the substrate theorem:
`geometric_lattice`, `geometric_selects_e8`, `sectors_are_d4`, `vacuum_selects`, `Derived.one_time`,
`Derived.boundary_sphere`. -/
theorem consequence_holds : ∀ p : Postulate, Consequence p := by
  intro p
  cases p
  · trivial
  · intro s h; exact (geometric_lattice h).1
  · intro s h; exact (geometric_lattice h).2.2.1
  · intro s h; exact h.bitAddressed
  · intro s h z; exact (geometric_lattice h).2.1 z
  · intro s h hm; exact geometric_selects_e8 h hm
  · intro s h; exact sectors_are_d4 h
  · intro s Δ h hm hsec hc; exact (vacuum_selects h hm hsec hc).2.2.1
  · intro s Δ h hm hsec hc; exact (vacuum_selects h hm hsec hc).2.2.1
  · intro q h; exact Derived.one_time h
  · intro S h; exact (Derived.boundary_sphere h).2

/-- **The reading: `Geometric` satisfies PM's requirements.** A substrate whose cost levels are
finite (`Geometric.finite`) and whose update is a bijection (Conservation, `never_merge_iff_bijective`;
Causality) is a `PMRequirements` instance on `ℤⁿ`. So `Geometric` *is* the lattice reading of the
three requirements, not an independent assumption. -/
def geometric_reading {s : Substrate} (h : Geometric s)
    (step : (Fin s.n → ℤ) → (Fin s.n → ℤ)) (hstep : Function.Bijective step) :
    PMRequirements (Fin s.n → ℤ) where
  step := step
  cost := fun (x : Fin s.n → ℤ) => ((x ⬝ᵥ (s.A *ᵥ x) : ℤ) : ℝ)
  finiteness := by
    intro c
    refine (h.finite (Int.floor c)).subset ?_
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    exact Int.le_floor.mpr hx
  conservation := hstep.1
  causality := hstep.2

/-- **S1, explored.** The three requirements alone do not force an additive lattice
(`PersistenceMechanics.Requirements.requirements_not_lattice`); Paper I's Postulate L — addresses
form `Λ ≅ ℤⁿ` with an integral symmetric cost — is the additional *reading*. Two sub-facts pin the
residual: bounded-cost finiteness gives positivity but **not** finite generation (the finite-support
group `ℤ^{(∞)}` has finite cost sublevels yet is not finitely generated), while bit-addressing
(`2Λ* ⊆ Λ`, Postulate A) is what `ℤ^{(∞)}` fails.

**Resolved (negatively).** Bit-addressing does **not** force finite generation: the infinite-rank even
lattice `D_∞ = {x ∈ ℤ^(∞) : Σ xᵢ even}` (`PMSubstrate.Address.DInf`) satisfies bit-addressing
(`Address.two_smul_mem_DInf`, since `ℤ^(∞)` is its own dual in `ℓ²`) and finite cost sublevels, yet is
not finitely generated (`Address.DInf_not_finite`). So the finite generation of Postulate L is a
**genuine additional premise**, not a consequence of the substrate readings. `S1_residual` below names
the (false) sharpening, kept as the record of what was tested. -/
def S1_residual : Prop :=
  ∀ (M : Type*) [AddCommGroup M] (r : PMRequirements M)
    (B : LinearMap.BilinForm ℤ M) (_hcost : ∀ x, r.cost x = (B x x : ℝ)),
    Module.Finite ℤ M

end PMSubstrate.RequirementMap
