import PMConstants.ReferenceAxis
import PMConstants.GaugeLedgers
import Mathlib.GroupTheory.Perm.Fin

/-!
# Which frame rows the electroweak refreshes cover

The frame is `172 = D·Δ`: four rows (the lattice directions) of `43` phase addresses. The carriers
`±2eᵢ` lie along the same four directions, so a carrier axis and a frame row are the same index; the
reserved reference occupies one row, its axis (`ReferenceAxis`).

**Which row.** Paper I's signature already distinguishes the time direction. `axis_symmetry_kept`:
among the axis permutations that respect the signature (fix time), those that also fix the
reference's axis number `6` if the reference is on the time axis and `2` otherwise. Placing it on a
spatial axis would add a maintained distinction (a preferred spatial direction) and break spatial
isotropy; Economy places it on the time axis. So the reserved row is the clock row and the lepton axis
is temporal; the three colour axes are spatial.

**Which sector covers which row.** Every frame row must be refreshed (Conservation), each exactly once
(Economy, `MinimalRefresh.strict_if_extra`), and only the electroweak refreshes read the frame (colour
reads the payload, `ColourReference`).
* Weak moves the reference within its own axis (the doublet index is the carrier's sign), so it must
  refresh the reference row, and it acts on no other row.
* `rows_assigned`: under these constraints the assignment is forced: weak refreshes the clock row
  alone and hypercharge the three spatial rows.
* `frame_ledgers`: the frame parts of the two ledgers are `43` and `129`, the clock and spatial
  resources of `GaugeLedgers` (`frame_matches`).

`identification_is_identity`: the only row-to-axis identification commuting with every axis
permutation is the identity. Premises: frame rows and carrier axes are both the lattice
directions; weak acts on the
frame only through the reference. The wire and payload parts of the hypercharge ledger are not
derived here.
-/

namespace PMConstants.RequirementRows
open Finset

/-- **The reference on the time axis keeps all signature-compatible axis symmetry.** -/
theorem axis_symmetry_kept (a : Fin 4) :
    (univ.filter fun σ : Equiv.Perm (Fin 4) => σ 0 = 0 ∧ σ a = a).card = if a = 0 then 6 else 2 := by
  revert a; decide

inductive Sector | weak | hyper
  deriving DecidableEq

/-- **The row assignment is forced.** `f r` is the sector refreshing row `r` (row `0` is the
reference row). Weak must refresh the reference row and refreshes no other. -/
theorem rows_assigned (f : Fin 4 → Sector) (hw : f 0 = .weak) (hconf : ∀ r, f r = .weak → r = 0) :
    ∀ r, f r = if r = 0 then .weak else .hyper := by
  intro r
  by_cases h : r = 0
  · subst h; simp [hw]
  · simp only [h, ↓reduceIte]
    cases hfr : f r
    · exact absurd (hconf r hfr) h
    · rfl

/-- **Rows and axes are identified by the identity.** Frame rows and carrier axes are both indexed
by the four lattice directions, with the same axis-permutation symmetry. An identification that
commutes with every axis permutation is the identity: any other would single out directions, a
further distinction to maintain. -/
theorem identification_is_identity (f : Equiv.Perm (Fin 4))
    (hf : ∀ σ : Equiv.Perm (Fin 4), f * σ = σ * f) : f = 1 := by
  revert f; decide

/-- Frame resources per row. -/
def rowWeight : ℕ := 43

/-- **The frame parts of the electroweak ledgers.** -/
theorem frame_ledgers (f : Fin 4 → Sector) (hw : f 0 = .weak) (hconf : ∀ r, f r = .weak → r = 0) :
    (univ.filter fun r => f r = .weak).card * rowWeight = 43 ∧
      (univ.filter fun r => f r = .hyper).card * rowWeight = 129 := by
  have hf := rows_assigned f hw hconf
  have : f = fun r => if r = 0 then .weak else .hyper := funext hf
  subst this
  constructor <;> decide

theorem frame_matches :
    GaugeLedgers.weight .clock = 43 ∧ GaugeLedgers.weight .space = 129 := ⟨rfl, rfl⟩

end PMConstants.RequirementRows
