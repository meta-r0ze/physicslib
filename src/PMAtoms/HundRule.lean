import PMAtoms.Aufbau
import Mathlib.Tactic

/-!
# Hund's first rule from the persistence filter

Two electrons of the same spin can persist together only in a spatially antisymmetric state, so
they never share a point: same-spin pairs carry no coincidence events, and a configuration with
more same-spin pairs has fewer distinction events and persists better. This is the filter that
gives the nuclear like-pair weight (`IsospinLedger.likePersistingStates`), applied to electrons.

Within a subshell of `m = 2ℓ+1` orbitals, `k` electrons split into `up` and `down` with
`up, down ≤ m` (Pauli; `spinStates = 2` from `PL.trace`). The same-spin pair count
`C(up,2) + C(down,2)` is largest for the most aligned split `up = min(k, m)`
(`hund_maximizes`), and only that split and its mirror reach it (`hund_unique`). Its spin is
`2S = min(k, 2m − k)` (`hundSpin2`). That is Hund's first rule, derived by counting.

**Comparison.** Applied to the Aufbau configurations (the fill order is a supplied input,
`Aufbau`), the ground-state multiplicity `2S+1` matches the observed ground term for `Z = 1–54`
except Cr, Nb, Mo and Pd (`groundMultiplicity_aufbau`). Those four are exactly where the observed
configuration differs from the Aufbau order (`3d⁵4s¹`, `4d⁴5s¹`, `4d⁵5s¹`, `4d¹⁰`); on the
observed configurations the counting gives the observed multiplicity for them too
(`groundMultiplicity_exceptions`). So the spin rule is derived; the fill order stays the input.
-/

namespace PMAtoms.Hund
open PMAtoms.Aufbau

/-- Same-spin pairs of a spin split. -/
def sameSpinPairs (up down : ℕ) : ℕ := up.choose 2 + down.choose 2

/-- The most aligned split: as many up-spins as there are orbitals. -/
def hundUp (m k : ℕ) : ℕ := min k m

/-- `2S` of the most aligned split of `k` electrons in subshell `ℓ` (`m = 2ℓ+1` orbitals). -/
def hundSpin2 (l k : ℕ) : ℕ := hundUp (2 * l + 1) k - (k - hundUp (2 * l + 1) k)

/-- **The aligned split maximizes same-spin pairs** (`s, p, d, f` subshells, every Pauli-allowed
occupation and split). -/
theorem hund_maximizes :
    ∀ l < 4, ∀ k ≤ 2 * (2 * l + 1), ∀ up ≤ k, up ≤ 2 * l + 1 → k - up ≤ 2 * l + 1 →
      sameSpinPairs up (k - up) ≤
        sameSpinPairs (hundUp (2 * l + 1) k) (k - hundUp (2 * l + 1) k) := by
  decide +kernel

/-- **Only the aligned split and its mirror reach the maximum.** -/
theorem hund_unique :
    ∀ l ∈ List.range 4, ∀ k ∈ List.range (2 * (2 * l + 1) + 1), ∀ up ∈ List.range (k + 1),
      (up ≤ 2 * l + 1 ∧ k - up ≤ 2 * l + 1 ∧
        sameSpinPairs up (k - up) =
          sameSpinPairs (hundUp (2 * l + 1) k) (k - hundUp (2 * l + 1) k)) →
        up = hundUp (2 * l + 1) k ∨ k - up = hundUp (2 * l + 1) k := by
  decide +kernel

/-- `2S = min(k, 2m − k)`. -/
theorem hundSpin2_eq : ∀ l < 4, ∀ k ≤ 2 * (2 * l + 1),
    hundSpin2 l k = min k (2 * (2 * l + 1) - k) := by
  decide +kernel

/-- Ground-state `2S` of a configuration: each subshell aligned, and the subshells aligned with
each other (which also maximizes same-spin pairs). -/
def configSpin2 (c : List ((ℕ × ℕ) × ℕ)) : ℕ := (c.map fun p => hundSpin2 p.1.2 p.2).sum

/-- Ground-state multiplicity `2S+1` of the Aufbau configuration of `z` electrons. -/
def groundMultiplicity (z : ℕ) : ℕ := configSpin2 (configuration z) + 1

/-- Observed ground-term multiplicities `2S+1`, `Z = 1–54` (comparison data). -/
def observedMultiplicity : List ℕ :=
  [2, 1, 2, 1, 2, 3, 4, 3, 2, 1,
   2, 1, 2, 3, 4, 3, 2, 1,
   2, 1, 2, 3, 4, 7, 6, 5, 4, 3, 2, 1, 2, 3, 4, 3, 2, 1,
   2, 1, 2, 3, 6, 7, 6, 5, 4, 1, 2, 1, 2, 3, 4, 3, 2, 1]

theorem observedMultiplicity_length : observedMultiplicity.length = 54 := by decide

/-- **Hund on the Aufbau configurations.** Predicted multiplicities for `Z = 1–54`; they differ
from `observedMultiplicity` only at `Z = 24, 41, 42, 46` (Cr, Nb, Mo, Pd). -/
theorem groundMultiplicity_aufbau :
    (List.range 54).map (fun i => groundMultiplicity (i + 1)) =
      [2, 1, 2, 1, 2, 3, 4, 3, 2, 1,
       2, 1, 2, 3, 4, 3, 2, 1,
       2, 1, 2, 3, 4, 5, 6, 5, 4, 3, 2, 1, 2, 3, 4, 3, 2, 1,
       2, 1, 2, 3, 4, 5, 6, 5, 4, 3, 2, 1, 2, 3, 4, 3, 2, 1] := by
  decide +kernel

/-- The mismatches are exactly Cr, Nb, Mo, Pd. -/
theorem aufbau_mismatches :
    ((List.range 54).filter fun i =>
        groundMultiplicity (i + 1) ≠ observedMultiplicity.getD i 0).map (· + 1) =
      [24, 41, 42, 46] := by
  decide +kernel

/-- **Hund on the observed configurations of the Aufbau exceptions** (open subshells only):
Cr `3d⁵4s¹` → 7, Nb `4d⁴5s¹` → 6, Mo `4d⁵5s¹` → 7, Pd `4d¹⁰` → 1; also Cu `3d¹⁰4s¹` → 2,
Ru `4d⁷5s¹` → 5, Rh `4d⁸5s¹` → 4, Ag `4d¹⁰5s¹` → 2. -/
theorem groundMultiplicity_exceptions :
    configSpin2 [((3, 2), 5), ((4, 0), 1)] + 1 = 7 ∧
    configSpin2 [((4, 2), 4), ((5, 0), 1)] + 1 = 6 ∧
    configSpin2 [((4, 2), 5), ((5, 0), 1)] + 1 = 7 ∧
    configSpin2 [((4, 2), 10)] + 1 = 1 ∧
    configSpin2 [((3, 2), 10), ((4, 0), 1)] + 1 = 2 ∧
    configSpin2 [((4, 2), 7), ((5, 0), 1)] + 1 = 5 ∧
    configSpin2 [((4, 2), 8), ((5, 0), 1)] + 1 = 4 ∧
    configSpin2 [((4, 2), 10), ((5, 0), 1)] + 1 = 2 := by
  decide +kernel

end PMAtoms.Hund
