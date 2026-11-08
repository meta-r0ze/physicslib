import PMAtoms.Shells
import Mathlib.Tactic

/-!
# The Aufbau order and electron configuration

First module of the chemistry pillar. The *capacities* are E8-derived
(`PMAtoms.Shells`: `2ℓ+1` magnetic states times the spin-2 rank of the PM-2 chiral
projector, giving the shell capacity `2n²`). The *order* in which subshells fill
is the Madelung/Aufbau rule `(n+ℓ, n)`; it is a supplied model input here (the
hydrogenic energy `−R∞/n²` carries no `ℓ`-dependence, so the order needs the
screening/chemistry physics). This module states the order and configuration
explicitly so chemistry comparisons can be built on top.
-/

namespace PMChemistry.Aufbau

/-- The Madelung sort key `(n+ℓ)·8 + n`. With `n ≤ 7` this is strictly increasing
exactly along the `(n+ℓ, n)` order, so it linearizes the Aufbau rule. -/
def madelungKey (nl : ℕ × ℕ) : ℕ := (nl.1 + nl.2) * 8 + nl.1

/-- The Madelung/Aufbau order of subshells `(n, ℓ)`. -/
def aufbau : List (ℕ × ℕ) :=
  [(1, 0), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (3, 2), (4, 1),
   (5, 0), (4, 2), (5, 1), (6, 0), (4, 3), (5, 2), (6, 1),
   (7, 0), (5, 3), (6, 2), (7, 1)]

/-- **The order is the Madelung order**: the keys are strictly increasing and the
list is duplicate-free. -/
theorem aufbau_sorted :
    (aufbau.map madelungKey).Pairwise (· < ·) := by decide

theorem aufbau_nodup : aufbau.Nodup := by decide

/-- Subshell capacity `2(2ℓ+1)`, from `PMAtoms.Shells`. -/
def subshellCapacity (nl : ℕ × ℕ) : ℕ := PMAtoms.orbitalCapacity nl.2

theorem subshellCapacity_eq (nl : ℕ × ℕ) :
    subshellCapacity nl = 4 * nl.2 + 2 :=
  PMAtoms.orbitalCapacity_eq nl.2

/-- Fill `z` electrons in the Aufbau order, returning `(subshell, occupation)`. -/
def fill : List (ℕ × ℕ) → ℕ → List ((ℕ × ℕ) × ℕ)
  | [], _ => []
  | nl :: rest, z =>
      let taken := min z (subshellCapacity nl)
      if taken = 0 then [] else (nl, taken) :: fill rest (z - taken)

/-- The electron configuration of `z` electrons (the Aufbau order). -/
def configuration (z : ℕ) : List ((ℕ × ℕ) × ℕ) := fill aufbau z

example : configuration 0 = [] := rfl
example : configuration 1 = [((1, 0), 1)] := rfl

end PMChemistry.Aufbau
