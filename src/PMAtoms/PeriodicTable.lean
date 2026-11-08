import PMAtoms.Aufbau
import PMAtoms.Shells
import Mathlib.Tactic

/-!
# The periodic table from the E8 shell capacities

The shapes of the periodic table follow from the Aufbau order and the E8 subshell
capacities `2(2ℓ+1)` (`PMAtoms.Shells`). The periods partition the Aufbau order
into the conventional blocks; each period length is the sum of its block's
capacities, and the cumulative ends are the noble-gas atomic numbers. The block
partition and the conventional order are model inputs (as in `Aufbau`); the
capacities and the resulting counts are E8.
-/

namespace PMAtoms.PeriodicTable

open Aufbau

/-- The subshells filled in each period (the conventional Aufbau blocks). -/
def periodSubshells : List (List (ℕ × ℕ)) :=
  [[(1, 0)],
   [(2, 0), (2, 1)],
   [(3, 0), (3, 1)],
   [(4, 0), (3, 2), (4, 1)],
   [(5, 0), (4, 2), (5, 1)],
   [(6, 0), (4, 3), (5, 2), (6, 1)],
   [(7, 0), (5, 3), (6, 2), (7, 1)]]

/-- **The periods partition the Aufbau order.** -/
theorem periodSubshells_flatten : periodSubshells.flatten = aufbau := by decide

/-- Capacity of a block: the sum of its subshell capacities. -/
def blockCapacity (P : List (ℕ × ℕ)) : ℕ := (P.map subshellCapacity).sum

/-- The period lengths, computed from the E8 capacities. -/
def periodLengths : List ℕ := periodSubshells.map blockCapacity

/-- **Period lengths `2, 8, 8, 18, 18, 32, 32`.** -/
theorem periodLengths_eq : periodLengths = [2, 8, 8, 18, 18, 32, 32] := by decide

/-- The noble-gas atomic numbers (frozen chemistry comparison values). -/
def nobleNumbers : List ℕ := [2, 10, 18, 36, 54, 86, 118]

/-- **The noble-gas numbers are the cumulative period lengths.** -/
theorem nobleNumbers_eq :
    nobleNumbers = (List.scanl (· + ·) 0 periodLengths).tail := by decide

/-- Valence electrons: those in the highest occupied principal quantum number `n`,
read from the Aufbau configuration. -/
def valenceElectrons (z : ℕ) : ℕ :=
  let c := configuration z
  let nmax := c.foldl (fun acc p => max acc p.1.1) 0
  (c.filter (fun p => p.1.1 = nmax)).foldl (fun acc p => acc + p.2) 0

example : valenceElectrons 1 = 1 := by decide
example : valenceElectrons 2 = 2 := by decide

end PMAtoms.PeriodicTable
