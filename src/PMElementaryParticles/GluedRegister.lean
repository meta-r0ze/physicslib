import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Prod

/-!
# The protocol register on the E8 glued roots

`E₈ = D₄ ⊕ D₄` with diagonal glue: the `192` glued roots are `(a, b)` with `a` and `b` carriers of
the same class (`v`, `s` or `c`) in the two `D₄` factors, `8 × 8` per class. Coordinates are doubled,
so carriers are integer vectors: the vector class is `±2eᵢ`, the spinor classes are `(±1, ±1, ±1, ±1)`
with an even (`s`) or odd (`c`) number of minus signs.

Reading (EP REVIEW, protocol register): each wall of generation `g` is a glue class read through one
factor. On wall T (class `g + 1`) the amplitude is the first factor's carrier and the protocol label
is the second's; on wall F (class `g − 1`) the roles are exchanged. This module checks the finite facts
the reading uses:

* `wallStep_class`: a wall step (a `D₄` root reflection of the amplitude carrier) keeps the class, so
  it keeps the glue class and leaves the label untouched;
* `neg_class`, `neg_ne`: the label's antipode acts within the class with no fixed carrier, so it is a
  sign on the label (`4 + 4`), not a global sign on the wall: it can separate weak partners;
* `triality_class`, `triality_root`, `triality_neg`: an orthogonal map of order three that keeps the
  `D₄` roots, sends class `x` to class `x + 1` and commutes with the antipode, so applied to both
  factors it is an `E₈` automorphism; the factor swap is one too;
* `crossing_walls`: swap followed by the diagonal triality sends every glued root of class `g + 1`
  to a glued root of class `g − 1`, the amplitude from the first factor to the second and the label
  from the second to the first: wall T onto wall F, with the label carried across.

The physical identification (walls, protocols, gauge) is the reading, not proved here.
-/

namespace PMElementaryParticles.GluedRegister

/-- Doubled `D₄` weight coordinates. -/
abbrev Wt := Fin 4 → ℤ

def sgn (b : Bool) : ℤ := if b then -1 else 1

def bit (i : Fin 8) (k : ℕ) : Bool := (i.val / 2 ^ k) % 2 = 1

/-- The eight carriers of class `x` (`0 = v`, `1 = s`, `2 = c`), doubled coordinates. -/
def carrier : Fin 3 → Fin 8 → Wt
  | 0, i => fun t => if t.val = i.val / 2 then 2 * sgn (bit i 0) else 0
  | 1, i => fun t => if t.val < 3 then sgn (bit i t.val)
      else sgn (xor (xor (bit i 0) (bit i 1)) (bit i 2))
  | 2, i => fun t => if t.val < 3 then sgn (bit i t.val)
      else sgn (!(xor (xor (bit i 0) (bit i 1)) (bit i 2)))

/-- The 24 `D₄` roots, doubled: `±2eᵢ ± 2eⱼ`. -/
def root (i j : Fin 4) (s₁ s₂ : Bool) : Wt :=
  fun t => (if t = i then 2 * sgn s₁ else 0) + (if t = j then 2 * sgn s₂ else 0)

def dot (u w : Wt) : ℤ := ∑ t, u t * w t

/-- Reflection in a root (doubled coordinates: `w − (w·r/4) r`). -/
def refl (r w : Wt) : Wt := fun t => w t - (dot w r / 4) * r t

/-- A wall step keeps the class of the carrier it moves. -/
theorem wallStep_class : ∀ (x : Fin 3) (a : Fin 8) (i j : Fin 4) (s₁ s₂ : Bool), i ≠ j →
    ∃ a' : Fin 8, refl (root i j s₁ s₂) (carrier x a) = carrier x a' := by
  decide

/-- The antipode acts within each class. -/
theorem neg_class : ∀ (x : Fin 3) (a : Fin 8), ∃ a' : Fin 8, -carrier x a = carrier x a' := by
  decide

/-- The antipode fixes no carrier. -/
theorem neg_ne : ∀ (x : Fin 3) (a : Fin 8), -carrier x a ≠ carrier x a := by
  decide

/-- The carriers of a class are distinct. -/
theorem carrier_injective : ∀ (x : Fin 3) (a a' : Fin 8), carrier x a = carrier x a' → a = a' := by
  decide

def M : Fin 4 → Fin 4 → ℤ :=
  ![![1, 1, 1, -1], ![1, 1, -1, 1], ![1, -1, 1, 1], ![1, -1, -1, -1]]

/-- Triality on doubled coordinates. -/
def triality (w : Wt) : Wt := fun r => (∑ t, M r t * w t) / 2

theorem triality_class : ∀ (x : Fin 3) (a : Fin 8),
    ∃ a' : Fin 8, triality (carrier x a) = carrier (x + 1) a' := by
  decide

theorem triality_root : ∀ (i j : Fin 4) (s₁ s₂ : Bool), i ≠ j →
    ∃ (i' j' : Fin 4) (s₁' s₂' : Bool), i' ≠ j' ∧
      triality (root i j s₁ s₂) = root i' j' s₁' s₂' := by
  decide

theorem triality_neg : ∀ (x : Fin 3) (a : Fin 8),
    triality (-carrier x a) = -triality (carrier x a) := by
  decide

/-- The crossing: swap the factors, then apply triality to both. -/
def crossing (p : Wt × Wt) : Wt × Wt := (triality p.2, triality p.1)

/-- Wall T of generation `g` (class `g + 1`) lands on wall F (class `g − 1`), amplitude and label
exchanged between the factors. -/
theorem crossing_walls : ∀ (g : Fin 3) (a b : Fin 8), ∃ a' b' : Fin 8,
    crossing (carrier (g + 1) a, carrier (g + 1) b) = (carrier (g - 1) b', carrier (g - 1) a') := by
  decide

/-- Per generation: `8` amplitude carriers `× 8` labels on each wall. -/
theorem wall_card : Fintype.card (Fin 8 × Fin 8) = 64 := by decide

end PMElementaryParticles.GluedRegister
