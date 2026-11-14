import PMConstants.CarrierActions
import Mathlib.Data.Fintype.Perm

/-!
# Why the weak refresh acts uniformly on its sector

`CarrierActions.weak_chiral` takes the minimal refresh among the sector-uniform sign actions. This
module derives the uniformity from the root structure.

A refresh event is a root reflection (`PMAction.Machine.RootMaintenance`). On the vector-class
carriers `±2eᵢ`, a word of D₄ root reflections acts as a signed permutation of the four axes with
an **even** number of sign changes: that is the Weyl group of D₄ (the reflection in `eᵢ − eⱼ` swaps
two axes, the one in `eᵢ + eⱼ` swaps them and flips both signs). Weak is a different factor from
colour, so its refresh commutes with the colour-axis exchanges (`CarrierActions.commute`).

* `signed`: the signed axis permutation `(π, ε)` acting on the carriers.
* `refresh_uniform`: a signed axis permutation with an even number of sign changes that commutes
  with every colour-axis exchange and moves the reference (a carrier on the lepton axis `0`) is the
  sign exchange of every carrier, `signExchange`. Commuting with colour forces the permutation to be
  trivial and the three colour signs to agree; evenness then ties the lepton sign to them.
* `odd_counterexamples`: without evenness, flipping only the lepton axis, or only the three colour
  axes, also commutes with colour; the lepton-only flip moves the reference with support `2`. The D₄
  roots are what exclude them.

So the weak refresh is the sign exchange of the whole sector, the uniformity that `weak_chiral`
assumed.
-/

noncomputable section
namespace PMConstants.WeakUniform
open PMAction.CarrierEvents PMConstants.CarrierRepresentation PMConstants.CarrierActions Finset

/-- Flip the signs of the axes in `ε`. -/
def flipBox (ε : Fin 4 → Bool) (v : V) : Box := fun i => if ε i then (v.1 i).rev else v.1 i

lemma flip_valid : ∀ (ε : Fin 4 → Bool) (v : V), valid 0 (flipBox ε v) := by decide +kernel

def flip (ε : Fin 4 → Bool) : Equiv.Perm V where
  toFun v := ⟨flipBox ε v, flip_valid ε v⟩
  invFun v := ⟨flipBox ε v, flip_valid ε v⟩
  left_inv v := by
    apply Subtype.ext; funext i; by_cases h : ε i <;> simp [flipBox, h]
  right_inv v := by
    apply Subtype.ext; funext i; by_cases h : ε i <;> simp [flipBox, h]

/-- The signed axis permutation `(π, ε)`. -/
def signed (π : Equiv.Perm (Fin 4)) (ε : Fin 4 → Bool) : Equiv.Perm V :=
  (permute 0 π).trans (flip ε)

/-- The hypotheses on a refresh: D₄-even, commuting with colour, moving the reference. -/
def Adm (π : Equiv.Perm (Fin 4)) (ε : Fin 4 → Bool) : Prop :=
  (univ.filter fun i => ε i = true).card % 2 = 0 ∧
    (∀ (a b : Fin 3) (v : V), signed π ε (axisExchange a b v) = axisExchange a b (signed π ε v)) ∧
      ∃ v : V, axis v = 0 ∧ signed π ε v ≠ v

instance (π : Equiv.Perm (Fin 4)) (ε : Fin 4 → Bool) : Decidable (Adm π ε) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The refresh is the sign exchange of the whole sector. -/
def Uni (π : Equiv.Perm (Fin 4)) (ε : Fin 4 → Bool) : Prop := ∀ v : V, signed π ε v = signExchange v

instance (π : Equiv.Perm (Fin 4)) (ε : Fin 4 → Bool) : Decidable (Uni π ε) :=
  inferInstanceAs (Decidable (∀ v : V, signed π ε v = signExchange v))

lemma check : ∀ π ∈ permsOfFinset (univ : Finset (Fin 4)), ∀ ε : Fin 4 → Bool,
    Adm π ε → Uni π ε := by
  decide +kernel

/-- **The weak refresh is uniform.** -/
theorem refresh_uniform (π : Equiv.Perm (Fin 4)) (ε : Fin 4 → Bool)
    (heven : (univ.filter fun i => ε i = true).card % 2 = 0)
    (hc : ∀ (a b : Fin 3) (v : V), signed π ε (axisExchange a b v) = axisExchange a b (signed π ε v))
    (hm : ∃ v : V, axis v = 0 ∧ signed π ε v ≠ v) :
    ∀ v : V, signed π ε v = signExchange v :=
  check π (mem_perms_of_finset_iff.2 fun _ => mem_univ _) ε ⟨heven, hc, hm⟩

/-- Without the D₄ evenness, the lepton-only flip and the colour-only flip also commute with
colour; the lepton-only flip moves the reference and only its sign pair. -/
theorem odd_counterexamples :
    (∀ (a b : Fin 3) (v : V),
      flip ![true, false, false, false] (axisExchange a b v) =
        axisExchange a b (flip ![true, false, false, false] v)) ∧
    (∀ (a b : Fin 3) (v : V),
      flip ![false, true, true, true] (axisExchange a b v) =
        axisExchange a b (flip ![false, true, true, true] v)) ∧
    (univ.filter fun v : V => flip ![true, false, false, false] v ≠ v).card = 2 ∧
    (∃ v : V, axis v = 0 ∧ flip ![true, false, false, false] v ≠ v) := by
  decide +kernel

end PMConstants.WeakUniform
