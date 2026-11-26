import PMKAutomaton.Machine.ClockRing

/-!
# An aligned D4 and the clock signatures of the E8 glue cosets

`ClockRing` defines the E8 roots and the clock reading. This module fixes one
aligned placement of a spacetime `D4`, proves the placement data, and certifies
the clock signatures of the three `D4` glue cosets.

The simple system used here is

* `a`, `b`, `c`, `beta` from the base-13 codes of `ClockRing.ofCode`;
* `b` is the central node: `<a,b> = <b,c> = <b,beta> = -1`, all other pairs
  orthogonal.

The roots orthogonal to all four simple roots form the internal `D4`. The
remaining clock-silent roots form the spacetime `D4`. Its twelve roots that
pair trivially with the clock plane are the slice roots; the other twelve are
the clock-axis roots.

The coset key is

`glueKey r = ((<r,a> + <r,c>) mod 2, (<r,a> + <r,beta>) mod 2)`.

It is linear, vanishes on both `D4`s, and its three nonzero values are the
vector, spinor and conjugate-spinor cosets. The theorem names for the counts
are `vectorRoots_counts`, `spinorRoots_counts`, `conjugateSpinorRoots_counts`,
and the total decompositions are `plus_total`, `minus_total`, `silent_total`.

The equal-weight step orbit is certified in `PMKAutomaton.ClockTickWeights`.
What remains numerical or an input: the robustness across the ten aligned
placements and the choice of reference class. The alignment itself is one
certified placement, not a proof that it is selected.
-/

namespace PMKAutomaton.ClockAlignment

open PMKAutomaton.ClockRing
open PMSubstrate

/-- First simple root of the aligned spacetime D4. -/
def a : V := ofCode 266246023

/-- Central node of the aligned spacetime D4. -/
def b : V := ofCode 470613877

/-- Third simple root of the aligned spacetime D4. -/
def c : V := ofCode 412692169

/-- Fourth simple root of the aligned spacetime D4. -/
def beta : V := ofCode 413496453

theorem a_mem : a ∈ rootList := by decide +kernel
theorem b_mem : b ∈ rootList := by decide +kernel
theorem c_mem : c ∈ rootList := by decide +kernel
theorem beta_mem : beta ∈ rootList := by decide +kernel

theorem pair_a_b : PMSubstrate.Lattices.pairing a b = -1 := by decide +kernel
theorem pair_b_c : PMSubstrate.Lattices.pairing b c = -1 := by decide +kernel
theorem pair_b_beta : PMSubstrate.Lattices.pairing b beta = -1 := by decide +kernel
theorem pair_a_c : PMSubstrate.Lattices.pairing a c = 0 := by decide +kernel
theorem pair_a_beta : PMSubstrate.Lattices.pairing a beta = 0 := by decide +kernel
theorem pair_c_beta : PMSubstrate.Lattices.pairing c beta = 0 := by decide +kernel

/-- The property of being orthogonal to the four aligned simple roots. -/
def internalProp (r : V) : Prop :=
  PMSubstrate.Lattices.pairing r a = 0 ∧ PMSubstrate.Lattices.pairing r b = 0 ∧ PMSubstrate.Lattices.pairing r c = 0 ∧ PMSubstrate.Lattices.pairing r beta = 0

instance (r : V) : Decidable (internalProp r) := by
  unfold internalProp
  infer_instance

/-- The internal `D4`: the roots orthogonal to the spacetime simple system. -/
def internalRoots : List V := rootList.filter fun r => internalProp r

theorem internalRoots_length : internalRoots.length = 24 := by decide +kernel

/-- No internal `D4` root is clock-silent. Its readings are one `+1`, one `-1`,
and twenty-two other nonzero classes of `ZMod 43`. -/
theorem internalRoots_not_silent : ∀ r ∈ internalRoots, clockReading r ≠ 0 := by
  decide +kernel

/-- The `D4` glue key: the two parity invariants of the four-root system. -/
def glueKey (r : V) : ZMod 2 × ZMod 2 :=
  (((PMSubstrate.Lattices.pairing r a + PMSubstrate.Lattices.pairing r c : ℤ) : ZMod 2),
    ((PMSubstrate.Lattices.pairing r a + PMSubstrate.Lattices.pairing r beta : ℤ) : ZMod 2))

/-- The glue key is additive. -/
theorem glueKey_add (r s : V) :
    glueKey (r + s) = glueKey r + glueKey s := by
  ext <;> simp [glueKey, pair_add_left] <;> ring

/-- The spacetime `D4` is the kernel of the glue key away from the internal
`D4`. -/
def spacetimeProp (r : V) : Prop := glueKey r = 0 ∧ ¬ internalProp r

instance (r : V) : Decidable (spacetimeProp r) := by
  unfold spacetimeProp
  infer_instance

def spacetimeRoots : List V := rootList.filter fun r => spacetimeProp r

theorem spacetimeRoots_length : spacetimeRoots.length = 24 := by decide +kernel

/-- The slice roots are the spacetime roots orthogonal to the clock plane. -/
def sliceRoots : List V :=
  spacetimeRoots.filter fun r =>
    PMSubstrate.Lattices.pairing r ClockPlane.cu = 0 ∧ PMSubstrate.Lattices.pairing r ClockPlane.cv = 0

theorem sliceRoots_length : sliceRoots.length = 12 := by decide +kernel

/-- Every slice root is clock-silent. -/
theorem sliceRoots_silent : ∀ r ∈ sliceRoots, clockReading r = 0 := by
  decide +kernel

theorem sliceRoots_silent_count :
    (sliceRoots.filter fun r => clockReading r = 0).length = 12 := by
  decide +kernel

/-- The other twelve spacetime roots are the clock-axis roots. -/
def clockAxisRoots : List V :=
  spacetimeRoots.filter fun r =>
    ¬ (PMSubstrate.Lattices.pairing r ClockPlane.cu = 0 ∧ PMSubstrate.Lattices.pairing r ClockPlane.cv = 0)

theorem clockAxisRoots_length : clockAxisRoots.length = 12 := by decide +kernel

/-- Six clock-axis roots advance the reading by `+1` and six by `-1`. -/
theorem clockAxisRoots_counts :
    (clockAxisRoots.filter fun r => clockReading r = 1).length = 6 ∧
      (clockAxisRoots.filter fun r => clockReading r = -1).length = 6 := by
  decide +kernel

/-- The roots of a fixed nonzero glue class. -/
def rootsOfKey (k : ZMod 2 × ZMod 2) : List V :=
  rootList.filter fun r => glueKey r = k

theorem vectorRoots_length : (rootsOfKey (0, 1)).length = 64 := by decide +kernel
theorem spinorRoots_length : (rootsOfKey (1, 1)).length = 64 := by decide +kernel
theorem conjugateSpinorRoots_length : (rootsOfKey (1, 0)).length = 64 := by
  decide +kernel

/-- The vector coset has seven `+1` roots, seven `-1` roots, and two silent
roots. -/
theorem vectorRoots_counts :
    ((rootsOfKey (0, 1)).filter fun r => clockReading r = 1).length = 7 ∧
      ((rootsOfKey (0, 1)).filter fun r => clockReading r = -1).length = 7 ∧
      ((rootsOfKey (0, 1)).filter fun r => clockReading r = 0).length = 2 := by
  decide +kernel

/-- The spinor coset has four `+1` roots, four `-1` roots, and no silent root. -/
theorem spinorRoots_counts :
    ((rootsOfKey (1, 1)).filter fun r => clockReading r = 1).length = 4 ∧
      ((rootsOfKey (1, 1)).filter fun r => clockReading r = -1).length = 4 ∧
      ((rootsOfKey (1, 1)).filter fun r => clockReading r = 0).length = 0 := by
  decide +kernel

/-- The conjugate-spinor coset has four `+1` roots, four `-1` roots, and eight
silent roots. -/
theorem conjugateSpinorRoots_counts :
    ((rootsOfKey (1, 0)).filter fun r => clockReading r = 1).length = 4 ∧
      ((rootsOfKey (1, 0)).filter fun r => clockReading r = -1).length = 4 ∧
      ((rootsOfKey (1, 0)).filter fun r => clockReading r = 0).length = 8 := by
  decide +kernel

/-- The clock root and its negative lie in the vector coset. -/
theorem cu_key : glueKey ClockPlane.cu = (0, 1) := by decide +kernel
theorem neg_cu_key : glueKey (-ClockPlane.cu) = (0, 1) := by decide +kernel

/-- The internal `D4` contributes one `+1` root and one `-1` root. -/
theorem internalRoots_tick_counts :
    (internalRoots.filter fun r => clockReading r = 1).length = 1 ∧
      (internalRoots.filter fun r => clockReading r = -1).length = 1 ∧
      (internalRoots.filter fun r => clockReading r = 0).length = 0 := by
  decide +kernel

/-- The per-class counts add up to the clock's `+1` total: six clock-axis roots,
one internal root, and seven, four and four from the three glue cosets. -/
theorem plus_total :
    (clockAxisRoots.filter fun r => clockReading r = 1).length +
        (internalRoots.filter fun r => clockReading r = 1).length +
        ((rootsOfKey (0, 1)).filter fun r => clockReading r = 1).length +
        ((rootsOfKey (1, 1)).filter fun r => clockReading r = 1).length +
        ((rootsOfKey (1, 0)).filter fun r => clockReading r = 1).length = 22 := by
  rw [clockAxisRoots_counts.1, internalRoots_tick_counts.1, vectorRoots_counts.1,
    spinorRoots_counts.1, conjugateSpinorRoots_counts.1]

/-- The per-class counts add up to the clock's `-1` total. -/
theorem minus_total :
    (clockAxisRoots.filter fun r => clockReading r = -1).length +
        (internalRoots.filter fun r => clockReading r = -1).length +
        ((rootsOfKey (0, 1)).filter fun r => clockReading r = -1).length +
        ((rootsOfKey (1, 1)).filter fun r => clockReading r = -1).length +
        ((rootsOfKey (1, 0)).filter fun r => clockReading r = -1).length = 22 := by
  rw [clockAxisRoots_counts.2, internalRoots_tick_counts.2.1, vectorRoots_counts.2.1,
    spinorRoots_counts.2.1, conjugateSpinorRoots_counts.2.1]

/-- The per-class counts add up to the clock's silent total: twelve slice roots,
none internal, and two, zero and eight from the three glue cosets. -/
theorem silent_total :
    (sliceRoots.filter fun r => clockReading r = 0).length +
        (internalRoots.filter fun r => clockReading r = 0).length +
        ((rootsOfKey (0, 1)).filter fun r => clockReading r = 0).length +
        ((rootsOfKey (1, 1)).filter fun r => clockReading r = 0).length +
        ((rootsOfKey (1, 0)).filter fun r => clockReading r = 0).length = 22 := by
  rw [sliceRoots_silent_count, internalRoots_tick_counts.2.2, vectorRoots_counts.2.2,
    spinorRoots_counts.2.2, conjugateSpinorRoots_counts.2.2]

end PMKAutomaton.ClockAlignment
