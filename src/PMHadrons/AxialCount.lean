import PMSubstrate.E8Values
import Mathlib.Tactic

/-! **Construction (step 1 of `g_A`).** The nucleon's spin-flip count.

`g_A` is how much of a carrier-level spin flip survives as a spin flip of the whole nucleon.
The vector (charge-only) part is protected; the axial (spin-flip) part depends on how the
composite holds spin. Step 1 is the **count**: three carriers, each with a binary spin leg and a
binary `u/d` label, in the composite state the substrate allows. Step 2 (open) is the reduction
from the carriers' confined motion on the `3×3×3` cube.

Inputs, each already in the tree:

* **three carriers** — a colour-neutral baryon holds one carrier of each of the `σ − χ = 3`
  colours (`PMHadrons.Occupancy`: colour neutrality);
* **one bit of spin per carrier** — `PMSubstrate.PersistencePremises.leg_state_binary`;
* **the `u/d` doublet with unit raising/lowering entries** — `PMAction.ChargedCurrent`
  (`raising_entries`, the su(2) doublet algebra);
* **the composite is symmetric in spin ⊗ label** — the colour part of a three-colour singlet is
  antisymmetric, and the carriers are fermions, so the rest is symmetric.

The proton (spin up) is the symmetrization over the six carrier orderings of
`u u d ⊗ (2↑↑↓ − ↑↓↑ − ↓↑↑)`; the neutron is the label-lowering of the proton (`T₋`), so the
two have equal norm (`norms`). Matrix elements of the summed one-carrier operators, by exact
rational computation on the 64 three-carrier states:

* vector `⟨p| Σ τ₊ |n⟩ / ⟨p|p⟩ = 1` (`vector_count`),
* axial `⟨p| Σ σ_z τ₊ |n⟩ / ⟨p|p⟩ = 5/3` (`axial_count`, `axial_ratio`),

and `5/3 = σ/(σ − χ)` (`axial_ratio_eq_invariants`). The measured `g_A = 1.2754` is `0.765`
of this count; that factor is step 2.
-/

namespace PMHadrons.AxialCount

/-- A three-carrier vector: 64 rational amplitudes. Carrier state `st = 2·spin + label`
(`spin 0 = ↑`, `label 0 = u`); carrier `i` sits in base-4 digit `i`. -/
abbrev Vec := List ℚ

def car (x i : ℕ) : ℕ := x / 4 ^ i % 4
def setc (x i a : ℕ) : ℕ := x - car x i * 4 ^ i + a * 4 ^ i
def get (v : Vec) (x : ℕ) : ℚ := v.getD x 0
def zero : Vec := List.replicate 64 0
def vadd (v w : Vec) (c : ℚ) : Vec := List.zipWith (fun a b => a + c * b) v w
def smul (c : ℚ) (v : Vec) : Vec := v.map (c * ·)
def ket3 (a b c : ℕ) : Vec := (List.range 64).map (fun x => if x = a + 4 * b + 16 * c then 1 else 0)
def inner (v w : Vec) : ℚ := (List.zipWith (· * ·) v w).sum

/-- Reorder the carriers: carrier `j` of the result is carrier `p j` of the input. -/
def perm (p : List ℕ) (v : Vec) : Vec :=
  (List.range 64).map fun x =>
    get v (car x (p.getD 0 0) + 4 * car x (p.getD 1 0) + 16 * car x (p.getD 2 0))

/-- A one-carrier operator `M` acting on carrier `i`. -/
def oneBody (M : ℕ → ℕ → ℚ) (i : ℕ) (v : Vec) : Vec :=
  (List.range 64).map fun x =>
    ((List.range 4).map fun a =>
      let coefficient := M (car x i) a
      if coefficient = 0 then 0 else coefficient * get v (setc x i a)).sum

/-- The operator summed over the three carriers. -/
def total (M : ℕ → ℕ → ℚ) (v : Vec) : Vec :=
  (List.range 3).foldl (fun acc i => vadd acc (oneBody M i v) 1) zero

/-- `T₋`: label `u → d`, spin unchanged. -/
def tauMinus (o i : ℕ) : ℚ := if o % 2 = 1 ∧ i % 2 = 0 ∧ o / 2 = i / 2 then 1 else 0
/-- `τ₊`: label `d → u`, spin unchanged (the vector, charge-only, transition). -/
def tauPlus (o i : ℕ) : ℚ := if o % 2 = 0 ∧ i % 2 = 1 ∧ o / 2 = i / 2 then 1 else 0
/-- `σ_z τ₊`: the same transition weighted by the spin (the axial, spin-flip-sensitive part). -/
def sigmaTauPlus (o i : ℕ) : ℚ :=
  if o % 2 = 0 ∧ i % 2 = 1 ∧ o / 2 = i / 2 then (if o / 2 = 0 then 1 else -1) else 0

/-- The six carrier orderings. -/
def orderings : List (List ℕ) := [[0,1,2], [0,2,1], [1,0,2], [1,2,0], [2,0,1], [2,1,0]]

/-- `u u d ⊗ (2↑↑↓ − ↑↓↑ − ↓↑↑)` (states: `u↑ = 0`, `d↑ = 1`, `u↓ = 2`, `d↓ = 3`). -/
def seed : Vec := vadd (vadd (smul 2 (ket3 0 0 3)) (ket3 0 2 1) (-1)) (ket3 2 0 1) (-1)

/-- The proton, spin up: the seed symmetrized over the carrier orderings. -/
def proton : Vec := orderings.foldl (fun acc p => vadd acc (perm p seed) 1) zero

/-- The neutron, spin up: the label-lowering of the proton. -/
def neutron : Vec := total tauMinus proton

theorem norms : inner proton proton = 72 ∧ inner neutron neutron = 72 := by decide +kernel

theorem vector_count : inner proton (total tauPlus neutron) = 72 := by decide +kernel

theorem axial_count : inner proton (total sigmaTauPlus neutron) = 120 := by decide +kernel

/-- **The axial-to-vector count is `5/3`.** -/
theorem axial_ratio :
    inner proton (total sigmaTauPlus neutron) / inner proton (total tauPlus neutron) = 5 / 3 := by
  rw [axial_count, vector_count]; norm_num

/-- `5/3 = σ/(σ − χ)`. -/
theorem axial_ratio_eq_invariants :
    (5 / 3 : ℚ) = (PMSubstrate.E8Values.sigma : ℚ) /
      ((PMSubstrate.E8Values.sigma : ℚ) - PMSubstrate.E8Values.chi) := by
  rw [PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.chi_eq]; norm_num

end PMHadrons.AxialCount
