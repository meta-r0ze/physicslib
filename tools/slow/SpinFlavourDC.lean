import PMHadrons.SpinFlavour

/-! **Construction (slow kernel check; outside the `src/` library globs).** Check it on its own:
`lake env lean tools/slow/SpinFlavourDC.lean`.

With `G^{ia} = Σ_q σ^i_q τ^a_q / 4` on the 64 three-carrier states (`AxialCount`):

* `dc_full`: the double commutator `Σ_{jb} [G^{jb},[G^{jb}, A]]` of the axial operator over the full
  nucleon + Δ space equals the axial operator between proton and neutron (`R = 4G`, factor `16`).
* `dc_nucleon_only`: with nucleon-only intermediate states it is `25/9 = (5/3)²` times that, so the
  Δ keeps `9/25` of the nucleon-only term cubic in the pion coupling.

Imaginary Pauli matrices are written `σ_y = iK` with `K` real; each `y` factor contributes `i`, so the
double commutator carries `(−1)^{#y}` (`sgn`).
-/

namespace PMHadrons.SpinFlavour
open PMHadrons.AxialCount

/-! ## The double commutator -/

def pX (o i : ℕ) : ℚ := if o ≠ i then 1 else 0
def pK (o i : ℕ) : ℚ := if o = 0 ∧ i = 1 then -1 else if o = 1 ∧ i = 0 then 1 else 0
def pZ (o i : ℕ) : ℚ := if o = i then (if o = 0 then 1 else -1) else 0

/-- Real parts of the Pauli matrices: `σ_x`, `K` (with `σ_y = iK`), `σ_z`. -/
def pauli : ℕ → ℕ → ℕ → ℚ
  | 0 => pX
  | 1 => pK
  | _ => pZ

/-- Spin ⊗ label product on a carrier state `st = 2·spin + label`. -/
def kron2 (S T : ℕ → ℕ → ℚ) (o i : ℕ) : ℚ := S (o / 2) (i / 2) * T (o % 2) (i % 2)

/-- `R^{jb} = Σ_q σ^j_q τ^b_q` with `y` factors replaced by `K` (`= 4G^{jb}` up to `i^{#y}`). -/
def R (j b : ℕ) (v : Vec) : Vec := total (kron2 (pauli j) (pauli b)) v

/-- The axial operator `Σ_q σ_z τ₊`. -/
def A (v : Vec) : Vec := total sigmaTauPlus v

def sgn (j b : ℕ) : ℚ := (if j = 1 then -1 else 1) * (if b = 1 then -1 else 1)

def idx9 : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

/-- `[Q,[Q,X]] v = QQXv − 2QXQv + XQQv`. -/
def dcTerm (X Q : Vec → Vec) (v : Vec) : Vec :=
  vadd (vadd (Q (Q (X v))) (Q (X (Q v))) (-2)) (X (Q (Q v))) 1

/-- `Σ_{jb} [G,[G,A]]` (times 16) on the full space. -/
def dcFull (v : Vec) : Vec :=
  idx9.foldl (fun acc jb => vadd acc (dcTerm A (R jb.1 jb.2) v) (sgn jb.1 jb.2)) zero

/-- **On the full nucleon + Δ space the double commutator is the axial operator** (`16 = 4²`). -/
theorem dc_full : inner proton (dcFull neutron) = 16 * inner proton (A neutron) := by
  decide +kernel

/-! ## Nucleon-only intermediate states -/

/-- `S₋`: spin down, label unchanged. -/
def sMinus (o i : ℕ) : ℚ := if o / 2 = 1 ∧ i / 2 = 0 ∧ o % 2 = i % 2 then 1 else 0

/-- The four nucleon states `p↑, p↓, n↑, n↓` (orthogonal, each of norm `72`). -/
def nucleons : List Vec := [proton, total sMinus proton, neutron, total sMinus neutron]

/-- Projection onto the nucleon states. -/
def projN (v : Vec) : Vec :=
  nucleons.foldl (fun acc b => vadd acc b (inner b v / inner b b)) zero

def dcNucleon (v : Vec) : Vec :=
  idx9.foldl (fun acc jb =>
    vadd acc (dcTerm (fun u => projN (A (projN u))) (fun u => projN (R jb.1 jb.2 (projN u))) v)
      (sgn jb.1 jb.2)) zero

/-- **Nucleon-only intermediate states give `25/9 = (5/3)²` times the full result**, so the Δ keeps
`9/25` of the nucleon-only cubic term. -/
theorem dc_nucleon_only :
    inner proton (dcNucleon neutron) = 25 / 9 * inner proton (dcFull neutron) := by
  decide +kernel

end PMHadrons.SpinFlavour
