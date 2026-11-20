import PMAction.ConfinedAxialCurrent
import PMAction.ChiralityConvention
import PMKAutomaton.Machine.CarrierEvents

/-!
# Carrier admittance on the wire: every conserving exchange is scalar on the reference

`NodeAmplitude`'s `K = 1`, `k = α/2` split carrier exchanges into in-cycle ones (vector class) and
node crossings (spinor classes) by the protocols' axis-`0` test (`PMFlavor.ExchangeAxis`). On the wire
the axes are the Dirac components (`CarrierVacuumSector`: a class-`c` wall state is the odd mode
`ψ(x) = Σᵢ xᵢ φᵢ/√8` of the class's eight carriers, so component `i` is coordinate axis `i` in every
class), and the reference is the second-wall zero mode on axes `2, 3`
(`ChiralityConvention.physicalBackground_apply`). This module redoes the test there.

**A conserving exchange cannot touch the reference.** A single-wall exchange keeps the wall
(commutes with the chirality `Γ`) and is isotropic (commutes with the spin `Σⱼ`,
`ConfinedAxialCurrent.Sigma`). Then:
* `commutant_chiral`: it is `a (1 + Γ)/2 + b (1 − Γ)/2`;
* `scalar_on_reference`: on any state supported on axes `2, 3`, the reference's support, it is
  multiplication by `b`. It rescales the reference and never changes its spin state, so it is a
  gauge-repairable (in-cycle) event for every class. The axis-contact test has no wire analogue,
  and nothing in the exchange's class sends it through the reference node.

**The native exchange is class-blind.** The native class-changing event moves a class-`a` carrier
`x` to a class-`b` carrier `y` by a minimal displacement `y − x` (class `a + b`).
* `uniform_hop`: with unit weight per allowed displacement, its Dirac block
  `Σ_{x,y} y_j x_k [y − x minimal]` is `16 δ_jk` for every ordered pair of distinct classes, that is
  `2 · 1` after the embedding's `1/8`. Every class pair has the same exchange, a scalar, as the
  commutant requires.
* `single_hop_anisotropic`: one fixed displacement (`−2e₀` from the spinor to the conjugate class) is
  not scalar (`diag(−4, 4, 4, 4)`): it singles out an axis, so it is not a conserving wall term.

So exchange amplitudes alone do not separate the classes, and the axis test does not give
`k/K = α/2` on the wire. What separates them is the reference's own class: its stationarity forbids
direct exchange into or out of that class on its wall (`ReferenceClassHop`).
-/

noncomputable section
namespace PMAction.CarrierAdmittance
open Matrix ConcreteFermion CarrierEvents PMSubstrate.Channels
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

/-- The two chiral projectors `(1 ± Γ)/2`, as diagonal matrices. -/
def plus : Spin := !![1,0,0,0; 0,1,0,0; 0,0,0,0; 0,0,0,0]
def minus : Spin := !![0,0,0,0; 0,0,0,0; 0,0,1,0; 0,0,0,1]

/-- **The commutant of the chirality and the spin is `span{(1 + Γ)/2, (1 − Γ)/2}`.** -/
theorem commutant_chiral (X : Spin) (hg : X * gamma = gamma * X)
    (hs : ∀ j, X * ConfinedAxialCurrent.Sigma j = ConfinedAxialCurrent.Sigma j * X) :
    X = X 0 0 • plus + X 2 2 • minus := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [plus, minus, gamma, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, gamma, ConfinedAxialCurrent.Sigma, alpha, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, plus, minus] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (1/2) * congrFun (congrFun (hs 0) 0) 0 + (-Complex.I/2) * congrFun (congrFun (hs 1) 0) 0
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, gamma, ConfinedAxialCurrent.Sigma, alpha, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, plus, minus] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (-1/2) * congrFun (congrFun (hg) 0) 2
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, gamma, ConfinedAxialCurrent.Sigma, alpha, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, plus, minus] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (-1/2) * congrFun (congrFun (hg) 0) 3
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, gamma, ConfinedAxialCurrent.Sigma, alpha, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, plus, minus] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (-1/2) * congrFun (congrFun (hs 0) 0) 0 + (-Complex.I/2) * congrFun (congrFun (hs 1) 0) 0
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, gamma, ConfinedAxialCurrent.Sigma, alpha, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, plus, minus] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (-1) * congrFun (congrFun (hs 0) 0) 1
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, gamma, ConfinedAxialCurrent.Sigma, alpha, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, plus, minus] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (-1/2) * congrFun (congrFun (hg) 1) 2
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, gamma, ConfinedAxialCurrent.Sigma, alpha, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, plus, minus] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (-1/2) * congrFun (congrFun (hg) 1) 3
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, gamma, ConfinedAxialCurrent.Sigma, alpha, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, plus, minus] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (1/2) * congrFun (congrFun (hg) 2) 0
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, gamma, ConfinedAxialCurrent.Sigma, alpha, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, plus, minus] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (1/2) * congrFun (congrFun (hg) 2) 1
  · simp [plus, minus, gamma, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, gamma, ConfinedAxialCurrent.Sigma, alpha, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, plus, minus] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (1/2) * congrFun (congrFun (hs 0) 2) 2 + (-Complex.I/2) * congrFun (congrFun (hs 1) 2) 2
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, gamma, ConfinedAxialCurrent.Sigma, alpha, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, plus, minus] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (1/2) * congrFun (congrFun (hg) 3) 0
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, gamma, ConfinedAxialCurrent.Sigma, alpha, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, plus, minus] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (1/2) * congrFun (congrFun (hg) 3) 1
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, gamma, ConfinedAxialCurrent.Sigma, alpha, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, plus, minus] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (-1/2) * congrFun (congrFun (hs 0) 2) 2 + (-Complex.I/2) * congrFun (congrFun (hs 1) 2) 2
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, gamma, ConfinedAxialCurrent.Sigma, alpha, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, plus, minus] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (-1) * congrFun (congrFun (hs 0) 2) 3

/-- **A conserving exchange multiplies any state on the reference's axes by one number.** -/
theorem scalar_on_reference (X : Spin) (hg : X * gamma = gamma * X)
    (hs : ∀ j, X * ConfinedAxialCurrent.Sigma j = ConfinedAxialCurrent.Sigma j * X)
    (v : Fin 4 → ℂ) (h0 : v 0 = 0) (h1 : v 1 = 0) : X *ᵥ v = X 2 2 • v := by
  rw [commutant_chiral X hg hs]
  ext i
  fin_cases i <;> simp [plus, minus, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec,
    dotProduct, Fin.sum_univ_four, h0, h1]

/-- The reference (`physicalBackground`) has its second-wall support on axes `2, 3`. -/
theorem reference_axes (r : Fin 2 → ℂ) :
    (fun i => ChiralityConvention.physicalBackground r (Sum.inr i)) 0 = 0 ∧
      (fun i => ChiralityConvention.physicalBackground r (Sum.inr i)) 1 = 0 := by
  simp [ChiralityConvention.physicalBackground_apply]

/-- A class change `x ↦ y` by a minimal displacement. -/
def step {a b : Fin 3} (x : Carrier a) (y : Carrier b) : Bool :=
  norm4 (vector y - vector x) = 4

/-- Dirac block of the uniform native exchange from class `a` to class `b`, before the `1/8`. -/
def hopBlock (a b : Fin 3) (j k : Fin 4) : ℤ :=
  ∑ x : Carrier a, ∑ y : Carrier b, if step x y then vector y j * vector x k else 0

/-- **The uniform native exchange is `16 δ_jk` for every pair of distinct classes.** -/
theorem uniform_hop : ∀ (a b : Fin 3), a ≠ b → ∀ j k : Fin 4,
    hopBlock a b j k = if j = k then 16 else 0 := by
  decide +kernel

/-- Dirac block of one fixed displacement `d` from class `a` to class `b`. -/
def singleBlock (a b : Fin 3) (d : Fin 4 → ℤ) (j k : Fin 4) : ℤ :=
  ∑ x : Carrier a, ∑ y : Carrier b,
    if vector y = vector x + d then vector y j * vector x k else 0

/-- **One displacement singles out an axis**: `−2e₀` from the spinor to the conjugate class has
Dirac block `diag(−4, 4, 4, 4)`. -/
theorem single_hop_anisotropic :
    singleBlock 1 2 ![-2, 0, 0, 0] 0 0 = -4 ∧ singleBlock 1 2 ![-2, 0, 0, 0] 1 1 = 4 := by
  decide +kernel

end PMAction.CarrierAdmittance
