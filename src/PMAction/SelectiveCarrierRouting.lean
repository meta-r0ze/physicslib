import PMAction.CompletedCarrierPhase
import PMAction.LocalIsometricDynamics

/-!
# The spatial split as one selective route and an on-site root echo

For the split coefficient C = (beta + i alpha_j)/2, P = C beta is an
orthogonal projector. Routing P along a supplied spatial permutation and leaving
its complement at rest conjugates on-site beta into the required neighbour
generator. The completed carrier realization has the same all-state coordinate
readout and restores every even mode after the full step.

The selector is an explicit completed internal root circuit. Applying the
spatial permutation conditionally on its spectral projector is still a joint
routing control, not supplied by on-site roots or an unconditioned shuffle.
The factorization isolates this physical admission premise. It selects neither
the spatial permutation nor the update clock, primitive prices or wall crossing.
-/
noncomputable section
namespace PMAction.SelectiveCarrierRouting
open Matrix CarrierEvents CarrierParity RootCliffordCompletion
open scoped Kronecker Matrix.Norms.Operator

/-- The outgoing part of the existing nilpotent link. -/
def P (j : Fin 3) := LocalUnitary.coefficient j * ConcreteFermion.beta

set_option maxHeartbeats 1500000 in
lemma projector_relations (j : Fin 3) :
    (P j)ᴴ = P j ∧ P j * P j = P j ∧
      P j * ConcreteFermion.beta * P j = 0 ∧
      P j * ConcreteFermion.beta = LocalUnitary.coefficient j ∧
      ConcreteFermion.beta * P j = (LocalUnitary.coefficient j)ᴴ := by
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals fin_cases j <;> ext i k <;> fin_cases i <;> fin_cases k <;>
    norm_num [P, LocalUnitary.coefficient, ConcreteFermion.beta, ConcreteFermion.alpha,
      mul_apply, conjTranspose_apply, Fin.sum_univ_four]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq, map_ofNat]

lemma beta_split (j : Fin 3) :
    LocalUnitary.coefficient j + (LocalUnitary.coefficient j)ᴴ = ConcreteFermion.beta := by
  simp only [LocalUnitary.coefficient, conjTranspose_add, conjTranspose_smul,
    ConcreteFermion.beta_hermitian.eq, (ConcreteFermion.alpha_hermitian j).eq]
  simp
  module

def selector (c : Fin 3) (p : ℝ) (j : Fin 3) :=
  CompletedCarrierPhase.phaseI c p * CompletedCarrierPhase.reflection c p (.alpha j) *
    CompletedCarrierPhase.reflection c p .beta

lemma selector_completed (c : Fin 3) (p : ℝ) (j : Fin 3) (hp : 0 < p) (hp1 : p < 1/2) :
    selector c p j = IsometricDynamics.extend (embedding c)
      (Complex.I • (ConcreteFermion.alpha j * ConcreteFermion.beta)) := by
  rw [selector, CompletedCarrierPhase.phase_completed c p hp hp1,
    CompletedCarrierPhase.reflection_completed c p (.alpha j) hp hp1,
    CompletedCarrierPhase.reflection_completed c p .beta hp hp1,
    ← IsometricDynamics.extend_mul _ (isometry c), ← IsometricDynamics.extend_mul _ (isometry c)]
  simp only [coordinate, Matrix.smul_mul, Matrix.one_mul]

def nativeP (c : Fin 3) (j : Fin 3) := IsometricDynamics.extend (embedding c) (P j)

/-- The selective projector is the positive spectral half of the constructed
internal selector; admitting a controlled spatial route is an additional step. -/
theorem native_projector_from_selector (c : Fin 3) (p : ℝ) (j : Fin 3)
    (hp : 0 < p) (hp1 : p < 1/2) :
    nativeP c j = (1/2 : ℂ) • (1 + selector c p j) := by
  rw [selector_completed c p j hp hp1]
  have hP : P j = (1/2 : ℂ) • (1 + Complex.I • (ConcreteFermion.alpha j * ConcreteFermion.beta)) := by
    simp only [P, LocalUnitary.coefficient, Matrix.add_mul, Matrix.smul_mul,
      ConcreteFermion.beta_square, smul_add, smul_smul]
    module
  rw [nativeP, hP]
  simp only [IsometricDynamics.extend, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
    Matrix.mul_one, Matrix.add_mul, smul_add, smul_smul, IsometricDynamics.complement, Matrix.mul_assoc]
  module

lemma native_projector_relations (c : Fin 3) (j : Fin 3) :
    (nativeP c j)ᴴ = nativeP c j ∧ nativeP c j * nativeP c j = nativeP c j := by
  constructor
  · rw [nativeP, IsometricDynamics.extend_star, (projector_relations j).1]
  · rw [nativeP, ← IsometricDynamics.extend_mul _ (isometry c), (projector_relations j).2.1]

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A joint spatial/internal control, with its admission intentionally explicit. -/
def route {a : Type*} [Fintype a] [DecidableEq a] (e : Equiv.Perm X) (Q : Matrix a a ℂ) :=
  e.permMatrix ℂ ⊗ₖ Q + (1 : Matrix X X ℂ) ⊗ₖ (1-Q)

lemma route_unitary {a : Type*} [Fintype a] [DecidableEq a]
    (e : Equiv.Perm X) (Q : Matrix a a ℂ) (hstar : Qᴴ = Q) (hQ : Q*Q = Q) :
    route e Q ∈ unitary (Matrix (X × a) (X × a) ℂ) := by
  have hp : (1-Q)*Q = 0 := by rw [sub_mul, Matrix.one_mul, hQ, sub_self]
  have hq : Q*(1-Q) = 0 := by rw [mul_sub, Matrix.mul_one, hQ, sub_self]
  have hqq : (1-Q)*(1-Q) = 1-Q := by
    rw [mul_sub, Matrix.mul_one, hp, sub_zero]
  have hu : (e.permMatrix ℂ)ᴴ * e.permMatrix ℂ = 1 := by
    simp [conjTranspose_permMatrix, ← permMatrix_mul]
  have hv : e.permMatrix ℂ * (e.permMatrix ℂ)ᴴ = 1 := by
    simp [conjTranspose_permMatrix, ← permMatrix_mul]
  constructor <;> change _ = (1 : Matrix (X × a) (X × a) ℂ)
  all_goals simp only [route, star_eq_conjTranspose, conjTranspose_add, conjTranspose_kronecker,
    conjTranspose_sub, conjTranspose_one, hstar, add_mul, mul_add, ← mul_kronecker_mul,
    hu, hv, Matrix.one_mul, Matrix.mul_one, hp, hq, hQ, hqq, kronecker_zero, add_zero, zero_add,
    ← kronecker_add, add_sub_cancel, one_kronecker_one]

lemma route_beta (e : Equiv.Perm X) (j : Fin 3) :
    route e (P j) * ((1 : Matrix X X ℂ) ⊗ₖ ConcreteFermion.beta) * (route e (P j))ᴴ =
      LocalUnitary.neighbor e j := by
  obtain ⟨hstar,hP,hzero,hleft,hright⟩ := projector_relations j
  have ha : P j * ConcreteFermion.beta * (1-P j) = LocalUnitary.coefficient j := by
    rw [mul_sub, Matrix.mul_one, hzero, sub_zero, hleft]
  have hb : (1-P j) * ConcreteFermion.beta * P j = (LocalUnitary.coefficient j)ᴴ := by
    calc
      _ = ConcreteFermion.beta * P j - P j * ConcreteFermion.beta * P j := by noncomm_ring
      _ = _ := by rw [hzero, sub_zero, hright]
  have hc : (1-P j) * ConcreteFermion.beta * (1-P j) = 0 := by
    calc
      _ = ConcreteFermion.beta - P j * ConcreteFermion.beta - ConcreteFermion.beta * P j +
          P j * ConcreteFermion.beta * P j := by noncomm_ring
      _ = 0 := by rw [hzero, hleft, hright, ← beta_split j]; abel
  simp only [route, LocalUnitary.neighbor, conjTranspose_add, conjTranspose_kronecker,
    conjTranspose_sub, conjTranspose_one, hstar, add_mul, mul_add, ← mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one, hzero, ha, hb, hc, kronecker_zero, zero_add, add_zero]
  abel

def nativeRoute (c : Fin 3) (e : Equiv.Perm X) (j : Fin 3) := route e (nativeP c j)

lemma nativeRoute_observed (c : Fin 3) (e : Equiv.Perm X) (j : Fin 3) :
    NativeObservation.Obs (LocalIsometricDynamics.encoding (X := X) (embedding c))
      (nativeRoute c e j) (route e (P j)) := by
  have hP : NativeObservation.Obs (embedding c) (nativeP c j) (P j) := by
    refine ⟨IsometricDynamics.intertwining _ (isometry c) _, ?_⟩
    simp [nativeP, IsometricDynamics.extend, Matrix.mul_add, ← Matrix.mul_assoc, isometry,
      IsometricDynamics.complement_right]
  exact NativeObservation.add (NativeObservation.kron (e.permMatrix ℂ) hP)
    (NativeObservation.kron 1 (NativeObservation.sub NativeObservation.one hP))

lemma nativeRoute_unitary (c : Fin 3) (e : Equiv.Perm X) (j : Fin 3) :
    nativeRoute c e j ∈ unitary (Matrix (X × Carrier c) (X × Carrier c) ℂ) :=
  route_unitary e _ (native_projector_relations c j).1 (native_projector_relations c j).2

/-- The on-site identity completion commutes with placing that circuit at every site. -/
lemma onsite_completion {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (E : Matrix a b ℂ) (U : Matrix b b ℂ) :
    IsometricDynamics.extend (LocalIsometricDynamics.encoding (X := X) E)
      ((1 : Matrix X X ℂ) ⊗ₖ U) = (1 : Matrix X X ℂ) ⊗ₖ IsometricDynamics.extend E U := by
  rw [IsometricDynamics.extend, LocalIsometricDynamics.complement_encoding]
  simp only [LocalIsometricDynamics.encoding, conjTranspose_kronecker, conjTranspose_one,
    ← mul_kronecker_mul, Matrix.one_mul, ← kronecker_add]
  rfl

/-- The native spatial program: selective route, on-site root echo, inverse route. -/
def step (c : Fin 3) (p : ℝ) (e : Equiv.Perm X) (j : Fin 3) (t : ℝ) :=
  nativeRoute c e j * ((1 : Matrix X X ℂ) ⊗ₖ ClassBlindFlip.pulse c p t) * (nativeRoute c e j)ᴴ

/-- Exact spatial matrix factorization. Executing it still requires physical
admission of the selective route. -/
theorem step_completed (c : Fin 3) (p : ℝ) (e : Equiv.Perm X) (j : Fin 3) (t : ℝ)
    (hp : 0 < p) (hp1 : p < 1/2) :
    step c p e j t = LocalIsometricDynamics.completion (embedding c)
      (LocalUnitary.step e j (RootTransferPhase.gap p*t)) := by
  have hu : route e (P j) * (route e (P j))ᴴ = 1 :=
    (route_unitary e _ (projector_relations j).1 (projector_relations j).2.1).2
  rw [step, ClassBlindFlip.pulse_completed c p t hp hp1, ← onsite_completion,
    PairedRootFlip.conjugate_completion _ _ _ _ (nativeRoute_observed c e j) (nativeRoute_unitary c e j)]
  have hk : (1 : Matrix X X ℂ) ⊗ₖ LocalUnitary.rotation ConcreteFermion.beta (RootTransferPhase.gap p*t) =
      LocalUnitary.rotation ((1 : Matrix X X ℂ) ⊗ₖ ConcreteFermion.beta) (RootTransferPhase.gap p*t) := by
    simp [LocalUnitary.rotation, kronecker_add, kronecker_smul]
  rw [hk, CompletedCarrierPhase.rotation_conjugate _ _ hu, route_beta]
  rfl

theorem step_unitary (c : Fin 3) (p : ℝ) (e : Equiv.Perm X) (j : Fin 3) (t : ℝ)
    (hp : 0 < p) (hp1 : p < 1/2) : step c p e j t ∈ unitary _ := by
  rw [step_completed c p e j t hp hp1]
  exact LocalIsometricDynamics.unitary _ (isometry c) _ (LocalUnitary.step_unitary e j _)

theorem step_fixes_even (c : Fin 3) (p : ℝ) (e : Equiv.Perm X) (j : Fin 3) (t : ℝ)
    (hp : 0 < p) (hp1 : p < 1/2) :
    step c p e j t * IsometricDynamics.complement
      (LocalIsometricDynamics.encoding (X := X) (embedding c)) =
      IsometricDynamics.complement (LocalIsometricDynamics.encoding (X := X) (embedding c)) := by
  rw [step_completed c p e j t hp hp1]
  simp only [LocalIsometricDynamics.completion, IsometricDynamics.extend, Matrix.add_mul,
    Matrix.mul_assoc, IsometricDynamics.complement_right _
      (LocalIsometricDynamics.encoding_isometry _ (isometry c)), Matrix.mul_zero, zero_add,
    IsometricDynamics.complement_square _ (LocalIsometricDynamics.encoding_isometry _ (isometry c))]

/-- The route itself translates the even modes; the complete echo restores them.
Their intermediate motion must therefore be included in the control ledger. -/
theorem route_even (c : Fin 3) (e : Equiv.Perm X) (j : Fin 3) :
    nativeRoute c e j * ((1 : Matrix X X ℂ) ⊗ₖ IsometricDynamics.complement (embedding c)) =
      e.permMatrix ℂ ⊗ₖ IsometricDynamics.complement (embedding c) := by
  have hP : nativeP c j * IsometricDynamics.complement (embedding c) =
      IsometricDynamics.complement (embedding c) := completed_fixes_even c _
  have hQ : (1-nativeP c j) * IsometricDynamics.complement (embedding c) = 0 := by
    rw [sub_mul, Matrix.one_mul, hP, sub_self]
  simp only [nativeRoute, route, Matrix.add_mul, ← mul_kronecker_mul,
    Matrix.mul_one, hP, hQ, kronecker_zero, add_zero]

/-- Exact all-state observation, including arbitrary even backgrounds. -/
theorem step_readout (c : Fin 3) (p : ℝ) (e : Equiv.Perm X) (j : Fin 3) (t : ℝ)
    (hp : 0 < p) (hp1 : p < 1/2) :
    (LocalIsometricDynamics.encoding (X := X) (embedding c))ᴴ * step c p e j t =
      LocalUnitary.step e j (RootTransferPhase.gap p*t) *
        (LocalIsometricDynamics.encoding (X := X) (embedding c))ᴴ := by
  rw [step_completed c p e j t hp hp1]
  exact LocalIsometricDynamics.readout _ (isometry c) _

/-- The complete native program has exactly the existing neighbour support bound. -/
theorem step_supported (c : Fin 3) (p : ℝ) (e : Equiv.Perm X) (j : Fin 3) (t : ℝ)
    (hp : 0 < p) (hp1 : p < 1/2) :
    ∀ x y v w, ¬ SplitUpdate.Near e x y → step c p e j t (x,v) (y,w) = 0 := by
  rw [step_completed c p e j t hp hp1]
  apply LocalIsometricDynamics.support _ _ (SplitUpdate.Near e) (fun _ => Or.inl rfl)
  intro x y i k hn
  have hx : x ≠ y := fun h => hn (Or.inl h.symm)
  have hp' : e x ≠ y := fun h => hn (Or.inr (Or.inl h.symm))
  have hm : e.symm x ≠ y := fun h => hn (Or.inr (Or.inr h.symm))
  simp [LocalUnitary.step, LocalUnitary.rotation, LocalUnitary.neighbor, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, hx, hp', hm, conjTranspose_permMatrix, Prod.ext_iff]

omit [Fintype X] in
/-- The inverse uses the same selector and reverses the supplied spatial route. -/
theorem nativeRoute_adjoint (c : Fin 3) (e : Equiv.Perm X) (j : Fin 3) :
    (nativeRoute c e j)ᴴ = nativeRoute c e.symm j := by
  simp only [nativeRoute, route, conjTranspose_add, conjTranspose_kronecker,
    conjTranspose_sub, conjTranspose_one, (native_projector_relations c j).1,
    conjTranspose_permMatrix]
  rfl

/-- A net update which reads only one designated spatial source at each site. -/
def SingleSource {a : Type*} (A : Matrix (X × a) (X × a) ℂ) (f : X → X) : Prop :=
  ∀ x y i k, y ≠ f x → A (x,i) (y,k) = 0

/-- Arbitrarily many unconditioned shuffles interspersed with on-site controls
still have one spatial source at each output site. -/
lemma singleSource_mul {a : Type*} [Fintype a]
    (A B : Matrix (X × a) (X × a) ℂ) (f g : X → X)
    (ha : SingleSource A f) (hb : SingleSource B g) : SingleSource (A*B) (g ∘ f) := by
  intro x y i k hn
  simp only [mul_apply]
  apply Finset.sum_eq_zero
  rintro ⟨z,l⟩ _
  by_cases hz : z = f x
  · rw [hb z y l k (by simpa only [hz, Function.comp_apply] using hn), mul_zero]
  · rw [ha x z i l hz, zero_mul]

omit [Fintype X] in
lemma shuffle_singleSource {a : Type*} (e : Equiv.Perm X) (U : Matrix a a ℂ) :
    SingleSource (e.permMatrix ℂ ⊗ₖ U) e := by
  intro x y i k hn
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Ne.symm hn]

/-- A nontrivial spatial direction has a nonzero self-read and neighbour-read
in the same output row. This witnesses why a selective control is necessary. -/
lemma two_sources (j : Fin 3) (t : ℝ) :
    LocalUnitary.step (finRotate 5) j t (0,0) (0,0) = (Real.cos t : ℂ) ∧
      LocalUnitary.step (finRotate 5) j t (0,0) (1,2) = Complex.I*(Real.sin t : ℂ)/2 := by
  have hneg : (-1 : Fin 5) ≠ 1 := by decide
  constructor <;> fin_cases j <;>
    norm_num [LocalUnitary.step, LocalUnitary.rotation, LocalUnitary.neighbor,
      LocalUnitary.coefficient, ConcreteFermion.beta, ConcreteFermion.alpha,
      kronecker_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      conjTranspose_permMatrix, finRotate_apply, finRotate_symm_apply, hneg]
  all_goals ring

/-- A spatial source cannot be chosen independently of the internal state for
this split, even allowing arbitrary one-source functions and internal controls. -/
theorem no_single_source (j : Fin 3) (t : ℝ) (hs : Real.sin t ≠ 0) (hc : Real.cos t ≠ 0)
    (f : Fin 5 → Fin 5) : ¬ SingleSource (LocalUnitary.step (finRotate 5) j t) f := by
  intro h
  by_cases hf : f 0 = 0
  · have hz := h 0 1 0 2 (by simp [hf])
    rw [(two_sources j t).2] at hz
    exact (div_ne_zero (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hs)) (by norm_num)) hz
  · have hz := h 0 0 0 0 (Ne.symm hf)
    rw [(two_sources j t).1] at hz
    exact hc (by exact_mod_cast hz)

/-- A site-local readout cannot turn one spatial source into several, even if
all unobserved carrier modes were used by the ambient internal controls. -/
lemma singleSource_readout {a b : Type*} [Fintype a] [Fintype b]
    (E : Matrix a b ℂ) (A : Matrix (X × a) (X × a) ℂ) (f : X → X)
    (ha : SingleSource A f) :
    SingleSource ((LocalIsometricDynamics.encoding (X := X) E)ᴴ * A *
      LocalIsometricDynamics.encoding (X := X) E) f := by
  intro x y i k hn
  have hentry := LocalIsometricDynamics.sandwich_entry Eᴴ A x y i k
  simp only [LocalIsometricDynamics.encoding, conjTranspose_kronecker,
    conjTranspose_one, conjTranspose_conjTranspose] at hentry ⊢
  rw [hentry]
  simp [ha x y _ _ hn]

/-- Using extra even amplitudes does not avoid the obstruction: every ambient
realization with this all-state readout still needs more than one spatial source. -/
theorem no_single_source_realization (c : Fin 3) (j : Fin 3) (t : ℝ)
    (hs : Real.sin t ≠ 0) (hc : Real.cos t ≠ 0)
    (A : Matrix (Fin 5 × Carrier c) (Fin 5 × Carrier c) ℂ) (f : Fin 5 → Fin 5)
    (hreadout : (LocalIsometricDynamics.encoding (X := Fin 5) (embedding c))ᴴ * A =
      LocalUnitary.step (finRotate 5) j t *
        (LocalIsometricDynamics.encoding (X := Fin 5) (embedding c))ᴴ) :
    ¬ SingleSource A f := by
  intro hA
  have he : (LocalIsometricDynamics.encoding (X := Fin 5) (embedding c))ᴴ * A *
      LocalIsometricDynamics.encoding (X := Fin 5) (embedding c) =
        LocalUnitary.step (finRotate 5) j t := by
    rw [hreadout, Matrix.mul_assoc,
      LocalIsometricDynamics.encoding_isometry _ (isometry c), Matrix.mul_one]
  have h := singleSource_readout (embedding c) A f hA
  rw [he] at h
  exact no_single_source j t hs hc f h

end PMAction.SelectiveCarrierRouting
