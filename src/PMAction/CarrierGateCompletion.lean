import PMTransport.Machine.RootTransferPhase
import PMAction.CompletionSelection
import PMTransport.Machine.CarrierWeyl

/-! Identity completion within the carrier permutation gates. The coordinate
embedding separates labels, so changing the root word while retaining its
encoded action cannot change its permutation on the hidden modes. -/
noncomputable section
namespace PMAction.CarrierGateCompletion
open Matrix CarrierEvents CarrierParity CarrierWeyl

variable (c : Fin 3)

private lemma row_injective : Function.Injective (embedding c) := by
  intro v w h
  apply vector_injective c
  funext i
  have he := congrFun h i
  have hn : scale ≠ 0 := by intro hz; have hs := scale_sq; rw [hz] at hs; norm_num at hs
  have hcast := mul_left_cancel₀ hn he
  exact_mod_cast hcast

theorem unique_permutation (e f : Equiv.Perm (Carrier c))
    (h : e.permMatrix ℂ * embedding c = f.permMatrix ℂ * embedding c) : e = f := by
  apply Equiv.ext
  intro v
  apply row_injective c
  funext i
  have he := congrFun (congrFun h v) i
  change (e.permMatrix ℂ *ᵥ fun w => embedding c w i) v =
    (f.permMatrix ℂ *ᵥ fun w => embedding c w i) v at he
  simpa only [permMatrix_mulVec, Function.comp_apply] using he

def KeepsPairs (e : Equiv.Perm (Carrier c)) : Prop :=
  ∀ v, e v = v ∨ e v = antipode c v

instance (e : Equiv.Perm (Carrier c)) : Decidable (KeepsPairs c e) :=
  inferInstanceAs (Decidable (∀ v, e v = v ∨ e v = antipode c v))

private lemma complement_entry (v w : Carrier c) :
    IsometricDynamics.complement (embedding c) v w =
      if w = v ∨ w = antipode c v then (1/2 : ℂ) else 0 := by
  have ha := no_fixed_antipode c v
  simp only [IsometricDynamics.complement, projector, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_some_iff]
  by_cases h : w = v
  · subst w
    norm_num [ha]
  · by_cases h' : w = antipode c v
    · norm_num [h, Ne.symm h, h', ha, Ne.symm ha]
    · norm_num [h, Ne.symm h, h', Ne.symm h']

theorem fixes_even_iff (e : Equiv.Perm (Carrier c)) :
    e.permMatrix ℂ * IsometricDynamics.complement (embedding c) =
      IsometricDynamics.complement (embedding c) ↔ KeepsPairs c e := by
  have entry (v w : Carrier c) :
      (e.permMatrix ℂ * IsometricDynamics.complement (embedding c)) v w =
      IsometricDynamics.complement (embedding c) (e v) w := by
    change (e.permMatrix ℂ *ᵥ _) v = _
    rw [permMatrix_mulVec]
    rfl
  constructor
  · intro h v
    have hv := congrFun (congrFun h v) (e v)
    rw [entry, complement_entry, complement_entry] at hv
    by_contra hn
    simp [hn] at hv
  · intro h
    ext v w
    rw [entry, complement_entry, complement_entry]
    rcases h v with hv | hv
    · rw [hv]
    · simp only [hv, antipode_involutive c v, or_comm]

/-- Exact admission test, allowing all permutations and therefore every root
word. On success the lookup word itself realizes the identity completion. -/
theorem lookup_admission_iff (g : Fin 6) :
    (∃ e : Equiv.Perm (Carrier c), e.permMatrix ℂ =
      IsometricDynamics.extend (embedding c) (complexMatrix g)) ↔ KeepsPairs c (lookup c g) := by
  have agree := CompletionSelection.agreement_iff _ (isometry c) _ _ (intertwining c g)
  constructor
  · rintro ⟨e, he⟩
    have hu : e = lookup c g := unique_permutation c _ _ (by
      rw [he, IsometricDynamics.intertwining _ (isometry c), intertwining])
    exact (fixes_even_iff c _).mp (agree.mp (hu ▸ he))
  · intro h
    exact ⟨_, agree.mpr ((fixes_even_iff c _).mpr h)⟩

/-- Complete classification for the six supplied lookup words in every class.
Index 0 is β and index 5 is the antipode. -/
theorem lookup_table : ∀ c g, KeepsPairs c (lookup c g) ↔
    g = 5 ∨ (c = 0 ∧ (g = 1 ∨ g = 3)) ∨ (c = 1 ∧ g = 0) ∨ (c = 2 ∧ g = 2) := by
  decide +kernel

/-- A single reconstructed involution pulse fixes every even mode exactly at
a phase return, or when the underlying permutation preserves every pair. -/
theorem pulse_fixes_even_iff (e : Equiv.Perm (Carrier c)) (he : Function.Involutive e)
    (p t : ℝ) :
    RootTransferPhase.phase e p t * IsometricDynamics.complement (embedding c) =
      IsometricDynamics.complement (embedding c) ↔
    Complex.exp (-(RootTransferPhase.gap p * t : ℝ) * Complex.I) = 1 ∨ KeepsPairs c e := by
  let z := Complex.exp (-(RootTransferPhase.gap p * t : ℝ) * Complex.I)
  let P := IsometricDynamics.complement (embedding c)
  rw [← fixes_even_iff, RootTransferPhase.phase_formula _ he]
  change (InvolutionSpectral.plus _ + z • InvolutionSpectral.minus _) * P = P ↔
    z = 1 ∨ e.permMatrix ℂ * P = P
  simp only [InvolutionSpectral.plus, InvolutionSpectral.minus, Matrix.add_mul,
    Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul]
  constructor
  · intro h
    by_cases hz : z = 1
    · exact Or.inl hz
    · right
      ext i j
      have hentry := congrFun (congrFun h i) j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at hentry
      apply sub_eq_zero.mp
      apply (mul_eq_zero.mp (_ : (z - 1) * ((e.permMatrix ℂ * P) i j - P i j) = 0)).resolve_left
        (sub_ne_zero.mpr hz)
      linear_combination -2 * hentry
  · rintro (h | h)
    · rw [h, one_smul]
      module
    · rw [h, sub_self, smul_zero, smul_zero, add_zero]
      module

/-- Every primitive simple reflection moves an antipodal pair in every class. -/
theorem simple_moves_pair : ∀ c j, ¬ KeepsPairs c (simple c j) := by decide +kernel

/-- For a non-returning β pulse the identity action on the complement is
realized exactly in class 1. No clock calibration is needed for the test. -/
theorem beta_pulse (p t : ℝ)
    (hz : Complex.exp (-(RootTransferPhase.gap p * t : ℝ) * Complex.I) ≠ 1) :
    RootTransferPhase.phase (lookup c 0) p t * IsometricDynamics.complement (embedding c) =
      IsometricDynamics.complement (embedding c) ↔ c = 1 := by
  have invol : ∀ d : Fin 3, Function.Involutive (lookup d 0) := by
    change ∀ d v, lookup d 0 (lookup d 0 v) = v
    decide +kernel
  rw [pulse_fixes_even_iff c _ (invol c), lookup_table]
  rw [or_iff_right hz]
  simp

end PMAction.CarrierGateCompletion
