import PMKAutomaton.Machine.CarrierWeyl
import PMKAutomaton.Machine.CarrierVacuumEvolution

/-!
# The four even modes of the actual vector-class carriers

The eight vector carriers have four antipodal pairs. Their normalized pair sums
form the complete even sector. Coordinate swaps are implemented by the existing
D4 simple-root words. This supplies a possible record space; its physical bank,
preparation and class-dependent gate admission are not selected here.
-/
noncomputable section
namespace PMAction.VectorEvenFrame
open Matrix CarrierEvents

abbrev C := Carrier 0

def indicator (v : C) (i : Fin 4) : ℤ := if vector v i = 0 then 0 else 1

lemma pair_gram : ∀ i j : Fin 4,
    (∑ v : C, indicator v i * indicator v j) = if i = j then 2 else 0 := by
  decide +kernel

lemma carrier_gram : ∀ v w : C,
    (∑ i, indicator v i * indicator w i) =
      (if v = w then 1 else 0) + (if CarrierParity.antipode 0 v = w then 1 else 0) := by
  decide +kernel

lemma contrast_gram : ∀ i j : Fin 4,
    (∑ v : C, vector v i * indicator v j) = 0 := by
  decide +kernel

lemma indicator_even : ∀ (v : C) (i : Fin 4),
    indicator (CarrierParity.antipode 0 v) i = indicator v i := by
  decide +kernel

def scale : ℂ := 2 * CarrierParity.scale

theorem scale_sq : star scale * scale = (1/2 : ℂ) := by
  calc
    _ = 4 * (star CarrierParity.scale * CarrierParity.scale) := by simp [scale]; ring
    _ = _ := by rw [CarrierParity.scale_sq]; norm_num

def embedding : Matrix C (Fin 4) ℂ := fun v i => scale * (indicator v i : ℂ)

theorem isometry : embeddingᴴ * embedding = 1 := by
  ext i j
  have hg := congrArg (fun z : ℤ => (z : ℂ)) (pair_gram i j)
  push_cast at hg
  have he (v : C) : star (embedding v i) * embedding v j =
      (1/2 : ℂ) * ((indicator v i : ℂ) * (indicator v j : ℂ)) := by
    simp only [embedding, star_mul, star_intCast]
    calc
      _ = (star scale * scale) * ((indicator v i : ℂ) * (indicator v j : ℂ)) := by ring
      _ = _ := by rw [scale_sq]
  simp only [mul_apply, conjTranspose_apply]
  simp_rw [he]
  rw [← Finset.mul_sum, hg]
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

theorem projector : embedding * embeddingᴴ =
    (1/2 : ℂ) • (1 + (CarrierParity.antipode 0).permMatrix ℂ) := by
  ext v w
  have hg := congrArg (fun z : ℤ => (z : ℂ)) (carrier_gram v w)
  push_cast at hg
  have he (i : Fin 4) : embedding v i * star (embedding w i) =
      (1/2 : ℂ) * ((indicator v i : ℂ) * (indicator w i : ℂ)) := by
    simp only [embedding, star_mul, star_intCast]
    calc
      _ = (star scale * scale) * ((indicator v i : ℂ) * (indicator w i : ℂ)) := by ring
      _ = _ := by rw [scale_sq]
  simp only [mul_apply, conjTranspose_apply]
  simp_rw [he]
  rw [← Finset.mul_sum, hg]
  by_cases hv : v = w
  · subst w
    norm_num [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, CarrierParity.no_fixed_antipode]
  · by_cases ha : CarrierParity.antipode 0 v = w <;>
      norm_num [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hv, ha]

theorem even_image (x : Fin 4 → ℂ) :
    (CarrierParity.antipode 0).permMatrix ℂ *ᵥ (embedding *ᵥ x) = embedding *ᵥ x := by
  rw [permMatrix_mulVec]
  ext v
  simp [embedding, mulVec, dotProduct, indicator_even]

theorem range_iff_even (ψ : C → ℂ) :
    (∃ x, embedding *ᵥ x = ψ) ↔ (CarrierParity.antipode 0).permMatrix ℂ *ᵥ ψ = ψ := by
  constructor
  · rintro ⟨x,rfl⟩; exact even_image x
  · intro h
    refine ⟨embeddingᴴ *ᵥ ψ,?_⟩
    rw [mulVec_mulVec, projector, smul_mulVec, add_mulVec, one_mulVec, h]
    module

/-- The even register may sit on either wall of its separate record carrier. -/
def wallState (s : Bool) (x : Fin 4 → ℂ) : CarrierVacuumSector.Labels 0 → ℂ :=
  if s then Sum.elim (fun _ => 0) (embedding *ᵥ x)
  else Sum.elim (embedding *ᵥ x) (fun _ => 0)

theorem wall_even (s : Bool) (x : Fin 4 → ℂ) :
    CarrierVacuumSector.parity 0 *ᵥ wallState s x = wallState s x := by
  have hz : (CarrierParity.antipode 0).permMatrix ℂ *ᵥ (fun _ : C => (0 : ℂ)) =
      (fun _ : C => (0 : ℂ)) := by
    ext v
    simp [mulVec, dotProduct]
  cases s <;> simp only [wallState, Bool.false_eq_true, ↓reduceIte,
    CarrierVacuumSector.parity, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    hz, zero_mulVec, add_zero, zero_add, even_image]

/-- Inert under the existing odd-compressed wall generator. This uses that
completion; admission and pricing of the controlled recording interaction remain open. -/
theorem wall_stationary (p : ℝ) (k : Fin 3 → ℝ) (δ : ℝ)
    (s : Bool) (x : Fin 4 → ℂ) :
    CarrierVacuumSector.hamiltonian 0 p k δ *ᵥ wallState s x = 0 :=
  CarrierVacuumEvolution.even_inert 0 p k δ _ (wall_even s x)

/-- The record modes are orthogonal to all four carrier-coordinate contrasts. -/
theorem odd_orthogonal : (CarrierParity.embedding 0)ᴴ * embedding = 0 := by
  ext i j
  have hg := congrArg (fun z : ℤ => (z : ℂ)) (contrast_gram i j)
  push_cast at hg
  simp only [mul_apply, conjTranspose_apply, CarrierParity.embedding, embedding, star_mul,
    star_intCast, Matrix.zero_apply]
  have he (v : C) : (vector v i : ℂ) * star CarrierParity.scale *
      (scale * (indicator v j : ℂ)) =
      (star CarrierParity.scale * scale) * ((vector v i : ℂ) * (indicator v j : ℂ)) := by ring
  simp_rw [he]
  rw [← Finset.mul_sum, hg, mul_zero]

/-- A normalized antipodal-pair marker. -/
def marker (i : Fin 4) : C → ℂ := embedding *ᵥ Pi.single i 1

lemma marker_apply (i : Fin 4) (v : C) : marker i v = scale * (indicator v i : ℂ) := by
  simp [marker, Matrix.col_apply, embedding]

/-- Axis transpositions act on the actual eight carrier labels. -/
def axisSwap (i : Fin 4) : Equiv.Perm C := permute 0 (Equiv.swap 0 i)

lemma axis_swap_twice : ∀ i : Fin 4, Function.Involutive (axisSwap i) := by
  unfold Function.Involutive
  decide +kernel

/-- Palindromic words in the existing D4 simple-root reflections.
These are implementation certificates, not minimum-price claims. -/
def word : Fin 4 → List (Fin 4) := ![[], [0], [0,1,0], [0,1,2,1,0]]

theorem root_word : ∀ (i : Fin 4) (v : C),
    ((word i).map (CarrierWeyl.simple 0)).prod v = axisSwap i v := by
  decide +kernel

lemma indicator_swap : ∀ (i : Fin 4) (v : C),
    indicator (axisSwap i v) 0 = indicator v i := by
  decide +kernel

/-- Root words write any marker from the reference-axis blank marker. -/
theorem write_marker (i : Fin 4) : (axisSwap i).permMatrix ℂ *ᵥ marker 0 = marker i := by
  rw [permMatrix_mulVec]
  ext v
  change marker 0 (axisSwap i v) = marker i v
  simp only [marker_apply, indicator_swap]

/-- The stabilizer of the reference axis has exactly its singleton and three spatial axes.
This describes the action on the even pair labels, not a selected particle interpretation. -/
theorem axis_orbits : ∀ i j : Fin 4,
    (∃ p : Equiv.Perm (Fin 4), p 0 = 0 ∧ p i = j) ↔ (i = 0 ↔ j = 0) := by
  decide +kernel

end PMAction.VectorEvenFrame
