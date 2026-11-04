import PMConstants.CarrierRegisterModel
import PMAction.WallChiralCurrent

/-!
# Test wall/chirality identifications against the full vacuum update

Packet left/right, the vacuum wall, and Dirac chirality are three distinct
labels. Matching either of the latter two to the packet tag does not give a
reducing sector of the full free eight-mode Hamiltonian, already at k = δ = 0.
The obstruction uses gapped states. On the zero kernel the two matching masks
agree, consistent with Paper II's chiral-current identification there.
No physical chiral current or interacting mass link is selected by this test.
-/
noncomputable section
set_option synthInstance.maxSize 512
namespace PMConstants.CarrierRegisterChirality
open Matrix PMAction CarrierRegisterModel
open scoped Kronecker

def leftPacket : Payload → Bool := Sum.elim (fun _ => true) (fun _ => false)
def secondWall : ConcreteFermion.Sites → Bool := Sum.elim (fun _ => false) (fun _ => true)
def negativeChirality : ConcreteFermion.Sites → Bool :=
  Sum.elim (fun i => decide (2 ≤ i.val)) (fun i => decide (2 ≤ i.val))

def wallMatch : Matrix Modes Modes ℂ :=
  diagonal (fun p => if secondWall p.1 = leftPacket p.2 then 1 else 0)
def chiralityMatch : Matrix Modes Modes ℂ :=
  diagonal (fun p => if negativeChirality p.1 = leftPacket p.2 then 1 else 0)
def vacuum : Matrix Modes Modes ℂ :=
  ConcreteFermion.hamiltonian 0 0 ⊗ₖ (1 : Matrix Payload Payload ℂ)

private theorem mixing_entry (v : CarrierRepresentation.V) (tag : Bool) :
    vacuum ((.inr 0), if tag then .inl v else .inr v)
      ((.inl 2), if tag then .inl v else .inr v) = -1 := by
  cases tag <;>
    norm_num [vacuum, ConcreteFermion.hamiltonian, DomainWallSpectrum.H,
      DomainWallSpectrum.back, DomainWallSpectrum.minus, ConcreteFermion.beta,
      ConcreteFermion.gamma, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four]

/-- A heavy-mode matrix entry crosses the proposed packet/wall matching. -/
theorem wall_matching_not_commute (v : CarrierRepresentation.V) :
    vacuum * wallMatch ≠ wallMatch * vacuum := by
  intro h
  have hh := congrFun (congrFun h ((.inr 0), .inr v)) ((.inl 2), .inr v)
  have he := mixing_entry v false
  simp only [Bool.false_eq_true, ↓reduceIte] at he
  simp [wallMatch, mul_diagonal, diagonal_mul, secondWall, leftPacket, he] at hh

/-- Dirac-chirality matching also fails on the full ambient vacuum, rather
than providing an automatic extension of the zero-kernel identification. -/
theorem chirality_matching_not_commute (v : CarrierRepresentation.V) :
    vacuum * chiralityMatch ≠ chiralityMatch * vacuum := by
  intro h
  have hh := congrFun (congrFun h ((.inr 0), .inl v)) ((.inl 2), .inl v)
  have he := mixing_entry v true
  simp only [↓reduceIte] at he
  simp [chiralityMatch, mul_diagonal, diagonal_mul, negativeChirality, leftPacket, he] at hh

/-- The two descriptions agree on actual zero modes, for every payload amplitude. -/
theorem matching_agrees_on_zero (ψ : ConcreteFermion.Sites → ℂ)
    (hψ : ConcreteFermion.hamiltonian 0 0 *ᵥ ψ = 0) (w : Payload → ℂ) :
    chiralityMatch *ᵥ (fun p : Modes => ψ p.1 * w p.2) =
      wallMatch *ᵥ (fun p : Modes => ψ p.1 * w p.2) := by
  have hc := (ConcreteFermion.kernel_coordinates ψ).mp hψ
  ext ⟨s,p⟩
  rcases s with i | i <;> fin_cases i <;> cases p <;>
    simp [chiralityMatch, wallMatch, Matrix.mulVec_diagonal, secondWall,
      negativeChirality, leftPacket, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2]

/-- The agreement also holds for arbitrary entangled spinor/payload zero modes. -/
theorem matching_agrees_on_full_kernel (ψ : Modes → ℂ) (hψ : vacuum *ᵥ ψ = 0) :
    chiralityMatch *ᵥ ψ = wallMatch *ᵥ ψ := by
  have hf (p : Payload) :
      ConcreteFermion.hamiltonian 0 0 *ᵥ (fun s => ψ (s,p)) = 0 := by
    ext s
    have hh := congrFun hψ (s,p)
    cases p <;>
      simpa [vacuum, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
        kronecker_apply, Matrix.one_apply] using hh
  ext ⟨s,p⟩
  have hc := (ConcreteFermion.kernel_coordinates (fun t => ψ (t,p))).mp (hf p)
  rcases s with i | i <;> fin_cases i <;> cases p <;>
    simp [chiralityMatch, wallMatch, Matrix.mulVec_diagonal, secondWall,
      negativeChirality, leftPacket, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2]

end PMConstants.CarrierRegisterChirality
