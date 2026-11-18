import PMElementaryParticles.ControlledGluedRegister
import PMAction.ChiralLightBand
import PMAction.ExactZeroMode

/-!
# Equal-class crossing on the gapped glued register

The wire crosses at fixed glue class. In the register's wall convention,
a forward crossing goes from generation `g` on T to `g + 2` on F.
The factor swap carries both signed indices across. Two pure roots then
act by spinor parity on the destination amplitude alone. On the gapped
chiralities this is the support of `WallExchange.back`; the reverse leg
has the adjoint support. The link coefficient is the wire's input `y`.

The zero-energy light readout below uses the inventory convention that
the static vacancy is excluded from the light states while its signed
index remains in the gapped register. The on-site couplings preserve the label, with an arbitrary generation
matrix for each label.
-/

noncomputable section
namespace PMElementaryParticles.GappedGluedCrossing

open GluedRegister ControlledGluedRegister ProtocolInventory
open PMConstants.PacketGaugeActions
open PMAction Matrix
open scoped Kronecker

/-- Same class on the two walls fixes the destination generation. -/
theorem equalClass_iff : ∀ g h : Fin 3, wallClass g false = wallClass h true ↔ h = g + 2 := by
  decide +kernel

/-- The same-generation swap-plus-triality crossing has different class support. -/
theorem triality_changes_wall_class : ∀ g : Fin 3, wallClass g false ≠ wallClass g true := by
  decide +kernel

/-- Four glued vector roots realize the factor swap. -/
def runSwap (w : Wt × Wt) : Wt × Wt :=
  ([0, 2, 4, 6] : List (Fin 8)).foldl
    (fun p i => reflectPair (carrier 0 i, -carrier 0 i) p) w

set_option maxRecDepth 4096 in
theorem swap_glued : ∀ (x : Fin 3) (a b : Fin 8),
    runSwap (carrier x a, carrier x b) = (carrier x b, carrier x a) := by
  decide +kernel

/-- A signed representative of an odd carrier axis. -/
def signedAxis (i : Fin 4) (s : Fin 2) : Fin 8 := ⟨2 * i.val + s.val, by omega⟩

/-- The two pure roots exchange axes 0 and 2, then 1 and 3, in the transported frame. -/
def parityRoot (x : Fin 3) (i : Fin 2) : Wt :=
  transport x (root (WallSeesaw.ix 0 i) (WallSeesaw.ix 1 i) false true)

theorem parityRoot_is_root : ∀ (x : Fin 3) (s : Fin 2),
    ∃ (i j : Fin 4) (a b : Bool), i ≠ j ∧ parityRoot x s = root i j a b := by
  decide +kernel

private def applyParity (x : Fin 3) (w : Wt × Wt) : Wt × Wt :=
  reflectPair (0, parityRoot x 1) (reflectPair (0, parityRoot x 0) w)

private theorem parity_frame : ∀ (x : Fin 3) (l : Fin 8) (i : Fin 4) (s : Fin 2),
    applyParity x (frame x l, frame x (signedAxis i s)) =
      (frame x l, frame x (signedAxis (i + 2) s)) := by
  decide +kernel

/-- The forward word is the factor swap followed by amplitude parity on wall F. -/
def runGappedCrossing (g : Fin 3) (w : Wt × Wt) : Wt × Wt :=
  applyParity (wallClass g false) (runSwap w)

theorem runGappedCrossing_encode (g : Fin 3) (c : Channels) (i : Fin 4) (s : Fin 2)
    (hc : active c = false) :
    runGappedCrossing g (encode g c (signedAxis i s)) =
      encode (g + 2) (opposite c) (signedAxis (i + 2) s) := by
  have hop : active (opposite c) = true := by rw [opposite_active, hc]; rfl
  have hx := (equalClass_iff g (g + 2)).mpr rfl
  obtain ⟨a, b, h⟩ := encode_glued g c (signedAxis i s)
  have hs : runSwap (encode g c (signedAxis i s)) =
      ((encode g c (signedAxis i s)).2, (encode g c (signedAxis i s)).1) := by
    rw [h, swap_glued]
  rw [runGappedCrossing, hs]
  simpa [encode, hc, hop, opposite_label, ← hx, place] using
    parity_frame (wallClass g false) (labelIndex c) i s

/-- Directed spin matrix with source restricted to wall T's gapped chirality. -/
def directed (f : Fin 4 → Fin 4) : ConcreteFermion.Spin :=
  fun i j => if 2 ≤ j.val ∧ i = f j then -1 else 0

/-- With the same frame on both walls, the bare swap has zero gapped-to-gapped restriction. -/
theorem bare_gap_zero :
    ChiralLightBand.P1 * directed id = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ChiralLightBand.P1, directed, mul_apply, Fin.sum_univ_four, diagonal]

/-- Parity aligns the word with the wire's gapped hop, with the wire's minus sign. -/
theorem directed_eq_back : directed (fun i => i + 2) = WallExchange.back := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [directed, WallExchange.back]

/-- The directed crossing has no matrix element between the light projections. -/
theorem light_crossing_zero :
    ChiralLightBand.P2 * WallExchange.back * ChiralLightBand.P1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ChiralLightBand.P1, ChiralLightBand.P2, WallExchange.back, mul_apply,
      Fin.sum_univ_four, diagonal]

abbrev Payload := Fin 3 × Fin 8

/-- The upper-right link reverses the forward word's generation shift. -/
def gapLink (y : Fin 3 → ℂ) : Matrix Payload Payload ℂ :=
  CyclicSeesaw.cyc y ⊗ₖ (1 : Matrix (Fin 8) (Fin 8) ℂ)

private theorem cyc_entry (y : Fin 3 → ℂ) (g h : Fin 3) :
    CyclicSeesaw.cyc y g h = if g = h + 1 then y h else 0 := by
  fin_cases g <;> fin_cases h <;> rfl

/-- The actual forward Hamiltonian block has the reflection word's support on
the gapped chirality and the conjugate of the input crossing coefficient. -/
theorem forward_entry (y : Fin 3 → ℂ) (g h : Fin 3) (a b : Fin 8) (i j : Fin 4) :
    (WallExchange.back ⊗ₖ (gapLink y)ᴴ) (i, h, b) (j, g, a) =
      if 2 ≤ j.val ∧ i = j + 2 ∧ h = g + 2 ∧ a = b then -star (y h) else 0 := by
  have hg : g = h + 1 ↔ h = g + 2 := by revert g h; decide +kernel
  have wrap : ∀ k : Fin 3, k + 2 + 1 = k := by decide +kernel
  rw [← directed_eq_back]
  by_cases hj : 2 ≤ j.val <;> by_cases hi : i = j + 2 <;>
    by_cases hh : h = g + 2 <;> by_cases hab : a = b <;>
    simp [gapLink, directed, conjTranspose_apply, cyc_entry, one_apply, hg, hj, hi, hh, hab,
      wrap g]

private theorem gapLink_left_inverse (y : Fin 3 → ℂ) (hy : ∀ g, y g ≠ 0) :
    (CompositeMass.cycInv y ⊗ₖ (1 : Matrix (Fin 8) (Fin 8) ℂ)) * gapLink y = 1 := by
  simp [gapLink, ← mul_kronecker_mul, CompositeMass.cycInv_mul _ hy]

theorem gapLink_inv (y : Fin 3 → ℂ) (hy : ∀ g, y g ≠ 0) :
    (gapLink y)⁻¹ = CompositeMass.cycInv y ⊗ₖ (1 : Matrix (Fin 8) (Fin 8) ℂ) :=
  inv_eq_left_inv (gapLink_left_inverse y hy)

/-- The static light input has seven occupied labels; label zero is the vacancy. -/
theorem static_occupied_iff : ∀ c : Channels, active c = false →
    (labelIndex c ≠ 0 ↔ baseProtocol c ≠ none) := by decide +kernel

theorem active_neutral_iff : ∀ c : Channels, active c = true →
    (labelIndex c = 0 ↔ baseProtocol c = some .neutrino) := by decide +kernel

private theorem repeat_link (A : Matrix (Fin 3) (Fin 3) ℂ) :
    A ⊗ₖ (1 : Matrix (Fin 8) (Fin 8) ℂ) = blockDiagonal (fun _ : Fin 8 => A) := by
  ext ⟨g, a⟩ ⟨h, b⟩
  by_cases hab : a = b <;> simp [one_apply, blockDiagonal, hab]

/-- Extend the static flip to the unoccupied light slot by zero. -/
def staticFlip (A : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ) (a : Fin 8) :
    Matrix (Fin 3) (Fin 3) ℂ := if a = 0 then 0 else A a

/-- With both light banks included, the zero-energy Schur mass is
independent in each signed label, including the neutral pair. -/
theorem paired_light_mass (y : Fin 3 → ℂ) (hy : ∀ g, y g ≠ 0)
    (A B : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ) :
    blockDiagonal B * (gapLink y)⁻¹ * (blockDiagonal A)ᴴ =
      blockDiagonal (fun a => B a * CompositeMass.cycInv y * (A a)ᴴ) := by
  rw [gapLink_inv y hy, repeat_link, blockDiagonal_conjTranspose, ← blockDiagonal_mul,
    ← blockDiagonal_mul]

/-- If the static neutral slot participates in the light block, this is
the exact zero-energy Schur pairing to the active neutrino. -/
theorem neutral_paired_mass_entry (y : Fin 3 → ℂ) (hy : ∀ g, y g ≠ 0)
    (A B : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ) (g h : Fin 3) :
    (blockDiagonal B * (gapLink y)⁻¹ * (blockDiagonal A)ᴴ) (g, 0) (h, 0) =
      (B 0 * CompositeMass.cycInv y * (A 0)ᴴ) g h := by
  rw [paired_light_mass y hy]
  simp [blockDiagonal]

/-- For diagonal on-site flips, the neutral block's reverse-cycle entry
from generation `g + 1` to `g`. -/
def neutralCycleWeight (y a b : Fin 3 → ℂ) (g : Fin 3) : ℂ :=
  b g * (y g)⁻¹ * star (a (g + 1))

/-- Diagonal neutral flips leave one Schur entry per generation and column. -/
theorem diagonal_neutral_mass_entry (y a b : Fin 3 → ℂ) (g h : Fin 3) :
    (diagonal b * CompositeMass.cycInv y * (diagonal a)ᴴ) g h =
      if h = g + 1 then neutralCycleWeight y a b g else 0 := by
  rw [diagonal_conjTranspose, mul_diagonal, diagonal_mul]
  fin_cases g <;> fin_cases h <;>
    simp [neutralCycleWeight, CompositeMass.cycInv, Pi.star_apply]

/-- The squared Schur singular values are the squared moduli of the three
cycle weights, with the active basis already diagonalizing the Gram matrix. -/
theorem diagonal_neutral_gram (y a b : Fin 3 → ℂ) :
    let M := diagonal b * CompositeMass.cycInv y * (diagonal a)ᴴ
    M * Mᴴ = diagonal (fun g =>
      neutralCycleWeight y a b g * star (neutralCycleWeight y a b g)) := by
  intro M
  ext g h
  rw [Matrix.mul_apply]
  simp only [conjTranspose_apply, M, diagonal_neutral_mass_entry]
  fin_cases g <;> fin_cases h <;>
    simp [diagonal]

/-- Equal flip and crossing magnitudes leave a degenerate neutral Schur
spectrum regardless of the phases or the chosen common magnitudes. -/
theorem diagonal_neutral_gram_uniform (y a b : Fin 3 → ℂ)
    (ρY ρA ρB : ℝ) (hy : ∀ g, ‖y g‖ = ρY)
    (ha : ∀ g, ‖a g‖ = ρA) (hb : ∀ g, ‖b g‖ = ρB) :
    let M := diagonal b * CompositeMass.cycInv y * (diagonal a)ᴴ
    M * Mᴴ = ((ρB * ρY⁻¹ * ρA) ^ 2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  dsimp only
  rw [diagonal_neutral_gram, ← diagonal_one, ← diagonal_smul]
  congr 1
  funext g
  rw [Pi.smul_apply, mul_comm (neutralCycleWeight y a b g), Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  simp [neutralCycleWeight, norm_inv, hy, ha, hb,
    Complex.real_smul]

/-- After excluding the static vacancy, the mass preserves the signed label.
The neutral output has no static light partner. Each occupied label has its
own two generation-space flip matrices. -/
theorem occupied_light_mass (y : Fin 3 → ℂ) (hy : ∀ g, y g ≠ 0)
    (A B : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ) :
    blockDiagonal B * (gapLink y)⁻¹ * (blockDiagonal (staticFlip A))ᴴ =
      blockDiagonal (fun a => if a = 0 then 0 else B a * CompositeMass.cycInv y * (A a)ᴴ) := by
  rw [paired_light_mass y hy]
  congr 1
  funext a
  by_cases ha : a = 0 <;> simp [staticFlip, ha]

theorem neutral_light_row (y : Fin 3 → ℂ) (hy : ∀ g, y g ≠ 0)
    (A B : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ) (g : Fin 3) (p : Payload) :
    (blockDiagonal B * (gapLink y)⁻¹ * (blockDiagonal (staticFlip A))ᴴ) (g, 0) p = 0 := by
  rw [occupied_light_mass y hy]
  simp [blockDiagonal]

/-- The neutral Schur zero lifts to an exact zero mode of the full
zero-momentum Hamiltonian. Its light projection is the active neutral basis
vector, with zero amplitude on the entire static light wall. -/
theorem neutral_exact_zero (y : Fin 3 → ℂ) (hy : ∀ g, y g ≠ 0)
    (A B : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ) (g : Fin 3) :
    ∃ z : Payload ⊕ Payload → ℂ,
      ExactZeroMode.H (gapLink y) (blockDiagonal (staticFlip A)) (blockDiagonal B) *ᵥ
        Sum.elim (Sum.elim 0 (Pi.single (g, 0) 1)) z = 0 := by
  let Y := gapLink y
  let D₁ := blockDiagonal (staticFlip A)
  let D₂ := blockDiagonal B
  let V := CompositeMass.V2 D₁ D₂
  let ν : Payload → ℂ := Pi.single (g, 0) 1
  let x : Payload ⊕ Payload → ℂ := Sum.elim 0 ν
  let z := -(WallSeesaw.Ginv Y *ᵥ (Vᴴ *ᵥ x))
  have hY := Matrix.isUnit_det_of_left_inverse (gapLink_left_inverse y hy)
  have hdual : (D₁ * (Yᴴ)⁻¹ * D₂ᴴ) *ᵥ ν = 0 := by
    rw [show D₁ * (Yᴴ)⁻¹ * D₂ᴴ = (D₂ * Y⁻¹ * D₁ᴴ)ᴴ by
      simp [conjTranspose_mul, conjTranspose_nonsing_inv, Matrix.mul_assoc]]
    change (D₂ * Y⁻¹ * D₁ᴴ)ᴴ *ᵥ Pi.single (g, 0) 1 = 0
    rw [mulVec_single_one]
    ext p
    change star ((blockDiagonal B * (gapLink y)⁻¹ * (blockDiagonal (staticFlip A))ᴴ)
      (g, 0) p) = 0
    rw [neutral_light_row y hy A B, star_zero]
  have hx : -(V * WallSeesaw.Ginv Y * Vᴴ) *ᵥ x = 0 := by
    change -(CompositeMass.V2 D₁ D₂ * WallSeesaw.Ginv Y * (CompositeMass.V2 D₁ D₂)ᴴ) *ᵥ x = 0
    rw [CompositeMass.effective_mass_general]
    dsimp only [x]
    rw [fromBlocks_mulVec]
    simp [hdual]
  have hz : WallSeesaw.G Y *ᵥ z = -(Vᴴ *ᵥ x) := by
    dsimp only [z]
    rw [mulVec_neg, mulVec_mulVec, (WallSeesaw.gapped_inverse Y hY).1, one_mulVec]
  have hv : V *ᵥ z = 0 := by
    dsimp only [z]
    rw [mulVec_neg, mulVec_mulVec, mulVec_mulVec, ← neg_mulVec, hx]
  refine ⟨z, ?_⟩
  change ExactZeroMode.H Y D₁ D₂ *ᵥ Sum.elim x z = 0
  rw [ExactZeroMode.H, fromBlocks_mulVec]
  change Sum.elim ((0 : Matrix _ _ ℂ) *ᵥ x + V *ᵥ z) (Vᴴ *ᵥ x + WallSeesaw.G Y *ᵥ z) = 0
  simp [hv, hz]

end PMElementaryParticles.GappedGluedCrossing
