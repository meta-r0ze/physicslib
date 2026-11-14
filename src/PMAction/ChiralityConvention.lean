import PMAction.WallChiralCurrent
import PMAction.WallExchange
import PMAction.Machine.NativeReferenceBackground
import PMAction.WeakVertex

/-!
# "Left-handed" is a convention fixed by the charged current

`WallChiralCurrent` shows the charged projector `(1 − Γ)/2` selects one wall on the zero kernel,
and leaves calling it left-handed as an input. Here that label is a convention, not physics.

* `orientation_flips_gammaFive`: reversing the spatial orientation (`γʲ ↦ −γʲ`, `j = 1, 2, 3`)
  turns `γ⁵ = i γ⁰γ¹γ²γ³` into `−γ⁵`.
* `axis_swap_flips_gammaFive`: exchanging two spatial axes does the same.
* `exchange_flips_chirality`: the wall-parity exchange `P = [[0, β], [β, 0]]` conjugates the
  wall chirality to its negative. It therefore exchanges the two chiral projectors
  (`exchange_swaps_projectors`).
* `exchange_hamiltonian`: the same `P` maps the actual lattice Hamiltonian
  (`ConcreteFermion.hamiltonian`) to itself with `k ↦ −k`. It is the parity symmetry.

* `projector_kills_background`, `opposite_keeps_background`, `exchanged_background`: Paper II's
  stationary reference background lies on the first wall. The posited projector `(1 − Γ)/2`
  annihilates it and `(1 + Γ)/2` keeps it. After the wall-parity exchange, `(1 − Γ)/2` keeps the
  exchanged background. Weak repairs the reference (`FrameOwnership`, Contract C), so its current
  must act on the reference's wall. The weak representation is therefore attached to the wall
  carrying the reference, and "left" names that wall. In Paper II's displayed coordinates this
  means using `(1 + Γ)/2`, or equivalently the exchanged description.

* `displayed_placement_excluded`, `physicalBackground_kernel`, `weak_acts_on_reference`: **the
  decision.** Paper II's Dirac algebra fixes `γ⁵ = Γ` and the charged projector `(1 − Γ)/2`
  (`VATrace.L = 1 − Γ`, `WeakVertex`). With that projector, the first-wall placement of the
  reference is excluded: the weak current maps it to zero. The exchanged placement
  `physicalBackground` is still a stationary zero mode, because the exchange is a symmetry, and
  the weak current keeps it. So the physical reference is the second-wall (`−Γ`) zero mode, and
  the existing projector is correct as written.

So which wall is called left depends on the orientation convention. The parity-related
description is an equivalent theory with the labels swapped. The physical content is that the
charged current couples to exactly one wall, which `WallChiralCurrent.selected_iff` derives;
"left-handed" names that wall. Attaching the weak representation is derived
(`PMConstants.WeakUniform`, `CarrierActions.weak_chiral`); the identification extends to the light
band through first order in `k` (`ChiralLightBand`).
-/

noncomputable section
namespace PMAction.ChiralityConvention
open Matrix ConcreteFermion WallChiralCurrent

/-- Dirac gammas in the reversed spatial orientation. -/
def reversedGamma : Fin 4 → Spin :=
  ![beta, -(beta * alpha 0), -(beta * alpha 1), -(beta * alpha 2)]

/-- Dirac gammas with spatial axes `0` and `1` exchanged. -/
def swappedGamma : Fin 4 → Spin := ![beta, beta * alpha 1, beta * alpha 0, beta * alpha 2]

def gammaFiveOf (G : Fin 4 → Spin) : Spin := Complex.I • (G 0 * G 1 * G 2 * G 3)

theorem orientation_flips_gammaFive : gammaFiveOf reversedGamma = -gamma := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [gammaFiveOf, reversedGamma, beta, alpha, gamma, mul_apply, Fin.sum_univ_four]

theorem axis_swap_flips_gammaFive : gammaFiveOf swappedGamma = -gamma := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [gammaFiveOf, swappedGamma, beta, alpha, gamma, mul_apply, Fin.sum_univ_four]

/-- The displayed orientation gives `+Γ`. -/
theorem displayed_gammaFive : gammaFiveOf diracGamma = gamma := gammaFive_eq

/-- Wall exchange with spinor parity on the eight wall components. -/
def exchange : Matrix Sites Sites ℂ := fromBlocks 0 beta beta 0

theorem exchange_sq : exchange * exchange = 1 := by
  rw [exchange, fromBlocks_multiply]
  simp [beta_square, ← fromBlocks_one]

theorem exchange_flips_chirality : exchange * chirality * exchange = -chirality := by
  rw [exchange, chirality, fromBlocks_multiply, fromBlocks_multiply]
  have h : beta * gamma * beta = -gamma := by
    rw [beta_gamma, neg_mul, mul_assoc, beta_square, mul_one]
  simp [h, fromBlocks_neg]

/-- **The exchange swaps the two chiral projectors.** -/
theorem exchange_swaps_projectors :
    exchange * projector * exchange = (1 / 2 : ℂ) • (1 + chirality) := by
  rw [projector, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_one,
    exchange_flips_chirality, exchange_sq, sub_neg_eq_add]

set_option maxHeartbeats 4000000 in
/-- **The exchange is a symmetry of the actual lattice Hamiltonian**, with momentum reversed. -/
theorem exchange_hamiltonian (k : Fin 3 → ℝ) (δ : ℝ) :
    exchange * hamiltonian k δ * exchange = hamiltonian (-k) δ := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [exchange, hamiltonian, DomainWallSpectrum.H, DomainWallSpectrum.momentum,
      DomainWallSpectrum.hop, DomainWallSpectrum.back, DomainWallSpectrum.plus,
      DomainWallSpectrum.minus, beta, gamma, alpha, mul_apply, Fin.sum_univ_four,
      Fin.sum_univ_three, Fintype.sum_sum_type, Real.sin_neg, Matrix.vecMul, dotProduct,
      Matrix.sub_apply, Matrix.one_apply, Matrix.add_apply, Matrix.smul_apply] <;> ring

/-! ## The charged current must act on the reference's wall -/

/-- Paper II's stationary reference background on the wall sites
(`NativeReferenceBackground.background_zero_mode`). -/
def background (r : Fin 2 → ℂ) : Sites → ℂ :=
  Sum.elim (WalkReferenceCoupling.pack (Sum.elim r r)) (fun _ => 0)

/-- Coordinates of the first-wall reference background. -/
theorem background_apply (r : Fin 2 → ℂ) :
    background r = Sum.elim
      (![(Real.sqrt 2 : ℂ) * r 0, (Real.sqrt 2 : ℂ) * r 1, 0, 0] : Fin 4 → ℂ)
      (fun _ => 0) := by
  have hsqrt : (Real.sqrt 2 : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  have h2 : ((Real.sqrt 2 : ℂ) ^ 2) = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  ext x
  rcases x with i | i <;> fin_cases i <;>
    simp [background, WalkReferenceCoupling.pack, WalkReferenceCoupling.raw,
      WalkReferenceCoupling.backward, WalkRecordTransport.encode, Sum.elim]
  all_goals
    field_simp [hsqrt]
    rw [h2]
    ring

theorem background_kernel (r : Fin 2 → ℂ) : hamiltonian 0 0 *ᵥ background r = 0 :=
  NativeReferenceBackground.background_zero_mode r

/-- **The posited projector `(1 − Γ)/2` annihilates the reference background.** -/
theorem projector_kills_background (r : Fin 2 → ℂ) : projector *ᵥ background r = 0 := by
  rw [kernel_projector _ (background_kernel r)]
  funext c; rcases c with a | a <;> simp [secondWall, background]

/-- **`(1 + Γ)/2` keeps the reference background.** -/
theorem opposite_keeps_background (r : Fin 2 → ℂ) :
    ((1 / 2 : ℂ) • (1 + chirality)) *ᵥ background r = background r := by
  have h : ((1 / 2 : ℂ) • (1 + chirality)) = 1 - projector := by
    rw [projector]; ext i j; simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]; ring
  rw [h, sub_mulVec, one_mulVec, projector_kills_background, sub_zero]

/-- **In the exchanged description the posited projector acts on the reference.** The wall-parity
exchange (a symmetry, `exchange_hamiltonian`) moves the background to the second wall, where
`(1 − Γ)/2` keeps it. -/
theorem exchanged_background (r : Fin 2 → ℂ) :
    projector *ᵥ (exchange *ᵥ background r) = exchange *ᵥ background r := by
  have hsw := exchange_swaps_projectors
  have e : projector = exchange * ((1 / 2 : ℂ) • (1 + chirality)) * exchange := by
    rw [← hsw, ← mul_assoc, ← mul_assoc, exchange_sq, one_mul, mul_assoc, exchange_sq, mul_one]
  rw [e, ← mulVec_mulVec, ← mulVec_mulVec,
    mulVec_mulVec (v := background r) (M := exchange) (N := exchange), exchange_sq,
    one_mulVec, opposite_keeps_background]

/-! ## The decision: place the reference where the weak current acts -/

lemma background_ne_zero (r : Fin 2 → ℂ) (hr : r ≠ 0) : background r ≠ 0 := by
  intro h
  have hp : WalkReferenceCoupling.pack (Sum.elim r r) = 0 := by
    funext a; have := congrFun h (.inl a); simpa [background] using this
  have hraw : WalkReferenceCoupling.raw (Sum.elim r r) = 0 := by
    have hc : ((1 / Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      rw [Ne, Complex.ofReal_eq_zero]; positivity
    have := hp
    rw [WalkReferenceCoupling.pack] at this
    exact (smul_eq_zero.mp this).resolve_left hc
  have h2 := WalkReferenceCoupling.recover_raw (Sum.elim r r)
  rw [hraw] at h2
  have h0 : WalkReferenceCoupling.recover 0 = 0 := by
    funext m; rcases m with i | i <;> fin_cases i <;> simp [WalkReferenceCoupling.recover]
  rw [h0] at h2
  apply hr
  funext i
  have := congrFun h2 (.inl i)
  simp at this
  simpa using this

/-- **The displayed placement is excluded.** For a nonzero reference, the charged projector
`(1 − Γ)/2` of Paper II's Dirac algebra (`γ⁵ = Γ`, `VATrace.L = 1 − Γ`) does not act on the
first-wall background: it maps it to zero. -/
theorem displayed_placement_excluded (r : Fin 2 → ℂ) (hr : r ≠ 0) :
    projector *ᵥ background r ≠ background r := by
  rw [projector_kills_background]; exact (background_ne_zero r hr).symm

/-- The physical reference: the stationary background in the wall-exchanged placement. -/
def physicalBackground (r : Fin 2 → ℂ) : Sites → ℂ := exchange *ᵥ background r

/-- Coordinates of the exchanged physical background: it lives on the second wall. -/
theorem physicalBackground_apply (r : Fin 2 → ℂ) :
    physicalBackground r = Sum.elim (fun _ => 0)
      (![0, 0, (Real.sqrt 2 : ℂ) * r 0, (Real.sqrt 2 : ℂ) * r 1] : Fin 4 → ℂ) := by
  rw [physicalBackground, background_apply]
  ext x
  rcases x with i | i <;> fin_cases i <;>
    simp [exchange, beta, fromBlocks, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Sum.elim]

/-- It is still a zero mode, because the exchange is a symmetry of the Hamiltonian at `k = 0`. -/
theorem physicalBackground_kernel (r : Fin 2 → ℂ) :
    hamiltonian 0 0 *ᵥ physicalBackground r = 0 := by
  have h := exchange_hamiltonian 0 0
  rw [neg_zero] at h
  have hH : hamiltonian 0 0 = exchange * hamiltonian 0 0 * exchange := by
    rw [h]
  rw [physicalBackground, hH, ← mulVec_mulVec, ← mulVec_mulVec,
    mulVec_mulVec (v := background r) (M := exchange) (N := exchange), exchange_sq, one_mulVec,
    background_kernel, mulVec_zero]

/-- **The weak current acts on the physical reference.** -/
theorem weak_acts_on_reference (r : Fin 2 → ℂ) :
    projector *ᵥ physicalBackground r = physicalBackground r := exchanged_background r

/-- **The wall projector is the block-diagonal Paper-II V−A projector.** -/
theorem projector_eq_fromBlocks_PL :
    projector = (fromBlocks (PMAction.WeakVertex.PL) 0 0 (PMAction.WeakVertex.PL) :
      Matrix Sites Sites ℂ) := by
  rw [projector, chirality, PMAction.WeakVertex.PL_eq]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [fromBlocks, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]

/-- **Uniqueness on the zero kernel.** Any operator that kills the unphysical
first-wall background and fixes the exchanged physical background agrees with the
chiral projector on every zero mode. The projector is therefore forced by the
reference on the kernel, not chosen; extending it off the kernel remains the
stated input. -/
theorem projector_unique_on_kernel (P : Matrix Sites Sites ℂ)
    (hkill : ∀ r, P *ᵥ background r = 0)
    (hfix : ∀ r, P *ᵥ physicalBackground r = physicalBackground r)
    (v : Sites → ℂ) (hv : hamiltonian 0 0 *ᵥ v = 0) :
    P *ᵥ v = projector *ᵥ v := by
  have hc := (kernel_coordinates v).mp hv
  let a : Fin 2 → ℂ := ![v (.inl 0) / (Real.sqrt 2 : ℂ), v (.inl 1) / (Real.sqrt 2 : ℂ)]
  let b : Fin 2 → ℂ := ![v (.inr 2) / (Real.sqrt 2 : ℂ), v (.inr 3) / (Real.sqrt 2 : ℂ)]
  have hsqrt : (Real.sqrt 2 : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  have hdecomp : v = background a + physicalBackground b := by
    rw [background_apply, physicalBackground_apply]
    ext x
    rcases x with i | i <;> fin_cases i <;>
      simp [a, b, Sum.elim, hc]
    all_goals field_simp [hsqrt]
  rw [hdecomp]
  have hL : P *ᵥ (background a + physicalBackground b) = physicalBackground b := by
    rw [mulVec_add, hkill, hfix]; simp
  have hR : projector *ᵥ (background a + physicalBackground b) = physicalBackground b := by
    rw [mulVec_add, projector_kills_background, weak_acts_on_reference]; simp
  rw [hL, hR]

theorem physicalBackground_ne_zero (r : Fin 2 → ℂ) (hr : r ≠ 0) : physicalBackground r ≠ 0 := by
  intro h
  apply background_ne_zero r hr
  have := congrArg (exchange *ᵥ ·) h
  simp only [physicalBackground, mulVec_mulVec, exchange_sq, one_mulVec, mulVec_zero] at this
  exact this

/-! ## The chirality orientation object

The sign of `γ⁵` is a **convention, fixed — not fitted — by the reference**. The
wall exchange swaps the two orientations; the maintained reference is fixed by
one of them. Downstream CP-phase branches read the physical orientation off this
object instead of choosing a sign; the mixing data cannot select it
(`PMFlavor.ReferenceFlavour.ckm_normSq_conj`). -/

/-- The two chirality orientations: the sign multiplying `γ⁵`. -/
inductive Orientation where
  | left
  | right
  deriving DecidableEq, Repr

namespace Orientation

/-- The chirality operator in this orientation, `±γ⁵`. -/
def chi : Orientation → Matrix Sites Sites ℂ
  | left => chirality
  | right => -chirality

/-- The opposite orientation. -/
def flip : Orientation → Orientation
  | left => right
  | right => left

/-- The chiral projector `½(1 − χ)`. -/
def proj (o : Orientation) : Matrix Sites Sites ℂ := (1 / 2 : ℂ) • (1 - chi o)

@[simp] theorem chi_left : chi left = chirality := rfl
@[simp] theorem chi_right : chi right = -chirality := rfl
@[simp] theorem flip_left : flip left = right := rfl
@[simp] theorem flip_right : flip right = left := rfl

/-- `left` is the displayed physical projector `½(1 − γ⁵)`. -/
theorem proj_left : proj left = WallChiralCurrent.projector := rfl

/-- The wall exchange swaps the two orientations. -/
theorem exchange_chi (o : Orientation) :
    exchange * chi o * exchange = chi (flip o) := by
  cases o with
  | left => simpa using exchange_flips_chirality
  | right =>
      rw [chi_right, flip_right, chi_left, mul_neg, neg_mul, exchange_flips_chirality,
        neg_neg]

theorem exchange_proj (o : Orientation) :
    exchange * proj o * exchange = proj (flip o) := by
  rw [proj, proj, mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [mul_sub, sub_mul, mul_one, exchange_sq, exchange_chi]

/-- **The physical orientation is fixed by the maintained reference.** The
reference is a chirality eigenmode, so it is fixed by exactly one of the two
projectors; that orientation is the substrate's convention. -/
def referenceOrientation : Orientation := left

theorem reference_proj (r : Fin 2 → ℂ) :
    (proj referenceOrientation) *ᵥ physicalBackground r = physicalBackground r := by
  rw [referenceOrientation, proj_left]
  exact weak_acts_on_reference r

end Orientation

end PMAction.ChiralityConvention
