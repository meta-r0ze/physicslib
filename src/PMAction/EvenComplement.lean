import PMAction.Machine.CarrierVacuumSector

/-!
# The even complement: the native wall gates are not conservative there

`CarrierVacuumSector.rawHamiltonian` builds the two-wall Hamiltonian from the native carrier
operators (`β`, `Γ`, the `αⱼ`: signed Weyl words and the reconstructed phase) on all eight carriers of
a class; its odd restriction is the Dirac wall (`identification`). The library gave the even
complement zero action "by our extension convention" (`CarrierVacuumEvolution.even_inert`). Here the
raw native operator is tested on the even complement.

The uniform carrier mode `u` (every carrier weight `1`) is antipode-even (`uniform_even`) and fixed
by every carrier permutation (`perm_uniform`), so `Γ u = u`: on it the chiral projectors are
`(1 + Γ)/2 = 1` and `(1 − Γ)/2 = 0`.

* `hop_uniform`, `back_uniform`: the wall-to-wall hop sends `u` to `−u`; the reverse hop sends it
  to `0`.
* `raw_not_hermitian`: so the raw native two-wall Hamiltonian is not Hermitian, for every class,
  momentum and detuning (the hop is not the adjoint of the reverse hop on `u`).
* `one_way`: at `k = 0`, `δ = 0` it maps `(0, u) ↦ (−u, 0)` and `(u, 0) ↦ 0`: a nilpotent pair, so
  `exp(−iHt)(0, u) = (0, u) + it(u, 0)` grows linearly in norm. The native gates do not conserve
  the even complement (Conservation), and an even state under them does not persist.

**Consequence.** A conservative update that keeps the native action on the odd sector (the wall)
must replace it on the even complement by a Hermitian completion `A`. Pricing invisible states by
their squared energy, as for the reference background and the other wall's flip
(`OtherWallStationary.energyPrice`), the completion has zero price on every even state exactly when
`A = 0` (`zero_price_iff`). So the identity completion is the unique most persistent one: the even
complement is stationary under the wall. That replaces the extension convention by Conservation plus
Economy, with the same price premise as `OtherWallStationary`.
-/

noncomputable section
namespace PMAction.EvenComplement
open Matrix CarrierEvents CarrierVacuumSector

variable (c : Fin 3)

/-- The uniform carrier mode. -/
def uniform : Carrier c → ℂ := fun _ => 1

lemma perm_uniform (σ : Equiv.Perm (Carrier c)) : σ.permMatrix ℂ *ᵥ uniform c = uniform c := by
  rw [PEquiv.toMatrix_toPEquiv_mulVec]; rfl

lemma permH_uniform (σ : Equiv.Perm (Carrier c)) :
    (σ.permMatrix ℂ)ᴴ *ᵥ uniform c = uniform c := by
  rw [conjTranspose_permMatrix, perm_uniform]

/-- The uniform mode is antipode-even. -/
theorem uniform_even : (CarrierParity.antipode c).permMatrix ℂ *ᵥ uniform c = uniform c :=
  perm_uniform c _

lemma gamma_uniform : gamma c *ᵥ uniform c = uniform c := perm_uniform c _
lemma beta_uniform : beta c *ᵥ uniform c = uniform c := perm_uniform c _

/-- **The wall-to-wall hop sends the uniform mode to its negative.** -/
theorem hop_uniform :
    DomainWallSpectrum.hop (beta c) (gamma c) *ᵥ uniform c = -uniform c := by
  simp only [DomainWallSpectrum.hop, DomainWallSpectrum.plus, neg_mulVec, ← mulVec_mulVec,
    smul_mulVec, add_mulVec, one_mulVec, gamma_uniform]
  rw [show ((1/2 : ℝ) • (uniform c + uniform c)) = uniform c by
    ext; simp [uniform]; norm_num, beta_uniform]

/-- **The reverse hop sends it to zero.** -/
theorem back_uniform : DomainWallSpectrum.back (beta c) (gamma c) *ᵥ uniform c = 0 := by
  simp only [DomainWallSpectrum.back, DomainWallSpectrum.minus, neg_mulVec, ← mulVec_mulVec,
    smul_mulVec, sub_mulVec, one_mulVec, gamma_uniform, sub_self, smul_zero, mulVec_zero, neg_zero]

/-- The adjoint of the reverse hop also kills it. -/
theorem backH_uniform :
    (DomainWallSpectrum.back (beta c) (gamma c))ᴴ *ᵥ uniform c = 0 := by
  simp only [DomainWallSpectrum.back, DomainWallSpectrum.minus, conjTranspose_neg,
    conjTranspose_mul, conjTranspose_smul, conjTranspose_sub, conjTranspose_one, neg_mulVec,
    ← mulVec_mulVec, beta, permH_uniform, smul_mulVec, sub_mulVec, one_mulVec]
  rw [show gamma c = (CarrierWeyl.lookup c 1).permMatrix ℂ from rfl, permH_uniform]
  simp

lemma uniform_ne_zero : uniform c ≠ 0 := by
  intro h
  have hc : Nonempty (Carrier c) := by
    rw [← Fintype.card_pos_iff, carrier_card]; norm_num
  obtain ⟨v⟩ := hc
  have := congrFun h v
  simp [uniform] at this

/-- **The raw native two-wall Hamiltonian is not Hermitian**, in every class, at every momentum and
detuning. -/
theorem raw_not_hermitian (p : ℝ) (k : Fin 3 → ℝ) (δ : ℝ) :
    ¬ (rawHamiltonian c p k δ).IsHermitian := by
  intro h
  have he := h.eq
  unfold rawHamiltonian DomainWallSpectrum.H at he
  rw [fromBlocks_conjTranspose] at he
  have hb := (fromBlocks_inj.mp he).2.1
  have hv := congrArg (· *ᵥ uniform c) hb
  rw [backH_uniform, hop_uniform] at hv
  exact uniform_ne_zero c (neg_eq_zero.mp hv.symm)

/-- **One-way coupling at `k = 0`, `δ = 0`**: `(0, u) ↦ (−u, 0)` and `(u, 0) ↦ 0`. -/
theorem one_way (p : ℝ) :
    rawHamiltonian c p 0 0 *ᵥ Sum.elim 0 (uniform c) = Sum.elim (-uniform c) 0 ∧
      rawHamiltonian c p 0 0 *ᵥ Sum.elim (uniform c) 0 = 0 := by
  have hK : DomainWallSpectrum.momentum (alpha c p) 0 = 0 := by
    simp [DomainWallSpectrum.momentum]
  constructor <;>
  · unfold rawHamiltonian DomainWallSpectrum.H
    rw [hK, fromBlocks_mulVec]
    ext x; rcases x with i | i <;>
      simp [hop_uniform, back_uniform]

/-- **The identity completion is the unique zero-price completion**: pricing each invisible state
by its squared energy, every state has zero price exactly when the completion vanishes. -/
theorem zero_price_iff {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) :
    (∀ ψ : m → ℂ, ∑ i, Complex.normSq ((A *ᵥ ψ) i) = 0) ↔ A = 0 := by
  constructor
  · intro h
    apply Matrix.ext_of_mulVec_single
    intro j
    have hj := h (Pi.single j 1)
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)] at hj
    funext i
    simpa using Complex.normSq_eq_zero.mp (hj i (Finset.mem_univ i))
  · rintro rfl ψ; simp

end PMAction.EvenComplement
