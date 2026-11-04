import PMConstants.GaugeReadoutWeights

/-! Stationary diagonal preparation under inter-type transfer. The generator,
nonzero hopping entries and basis-diagonal preparation remain explicit. The
result does not classify coherent stationary states or select a vacuum update. -/
noncomputable section
namespace PMConstants.LinkPreparation
open Matrix Finset CarrierActions CarrierReadoutOrbits GaugeReadoutWeights

section General
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def density (p : ι → ℝ) : Matrix ι ι ℂ := diagonal (fun i => (p i : ℂ))

/-- A diagonal density commutes with the generator exactly when its weights
agree across every nonzero matrix entry. No positivity or Hermiticity is needed
for this purely algebraic criterion. -/
theorem diagonal_commutes_iff (p : ι → ℝ) (H : Matrix ι ι ℂ) :
    density p*H=H*density p ↔ ∀ i j, H i j ≠ 0 → p i=p j := by
  constructor
  · intro h i j hij
    have he := congrArg (fun X : Matrix ι ι ℂ => X i j) h
    simp only [density,diagonal_mul,mul_diagonal] at he
    have hz : ((p i : ℂ)-(p j : ℂ))*H i j=0 := by linear_combination he
    have hp := (mul_eq_zero.mp hz).resolve_right hij
    exact_mod_cast sub_eq_zero.mp hp
  · intro hp
    ext i j
    simp only [density,diagonal_mul,mul_diagonal]
    by_cases hij : H i j=0
    · simp [hij]
    · rw [hp i j hij,mul_comm]

open scoped Matrix.Norms.Operator in
/-- Generator commutation gives exact finite-time stationarity, not merely a
leading-order equality. Preparation is diagonal; coherent densities are outside
this definition and theorem. -/
theorem stationary_evolution (p : ι → ℝ) (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (hs : density p*H=H*density p) (t : ℝ) :
    let U := LinkSpectralResponse.HermitianTransport.transport hH t
    U*density p*Uᴴ=density p := by
  intro U
  have hc : Commute (density p) H := hs
  have he := (hc.smul_right ((t : ℂ)*Complex.I)).exp_right
  have hu : U*Uᴴ=1 := (LinkSpectralResponse.HermitianTransport.transport_unitary hH t).2
  have he' : density p*U=U*density p := by
    simpa only [U,LinkEvolution.transport_eq_exp] using he.eq
  rw [← he',Matrix.mul_assoc,hu,mul_one]
end General

/-- At least one nonzero Q-u and one nonzero Q-d transfer, with their actual
carrier labels. This is a supplied dynamical condition, not derived from the
charge-difference equations of SectorLinks. -/
structure QuarkHops (H : Matrix Packet Packet ℂ) : Prop where
  up : ∃ v u : Packet, CarrierActions.channelType v=.Q ∧
    CarrierActions.channelType u=.u ∧ H v u ≠ 0
  down : ∃ v d : Packet, CarrierActions.channelType v=.Q ∧
    CarrierActions.channelType d=.d ∧ H v d ≠ 0

theorem stationary_quark_weights (w : RequirementTable.Ty → ℝ)
    (H : Matrix Packet Packet ℂ) (hh : QuarkHops H)
    (hs : density (typed w)*H=H*density (typed w)) : w .Q=w .u ∧ w .Q=w .d := by
  have he := (diagonal_commutes_iff (typed w) H).mp hs
  obtain ⟨v,u,hv,hu,hvu⟩ := hh.up
  obtain ⟨v',d,hv',hd,hvd⟩ := hh.down
  exact ⟨by simpa only [typed,hv,hu] using he v u hvu,
    by simpa only [typed,hv',hd] using he v' d hvd⟩

/-- The index gap is positive under a positive type preparation, even without
assuming electron/sterile inter-sector hops. -/
theorem stationary_index_gap (w : RequirementTable.Ty → ℝ)
    (H : Matrix Packet Packet ℂ) (hh : QuarkHops H)
    (hs : density (typed w)*H=H*density (typed w)) :
    hyperIndex w-weakIndex w=w .Q/3+w .e := by
  obtain ⟨hu,hd⟩ := stationary_quark_weights w H hh hs
  unfold hyperIndex weakIndex
  rw [← hu,← hd]
  ring

theorem equal_quarks_mixing_below_target (w : RequirementTable.Ty → ℝ)
    (hw : ∀ ty, 0 < w ty) (hu : w .Q=w .u) (hd : w .Q=w .d) : mixing w<clockRatio := by
  have hg : hyperIndex w-weakIndex w=w .Q/3+w .e := by
    unfold hyperIndex weakIndex
    rw [← hu,← hd]
    ring
  have hq := hw .Q
  have hl := hw .L
  have he := hw .e
  have hi : 0 < weakIndex w := by unfold weakIndex; positivity
  have hj : weakIndex w<hyperIndex w := by linarith
  have hy : 0 < hyperIndex w := by linarith
  have hf : (0 : ℝ)<footprint := by norm_num [footprint,overhead]
  have hr : (0 : ℝ)<footprint-43 := by norm_num [footprint,overhead]
  have hd : (0 : ℝ)<weakIndex w*43+hyperIndex w*(footprint-43) := by positivity
  rw [mixing,clockRatio,div_lt_div_iff₀ hd hf]
  norm_num [footprint,overhead]
  linarith

theorem stationary_mixing_below_target (w : RequirementTable.Ty → ℝ)
    (hw : ∀ ty, 0 < w ty) (H : Matrix Packet Packet ℂ) (hh : QuarkHops H)
    (hs : density (typed w)*H=H*density (typed w)) : mixing w<clockRatio := by
  obtain ⟨hu,hd⟩ := stationary_quark_weights w H hh hs
  exact equal_quarks_mixing_below_target w hw hu hd

/-- A whole family of flavour-diagonal Hermitian inter-sector links on the
actual packet. It illustrates the hop assumptions without selecting amplitudes
or identifying this family with the full Paper II domain-wall generator. -/
def transfer (m : CarrierRepresentation.V → ℂ) : Matrix Packet Packet ℂ :=
  fromBlocks 0 (diagonal m) (diagonal m)ᴴ 0

theorem transfer_hermitian (m : CarrierRepresentation.V → ℂ) : (transfer m).IsHermitian := by
  change (transfer m)ᴴ=transfer m
  simp [transfer,fromBlocks_conjTranspose]

def upCarrier : CarrierRepresentation.V := ⟨![2,4,2,2],by decide +kernel⟩
def downCarrier : CarrierRepresentation.V := ⟨![2,0,2,2],by decide +kernel⟩

lemma up_types : CarrierRepresentation.leftType upCarrier=.Q ∧
    CarrierRepresentation.rightType upCarrier=.u := by decide +kernel
lemma down_types : CarrierRepresentation.leftType downCarrier=.Q ∧
    CarrierRepresentation.rightType downCarrier=.d := by decide +kernel

theorem transfer_quark_hops (m : CarrierRepresentation.V → ℂ)
    (hu : m upCarrier ≠ 0) (hd : m downCarrier ≠ 0) : QuarkHops (transfer m) := by
  constructor
  · refine ⟨.inl upCarrier,.inr upCarrier,up_types.1,up_types.2,?_⟩
    simpa only [transfer,fromBlocks_apply₁₂,diagonal_apply_eq] using hu
  · refine ⟨.inl downCarrier,.inr downCarrier,down_types.1,down_types.2,?_⟩
    simpa only [transfer,fromBlocks_apply₁₂,diagonal_apply_eq] using hd

/-- For the isolated-pair transfer family, even a general coherent matrix
commuting with the generator has equal populations on the two ends of each
nonzero pair. No positivity or diagonal-density assumption is needed. -/
theorem coherent_pair_diagonal (ρ : Matrix Packet Packet ℂ)
    (m : CarrierRepresentation.V → ℂ) (hs : ρ*transfer m=transfer m*ρ)
    (v : CarrierRepresentation.V) (hm : m v ≠ 0) :
    ρ (.inl v) (.inl v)=ρ (.inr v) (.inr v) := by
  have he := congrArg (fun X : Matrix Packet Packet ℂ => X (.inl v) (.inr v)) hs
  simp [transfer,Matrix.mul_apply,Fintype.sum_sum_type,diagonal] at he
  have hz : (ρ (.inl v) (.inl v)-ρ (.inr v) (.inr v))*m v=0 := by
    linear_combination he
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hm)

/-- Coherences cannot supply the proposed compensation within this particular
zero-onsite, pairwise transfer family. General Hamiltonians with onsite terms
or additional inter-type couplings are not excluded by this result. -/
theorem coherent_transfer_below_target (ρ : Matrix Packet Packet ℂ)
    (m : CarrierRepresentation.V → ℂ) (hu : m upCarrier ≠ 0) (hd : m downCarrier ≠ 0)
    (hs : ρ*transfer m=transfer m*ρ) (w : RequirementTable.Ty → ℝ)
    (hw : ∀ ty, 0 < w ty) (hdiag : ∀ v, (ρ v v).re=typed w v) : mixing w<clockRatio := by
  have hup := congrArg Complex.re (coherent_pair_diagonal ρ m hs upCarrier hu)
  have hdn := congrArg Complex.re (coherent_pair_diagonal ρ m hs downCarrier hd)
  simp only [hdiag,typed,CarrierActions.channelType] at hup
  simp only [hdiag,typed,CarrierActions.channelType] at hdn
  exact equal_quarks_mixing_below_target w hw hup hdn

end PMConstants.LinkPreparation
