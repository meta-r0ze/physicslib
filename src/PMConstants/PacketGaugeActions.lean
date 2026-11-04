import PMConstants.CarrierActions
import PMConstants.LinkEvolution
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.Matrix.Block

/-! Common unitary weak and colour actions on the actual packet, with the
existing hypercharge assignment. The inherited axis/chirality interpretation
is not derived here. Restriction to SU(2)/SU(3) is possible; uniqueness or
physical selection of those subgroups and their normalization is not proved. -/
noncomputable section
namespace PMConstants.PacketGaugeActions
open Matrix Finset
open scoped Kronecker

abbrev Q := Fin 3 × Fin 2
abbrev Channels := Q ⊕ (Q ⊕ (Fin 2 ⊕ Fin 2))
abbrev M := Matrix Channels Channels ℂ

def channelIndex : Channels → Fin 16
  | .inl (c,s) => ⟨2*c.val+s.val,by omega⟩
  | .inr (.inl (c,s)) => if s=0 then ⟨6+c.val,by omega⟩ else ⟨9+c.val,by omega⟩
  | .inr (.inr (.inl s)) => ⟨12+s.val,by omega⟩
  | .inr (.inr (.inr s)) => if s=0 then 15 else 14

theorem channel_index_bijective : Function.Bijective channelIndex := by decide +kernel

def channelEquiv : Channels ≃ CarrierActions.Packet :=
  (Equiv.ofBijective channelIndex channel_index_bijective).trans CarrierActions.enumeration.symm

lemma channelEquiv_index (c : Channels) : CarrierActions.index (channelEquiv c)=channelIndex c := by
  change CarrierActions.enumeration (CarrierActions.enumeration.symm (channelIndex c))=channelIndex c
  exact CarrierActions.enumeration.apply_symm_apply _

def flipWeak : Channels → Channels
  | .inl (c,s) => .inl (c,s.rev)
  | .inr (.inr (.inl s)) => .inr (.inr (.inl s.rev))
  | c => c

def permuteColour (a b : Fin 3) : Channels → Channels
  | .inl (c,s) => .inl (Equiv.swap a b c,s)
  | .inr (.inl (c,s)) => .inr (.inl (Equiv.swap a b c,s))
  | c => c

lemma weak_index_compat : ∀ (c : Channels) (v : CarrierActions.Packet),
    channelIndex c=CarrierActions.index v →
      channelIndex (flipWeak c)=CarrierActions.index (CarrierActions.weak v) := by decide +kernel

lemma colour_index_compat : ∀ (a b : Fin 3) (c : Channels) (v : CarrierActions.Packet),
    channelIndex c=CarrierActions.index v →
      channelIndex (permuteColour a b c)=CarrierActions.index (CarrierActions.colour a b v) := by
  decide +kernel

theorem weak_label_matches (c : Channels) :
    channelEquiv (flipWeak c)=CarrierActions.weak (channelEquiv c) := by
  apply CarrierActions.index_bijective.1
  rw [channelEquiv_index]
  exact weak_index_compat c _ (channelEquiv_index c).symm

theorem colour_label_matches (a b : Fin 3) (c : Channels) :
    channelEquiv (permuteColour a b c)=CarrierActions.colour a b (channelEquiv c) := by
  apply CarrierActions.index_bijective.1
  rw [channelEquiv_index]
  exact colour_index_compat a b c _ (channelEquiv_index c).symm

def block (A B : Matrix Q Q ℂ) (C D : Matrix (Fin 2) (Fin 2) ℂ) : M :=
  fromBlocks A 0 0 (fromBlocks B 0 0 (fromBlocks C 0 0 D))

lemma block_mul (A B A' B' : Matrix Q Q ℂ) (C D C' D' : Matrix (Fin 2) (Fin 2) ℂ) :
    block A B C D*block A' B' C' D'=block (A*A') (B*B') (C*C') (D*D') := by
  simp [block,fromBlocks_multiply]

lemma block_star (A B : Matrix Q Q ℂ) (C D : Matrix (Fin 2) (Fin 2) ℂ) :
    (block A B C D)ᴴ=block Aᴴ Bᴴ Cᴴ Dᴴ := by simp [block,fromBlocks_conjTranspose]

lemma block_one : block 1 1 1 1=1 := by simp [block,fromBlocks_one]

lemma block_unitary (A B : Matrix Q Q ℂ) (C D : Matrix (Fin 2) (Fin 2) ℂ)
    (ha : A ∈ unitary _) (hb : B ∈ unitary _) (hc : C ∈ unitary _) (hd : D ∈ unitary _) :
    block A B C D ∈ unitary M := by
  have ha1 : Aᴴ*A=1 := ha.1
  have hb1 : Bᴴ*B=1 := hb.1
  have hc1 : Cᴴ*C=1 := hc.1
  have hd1 : Dᴴ*D=1 := hd.1
  have ha2 : A*Aᴴ=1 := ha.2
  have hb2 : B*Bᴴ=1 := hb.2
  have hc2 : C*Cᴴ=1 := hc.2
  have hd2 : D*Dᴴ=1 := hd.2
  constructor
  · change (block A B C D)ᴴ*block A B C D=1
    rw [block_star,block_mul,ha1,hb1,hc1,hd1,block_one]
  · change block A B C D*(block A B C D)ᴴ=1
    rw [block_star,block_mul,ha2,hb2,hc2,hd2,block_one]

lemma tensor_unitary {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (A : Matrix a a ℂ) (B : Matrix b b ℂ) (ha : A ∈ unitary _) (hb : B ∈ unitary _) :
    A ⊗ₖ B ∈ unitary (Matrix (a × b) (a × b) ℂ) := by
  have ha1 : Aᴴ*A=1 := ha.1
  have hb1 : Bᴴ*B=1 := hb.1
  have ha2 : A*Aᴴ=1 := ha.2
  have hb2 : B*Bᴴ=1 := hb.2
  constructor
  · change (A ⊗ₖ B)ᴴ*(A ⊗ₖ B)=1
    rw [conjTranspose_kronecker,← mul_kronecker_mul,ha1,hb1,one_kronecker_one]
  · change (A ⊗ₖ B)*(A ⊗ₖ B)ᴴ=1
    rw [conjTranspose_kronecker,← mul_kronecker_mul,ha2,hb2,one_kronecker_one]

def weak (U : Matrix (Fin 2) (Fin 2) ℂ) : M := block (1 ⊗ₖ U) 1 U 1
def colour (V : Matrix (Fin 3) (Fin 3) ℂ) : M := block (V ⊗ₖ 1) (V ⊗ₖ 1) 1 1

theorem weak_one : weak 1=1 := by simp [weak,block_one]
theorem colour_one : colour 1=1 := by simp [colour,block_one]

theorem weak_mul (U V : Matrix (Fin 2) (Fin 2) ℂ) : weak (U*V)=weak U*weak V := by
  simp [weak,block_mul,← mul_kronecker_mul]

theorem colour_mul (U V : Matrix (Fin 3) (Fin 3) ℂ) : colour (U*V)=colour U*colour V := by
  simp [colour,block_mul,← mul_kronecker_mul]

theorem factors_commute (U : Matrix (Fin 2) (Fin 2) ℂ) (V : Matrix (Fin 3) (Fin 3) ℂ) :
    weak U*colour V=colour V*weak U := by
  simp [weak,colour,block_mul,← mul_kronecker_mul]

theorem weak_unitary (U : Matrix (Fin 2) (Fin 2) ℂ) (hu : U ∈ unitary _) :
    weak U ∈ unitary M :=
  block_unitary _ _ _ _ (tensor_unitary _ U (one_mem _) hu) (one_mem _) hu (one_mem _)

theorem colour_unitary (V : Matrix (Fin 3) (Fin 3) ℂ) (hv : V ∈ unitary _) :
    colour V ∈ unitary M :=
  block_unitary _ _ _ _ (tensor_unitary V _ hv (one_mem _))
    (tensor_unitary V _ hv (one_mem _)) (one_mem _) (one_mem _)

/-- Existing Y charges, with right order (u,d) and (neutral,electron). -/
def charge : M := block ((1/3 : ℂ) • 1) (1 ⊗ₖ diagonal ![4/3,-2/3])
  ((-1 : ℂ) • 1) (diagonal ![0,-2])

theorem weak_charge (U : Matrix (Fin 2) (Fin 2) ℂ) : weak U*charge=charge*weak U := by
  simp [weak,charge,block_mul]

theorem colour_charge (V : Matrix (Fin 3) (Fin 3) ℂ) : colour V*charge=charge*colour V := by
  simp [colour,charge,block_mul,← mul_kronecker_mul]

theorem charge_hermitian : charge.IsHermitian := by
  have hd : star (![4/3,-2/3] : Fin 2 → ℂ)=![4/3,-2/3] := by
    funext i; fin_cases i <;> norm_num
  have he : star (![0,-2] : Fin 2 → ℂ)=![0,-2] := by
    funext i; fin_cases i <;> norm_num
  change chargeᴴ=charge
  simp [charge,block_star,conjTranspose_kronecker,diagonal_conjTranspose,hd,he]

def weakRepresentation : unitary (Matrix (Fin 2) (Fin 2) ℂ) →* unitary M where
  toFun U := ⟨weak U,weak_unitary U U.prop⟩
  map_one' := by apply Subtype.ext; exact weak_one
  map_mul' U V := by apply Subtype.ext; exact weak_mul U V

def colourRepresentation : unitary (Matrix (Fin 3) (Fin 3) ℂ) →* unitary M where
  toFun V := ⟨colour V,colour_unitary V V.prop⟩
  map_one' := by apply Subtype.ext; exact colour_one
  map_mul' U V := by apply Subtype.ext; exact colour_mul U V

/-- Real-parameter hypercharge transport; no period or global gauge quotient
is selected merely by this definition. -/
def hypercharge (t : ℝ) : M := LinkSpectralResponse.HermitianTransport.transport charge_hermitian t

theorem hypercharge_unitary (t : ℝ) : hypercharge t ∈ unitary M :=
  LinkSpectralResponse.HermitianTransport.transport_unitary _ _

open scoped Matrix.Norms.Operator in
theorem weak_hypercharge (U : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    weak U*hypercharge t=hypercharge t*weak U := by
  unfold hypercharge
  rw [LinkEvolution.transport_eq_exp]
  have hc : Commute (weak U) charge := weak_charge U
  exact (hc.smul_right ((t : ℂ)*Complex.I)).exp_right

open scoped Matrix.Norms.Operator in
theorem colour_hypercharge (V : Matrix (Fin 3) (Fin 3) ℂ) (t : ℝ) :
    colour V*hypercharge t=hypercharge t*colour V := by
  unfold hypercharge
  rw [LinkEvolution.transport_eq_exp]
  have hc : Commute (colour V) charge := colour_charge V
  exact (hc.smul_right ((t : ℂ)*Complex.I)).exp_right

/-- The block charges agree with the original indexed representation table. -/
theorem charge_table : ∀ c : Channels, charge c c=
    (RequirementTable.hyper Hypercharge.standard (RequirementTable.ty (channelIndex c)) : ℂ) := by
  intro c
  fin_cases c <;> norm_num [charge,block,channelIndex,RequirementTable.hyper,
    Hypercharge.standard,RequirementTable.ty,Matrix.kroneckerMap_apply]

/-- Reindexing by the actual carrier bijection preserves the algebra. -/
def onPacket : M ≃ₐ[ℂ] Matrix CarrierActions.Packet CarrierActions.Packet ℂ :=
  reindexAlgEquiv ℂ ℂ channelEquiv

lemma onPacket_star (A : M) : (onPacket A)ᴴ=onPacket Aᴴ :=
  conjTranspose_reindex channelEquiv channelEquiv A

theorem packet_unitary (A : M) (ha : A ∈ unitary M) :
    onPacket A ∈ unitary (Matrix CarrierActions.Packet CarrierActions.Packet ℂ) := by
  have h1 : Aᴴ*A=1 := ha.1
  have h2 : A*Aᴴ=1 := ha.2
  constructor
  · change (onPacket A)ᴴ*onPacket A=1
    rw [onPacket_star,← map_mul,h1,map_one]
  · change onPacket A*(onPacket A)ᴴ=1
    rw [onPacket_star,← map_mul,h2,map_one]

theorem packet_factors_commute (U : Matrix (Fin 2) (Fin 2) ℂ)
    (V : Matrix (Fin 3) (Fin 3) ℂ) :
    onPacket (weak U)*onPacket (colour V)=onPacket (colour V)*onPacket (weak U) := by
  rw [← map_mul,← map_mul,factors_commute]

/-- The common packet link is unitary whenever the supplied weak and colour
factors are unitary. Hypercharge transport is constructed, not assumed unitary. -/
theorem joint_packet_unitary (U : Matrix (Fin 2) (Fin 2) ℂ)
    (V : Matrix (Fin 3) (Fin 3) ℂ) (t : ℝ)
    (hu : U ∈ unitary _) (hv : V ∈ unitary _) :
    onPacket (weak U*colour V*hypercharge t) ∈ unitary _ := by
  apply packet_unitary
  exact (unitary M).mul_mem ((unitary M).mul_mem (weak_unitary U hu) (colour_unitary V hv))
    (hypercharge_unitary t)

end PMConstants.PacketGaugeActions
