import PMConstants.CarrierReadoutOrbits
import PMConstants.PacketTraceForm
import PMConstants.GaugeTraceNormalization
import PMConstants.WeightedReadoutResponse

/-! Response indices for every type-invariant incoherent basis preparation.
Weights are per carrier, not total type probabilities. Their physical
preparation/repair law is not selected by this classification. -/
noncomputable section
namespace PMConstants.GaugeReadoutWeights
open Matrix Finset PacketGaugeActions PacketTraceForm RequirementTable
open scoped Kronecker

/-- Type on the already constructed common packet blocks. -/
def channelType : Channels → Ty
  | .inl _ => .Q
  | .inr (.inl (_,s)) => if s=0 then .u else .d
  | .inr (.inr (.inl _)) => .L
  | .inr (.inr (.inr s)) => if s=0 then .n else .e

lemma channel_type_index : ∀ c : Channels, channelType c=ty (channelIndex c) := by decide +kernel

lemma actual_type (c : Channels) :
    CarrierActions.channelType (channelEquiv c)=channelType c := by
  rw [← CarrierActions.type_preserved,channelEquiv_index,← channel_type_index]

/-- The prepared basis law's weighted operator trace, before repair pricing. -/
def wtrace (w : Ty → ℝ) (X : M) : ℂ := ∑ c, (w (channelType c) : ℂ)*X c c

lemma wtrace_add (w : Ty → ℝ) (X Y : M) : wtrace w (X+Y)=wtrace w X+wtrace w Y := by
  simp [wtrace,mul_add,sum_add_distrib]
lemma wtrace_smul (w : Ty → ℝ) (a : ℂ) (X : M) : wtrace w (a • X)=a*wtrace w X := by
  simp [wtrace,← mul_sum,mul_left_comm]

/-- The weighted trace is on the actual carriers, not an unrelated copy. -/
theorem actual_wtrace (w : Ty → ℝ) (X : M) :
    (∑ v : CarrierActions.Packet, (CarrierReadoutOrbits.typed w v : ℂ)*(onPacket X) v v)=
      wtrace w X := by
  rw [← Equiv.sum_comp channelEquiv (fun v : CarrierActions.Packet =>
    (CarrierReadoutOrbits.typed w v : ℂ)*(onPacket X) v v)]
  simp [wtrace,CarrierReadoutOrbits.typed,actual_type,onPacket]

lemma actual_real_trace (w : Ty → ℝ) (X : M) :
    WeightedReadoutResponse.trace (CarrierReadoutOrbits.typed w) (onPacket X)=
      (wtrace w X).re := by
  rw [← actual_wtrace]
  simp [WeightedReadoutResponse.trace,Complex.re_sum]

/-- End-to-end comparison response on the actual carrier packet for any
nonnegative type weights. Probability normalization is a separate condition;
unormalized weights can instead describe supplied work intensities. -/
theorem actual_response (w : Ty → ℝ) (hw : ∀ t, 0 ≤ w t) (X : M)
    (hX : X.IsHermitian) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ ε : ℝ, |ε| ≤ δ →
      |WeightedReadoutResponse.score (CarrierReadoutOrbits.typed w)
        (NormedSpace.exp (((ε : ℂ)*Complex.I) • onPacket X))-
        ε^2*(wtrace w (X*X)).re/4| ≤ C*ε^4 := by
  have hk : (onPacket X).IsHermitian := by
    change (onPacket X)ᴴ=onPacket X
    rw [onPacket_star,hX.eq]
  have hp : ∀ v, 0 ≤ CarrierReadoutOrbits.typed w v := fun v => hw _
  refine ⟨LinkSpectralResponse.HermitianTransport.radius hk,
    WeightedReadoutResponse.coefficient (CarrierReadoutOrbits.typed w) hk,
    LinkSpectralResponse.HermitianTransport.radius_pos hk,
    WeightedReadoutResponse.coefficient_nonneg _ hp hk,?_⟩
  intro ε he
  have h := WeightedReadoutResponse.exponential _ hp hk he
  rw [← map_mul,actual_real_trace] at h
  exact h

set_option maxHeartbeats 800000 in
theorem weak_square (w : Ty → ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    wtrace w (weakGen A*weakGen A)=((3*w .Q+w .L : ℝ) : ℂ)*(A*A).trace := by
  simp [weakGen,wtrace,block,channelType,Fintype.sum_sum_type,
    Fintype.sum_prod_type,Fin.sum_univ_succ,Matrix.trace,Matrix.diag,
    Matrix.mul_apply]
  norm_num [Matrix.one_apply,Matrix.zero_apply]
  ring

set_option maxHeartbeats 800000 in
theorem colour_square (w : Ty → ℝ) (B : Matrix (Fin 3) (Fin 3) ℂ) :
    wtrace w (colourGen B*colourGen B)=((2*w .Q+w .u+w .d : ℝ) : ℂ)*(B*B).trace := by
  simp [colourGen,wtrace,block,channelType,Fintype.sum_sum_type,
    Fintype.sum_prod_type,Fin.sum_univ_succ,Matrix.trace,Matrix.diag,
    Matrix.mul_apply]
  norm_num [Matrix.one_apply,Matrix.zero_apply]
  ring

set_option maxHeartbeats 800000 in
theorem hyper_square (w : Ty → ℝ) : wtrace w (hyperGen*hyperGen)=
    ((w .Q/6+4*w .u/3+w .d/3+w .L/2+w .e : ℝ) : ℂ) := by
  norm_num [hyperGen,charge,Matrix.mul_smul,Matrix.smul_mul,block_mul,
    wtrace,block,channelType,Fintype.sum_sum_type,Fintype.sum_prod_type,
    Fin.sum_univ_succ,kronecker_apply,Matrix.mul_apply]
  norm_num [Matrix.one_apply,Matrix.zero_apply]
  ring

set_option maxHeartbeats 800000 in
lemma weak_colour_cross (w : Ty → ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (B : Matrix (Fin 3) (Fin 3) ℂ) :
    wtrace w (weakGen A*colourGen B)=(w .Q : ℂ)*B.trace*A.trace := by
  simp [weakGen,colourGen,wtrace,block,channelType,Fintype.sum_sum_type,
    Fintype.sum_prod_type,Fin.sum_univ_succ,Matrix.trace,Matrix.diag,Matrix.mul_apply]
  norm_num [Matrix.one_apply,Matrix.zero_apply]
  ring

set_option maxHeartbeats 800000 in
lemma weak_hyper_cross (w : Ty → ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    wtrace w (weakGen A*hyperGen)=((w .Q-w .L : ℝ) : ℂ)/2*A.trace := by
  simp [weakGen,hyperGen,charge,wtrace,block,channelType,Fintype.sum_sum_type,
    Fintype.sum_prod_type,Fin.sum_univ_succ,Matrix.trace,Matrix.diag,Matrix.mul_apply]
  norm_num [Matrix.one_apply,Matrix.zero_apply]
  ring

set_option maxHeartbeats 800000 in
lemma colour_hyper_cross (w : Ty → ℝ) (B : Matrix (Fin 3) (Fin 3) ℂ) :
    wtrace w (colourGen B*hyperGen)=((w .Q+2*w .u-w .d : ℝ) : ℂ)/3*B.trace := by
  simp [colourGen,hyperGen,charge,wtrace,block,channelType,Fintype.sum_sum_type,
    Fintype.sum_prod_type,Fin.sum_univ_succ,Matrix.trace,Matrix.diag,Matrix.mul_apply]
  norm_num [Matrix.one_apply,Matrix.zero_apply]
  ring

lemma weak_colour_commute (A : Matrix (Fin 2) (Fin 2) ℂ)
    (B : Matrix (Fin 3) (Fin 3) ℂ) : weakGen A*colourGen B=colourGen B*weakGen A := by
  simp [weakGen,colourGen,block_mul,← mul_kronecker_mul]

lemma weak_hyper_commute (A : Matrix (Fin 2) (Fin 2) ℂ) :
    weakGen A*hyperGen=hyperGen*weakGen A := by
  simp [weakGen,hyperGen,charge,block_mul]

lemma colour_hyper_commute (B : Matrix (Fin 3) (Fin 3) ℂ) :
    colourGen B*hyperGen=hyperGen*colourGen B := by
  simp [colourGen,hyperGen,charge,block_mul,
    ← mul_kronecker_mul]

/-- Type-invariant preparation retains the joint gauge quadratic form.
All mixed terms vanish for traceless fundamental non-Abelian generators. -/
theorem joint_square (w : Ty → ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (B : Matrix (Fin 3) (Fin 3) ℂ) (b : ℝ) (ha : A.trace=0) (hb : B.trace=0) :
    wtrace w (joint A B b*joint A B b)=
      ((3*w .Q+w .L : ℝ) : ℂ)*(A*A).trace+
      ((2*w .Q+w .u+w .d : ℝ) : ℂ)*(B*B).trace+
      ((w .Q/6+4*w .u/3+w .d/3+w .L/2+w .e : ℝ) : ℂ)*(b : ℂ)^2 := by
  simp only [joint,add_mul,mul_add,Matrix.smul_mul,Matrix.mul_smul,wtrace_add,wtrace_smul,
    ← weak_colour_commute,← weak_hyper_commute,← colour_hyper_commute,
    weak_square,colour_square,hyper_square,weak_colour_cross,weak_hyper_cross,
    colour_hyper_cross,ha,hb,mul_zero]
  ring

def weakIndex (w : Ty → ℝ) : ℝ := (3*w .Q+w .L)/2
def colourIndex (w : Ty → ℝ) : ℝ := (2*w .Q+w .u+w .d)/2
def hyperIndex (w : Ty → ℝ) : ℝ := w .Q/6+4*w .u/3+w .d/3+w .L/2+w .e

/-- All three actual trace-response coefficients at the stated fundamental
normalization. Unlike an unweighted support count these include charge squares. -/
theorem response_indices (w : Ty → ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (B : Matrix (Fin 3) (Fin 3) ℂ) (ha : (A*A).trace=1/2) (hb : (B*B).trace=1/2) :
    wtrace w (weakGen A*weakGen A)=(weakIndex w : ℂ) ∧
    wtrace w (colourGen B*colourGen B)=(colourIndex w : ℂ) ∧
    wtrace w (hyperGen*hyperGen)=(hyperIndex w : ℂ) := by
  rw [weak_square,colour_square,hyper_square,ha,hb]
  norm_num [weakIndex,colourIndex,hyperIndex]
  constructor <;> ring

/-- Equal sector response is two explicit linear constraints on preparation,
not a consequence of preserving each type orbit. -/
theorem equal_indices_iff (w : Ty → ℝ) :
    (weakIndex w=colourIndex w ∧ weakIndex w=hyperIndex w) ↔
      (w .Q+w .L=w .u+w .d ∧ 4*w .Q=4*w .u+w .d+3*w .e) := by
  unfold weakIndex colourIndex hyperIndex
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

def uniformWeights : Ty → ℝ := fun _ => 1/16

theorem uniform_indices : weakIndex uniformWeights=1/8 ∧
    colourIndex uniformWeights=1/8 ∧ hyperIndex uniformWeights=5/24 := by
  norm_num [weakIndex,colourIndex,hyperIndex,uniformWeights]

/-- An exact counterexample to uniqueness of the preparation law. Its small
integers are a mathematical witness, not a proposed substrate mechanism. -/
def equalIndexWitness : Ty → ℝ
  | .Q => 6/73 | .u => 3/73 | .d => 6/73 | .L => 3/73 | .e => 2/73 | .n => 2/73

theorem witness_positive_normalized :
    PersistenceMechanics.LawSelection.PosLaw (CarrierReadoutOrbits.typed equalIndexWitness) := by
  apply (CarrierReadoutOrbits.positive_law_iff _).mpr
  constructor
  · intro t; cases t <;> norm_num [equalIndexWitness]
  · norm_num [equalIndexWitness]

theorem witness_equal_indices : weakIndex equalIndexWitness=21/146 ∧
    colourIndex equalIndexWitness=21/146 ∧ hyperIndex equalIndexWitness=21/146 := by
  norm_num [weakIndex,colourIndex,hyperIndex,equalIndexWitness]

/-- The readout-dependent mixing diagnostic keeps the supplied raw workloads. -/
def mixing (w : Ty → ℝ) : ℝ :=
  weakIndex w*43/(weakIndex w*43+hyperIndex w*(footprint-43))

/-- With positive response, the manuscript mixing is equivalent to an exact
constraint on the preparation weights, not to arbitrary sector calibration. -/
theorem target_mixing_iff (w : Ty → ℝ) (hw : 0 < weakIndex w) (hy : 0 < hyperIndex w) :
    mixing w=clockRatio ↔ 4*w .Q=4*w .u+w .d+3*w .e := by
  have hf : (0 : ℝ)<footprint := by norm_num [footprint,overhead]
  have hl : (0 : ℝ)<footprint-43 := by norm_num [footprint,overhead]
  have hd : (0 : ℝ)<weakIndex w*43+hyperIndex w*(footprint-43) := by positivity
  rw [mixing,clockRatio,div_eq_div_iff hd.ne' hf.ne']
  norm_num [footprint,overhead,weakIndex,hyperIndex]
  constructor <;> intro h <;> linarith

theorem uniform_mixing : mixing uniformWeights=5547/37777 := by
  norm_num [mixing,weakIndex,hyperIndex,uniformWeights,footprint,overhead]

theorem witness_mixing : mixing equalIndexWitness=clockRatio := by
  norm_num [mixing,weakIndex,hyperIndex,equalIndexWitness,clockRatio,footprint,overhead]

lemma typed_uniform : CarrierReadoutOrbits.typed uniformWeights=
    (PersistenceMechanics.LawSelection.uniform : CarrierActions.Packet → ℝ) := by
  funext v
  norm_num [CarrierReadoutOrbits.typed,uniformWeights,PersistenceMechanics.LawSelection.uniform,
    CarrierActions.Packet,CarrierRepresentation.V,Fintype.card_sum,PMAction.CarrierEvents.carrier_card]

/-- If the existing average-return minimization is applied to these probes over
the symmetric positive laws, it selects the uniform result, not equal indices.
That application itself still needs a physical return-cost interpretation. -/
theorem return_minimum_raw_mixing (w : Ty → ℝ)
    (hp : PersistenceMechanics.LawSelection.PosLaw (CarrierReadoutOrbits.typed w))
    (hopt : ∀ z : Ty → ℝ, PersistenceMechanics.LawSelection.PosLaw (CarrierReadoutOrbits.typed z) →
      PersistenceMechanics.LawSelection.averageRate (CarrierReadoutOrbits.typed w) ≤
        PersistenceMechanics.LawSelection.averageRate (CarrierReadoutOrbits.typed z)) :
    mixing w=5547/37777 := by
  have : Nonempty CarrierActions.Packet := ⟨CarrierActions.enumeration.symm 0⟩
  have hu : PersistenceMechanics.LawSelection.PosLaw (CarrierReadoutOrbits.typed uniformWeights) := by
    rw [typed_uniform]; exact PersistenceMechanics.LawSelection.uniform_law
  have he : CarrierReadoutOrbits.typed w=PersistenceMechanics.LawSelection.uniform := by
    apply (PersistenceMechanics.LawSelection.averageRate_eq_iff hp).mp
    apply le_antisymm
    · simpa only [typed_uniform,PersistenceMechanics.LawSelection.uniform_averageRate] using
        hopt uniformWeights hu
    · exact PersistenceMechanics.LawSelection.averageRate_ge hp
  have hw : w=uniformWeights := CarrierReadoutOrbits.weights_unique w uniformWeights
    (he.trans typed_uniform.symm)
  rw [hw]; exact uniform_mixing

end PMConstants.GaugeReadoutWeights
