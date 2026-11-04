import PMConstants.PacketTraceForm
import PMConstants.MeanTraceResponse

/-! Consequences of the actual packet trace indices for the ledger reading.
This distinguishes raw comparison counts from already channel-weighted
stiffness. It does not choose or fit a sector-dependent compensation. -/
noncomputable section
namespace PMConstants.GaugeTraceNormalization
open PMConstants Matrix PacketTraceForm PacketGaugeActions

/-- These inputs treat the manuscript ledgers as raw refresh weights, so the
packet indices multiply them. This is a conditional diagnostic, not a revised
coupling prediction. -/
def rawMixing (c : ℝ) : ℝ :=
  StiffnessIndices.gsqI c (10/3) (GaugeLedgers.ledger GaugeLedgers.reqY) /
    (StiffnessIndices.gsqI c 2 (GaugeLedgers.ledger GaugeLedgers.reqSU2)+
      StiffnessIndices.gsqI c (10/3) (GaugeLedgers.ledger GaugeLedgers.reqY))

theorem raw_mixing_exact {c : ℝ} (hc : 0 < c) : rawMixing c=5547/37777 := by
  rw [rawMixing,GaugeLedgers.su2_value,GaugeLedgers.hyper_value]
  rw [StiffnessIndices.indexed_mixing hc (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [overhead])]
  norm_num [overhead]

theorem common_calibration_cannot_fix {c : ℝ} (hc : 0 < c) : rawMixing c ≠ clockRatio := by
  rw [raw_mixing_exact hc]
  norm_num [clockRatio,footprint,overhead]

def adjustedMixing (kW kY : ℝ) : ℝ :=
  (2*kW*43)/(2*kW*43+(10/3)*kY*(footprint-43))

/-- The exact relative factor needed if raw ledgers and the stated generator
normalizations are retained. This computes an obligation, not its origin. -/
theorem compensation_iff {kW kY : ℝ} (hw : 0 < kW) (hy : 0 < kY) :
    adjustedMixing kW kY=clockRatio ↔ kY=(3/5)*kW := by
  have hf : (0 : ℝ) < footprint := by norm_num [footprint,overhead]
  have hb : (0 : ℝ) < footprint-43 := by norm_num [footprint,overhead]
  have hd : (0 : ℝ) < 2*kW*43+(10/3)*kY*(footprint-43) := by positivity
  rw [adjustedMixing,clockRatio,div_eq_div_iff hd.ne' hf.ne']
  norm_num [footprint,overhead]
  constructor <;> intro h <;> linarith

/-- Conversely, already index-weighted workloads recover the manuscript
fraction. Applying the indices again would count them twice. -/
theorem effective_work_matching (rW rY : ℝ)
    (hw : 2*rW=43) (hy : (10/3)*rY=footprint-43) :
    (2*rW)/(2*rW+(10/3)*rY)=clockRatio := by
  rw [hw,hy]
  simp [clockRatio]

/-- The joint trace form transported to the actual carrier basis. -/
theorem packet_joint_trace (A : Matrix (Fin 2) (Fin 2) ℂ)
    (B : Matrix (Fin 3) (Fin 3) ℂ) (b : ℝ) (ha : A.trace=0) (hb : B.trace=0) :
    (onPacket (joint A B b)*onPacket (joint A B b)).trace=
      4*(A*A).trace+4*(B*B).trace+(10/3 : ℂ)*(b : ℂ)^2 := by
  rw [packet_trace_product,joint_trace_square A B b ha hb]

/-- A fully constructed Hermitian joint generator has the normalized trace
as its controlled leading mean response, on the common sixteen-state space. -/
theorem joint_mean_response (A : Matrix (Fin 2) (Fin 2) ℂ)
    (B : Matrix (Fin 3) (Fin 3) ℂ) (b ε : ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (he : |ε| ≤ LinkSpectralResponse.HermitianTransport.radius (joint_hermitian A B b hA hB)) :
    |PMAction.InterferenceReadout.meanFlag
        (NormedSpace.exp (((ε : ℂ)*Complex.I) • joint A B b))-
      ε^2*((joint A B b*joint A B b).trace.re/64)| ≤
      MeanTraceResponse.coefficient (joint_hermitian A B b hA hB)*ε^4 := by
  have h := MeanTraceResponse.exponential_mean (joint_hermitian A B b hA hB) he
  norm_num [Channels,Q,Fintype.card_sum,Fintype.card_prod] at h
  exact h

/-- End-to-end controlled response on the actual carrier packet. No spectral
basis or small-step radius is supplied by the caller. The common uniform
comparison/readout convention is the one represented by meanFlag. -/
theorem packet_response (A : Matrix (Fin 2) (Fin 2) ℂ)
    (B : Matrix (Fin 3) (Fin 3) ℂ) (b : ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (ha : A.trace=0) (hb : B.trace=0) :
    let K := onPacket (joint A B b)
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ ε : ℝ, |ε| ≤ δ →
      |PMAction.InterferenceReadout.meanFlag (NormedSpace.exp (((ε : ℂ)*Complex.I) • K))-
        ε^2*((4*(A*A).trace.re+4*(B*B).trace.re+(10/3)*b^2)/64)| ≤ C*ε^4 := by
  let : Nonempty CarrierActions.Packet := Fintype.card_pos_iff.mp (by
    simp [CarrierActions.Packet,CarrierRepresentation.V,Fintype.card_sum,PMAction.CarrierEvents.carrier_card])
  let K := onPacket (joint A B b)
  have hk : K.IsHermitian := by
    change (onPacket (joint A B b))ᴴ=onPacket (joint A B b)
    rw [onPacket_star,(joint_hermitian A B b hA hB).eq]
  refine ⟨LinkSpectralResponse.HermitianTransport.radius hk,MeanTraceResponse.coefficient hk,
    LinkSpectralResponse.HermitianTransport.radius_pos hk,MeanTraceResponse.coefficient_nonneg hk,?_⟩
  intro ε he
  have h := MeanTraceResponse.exponential_mean hk he
  have hr : (K*K).trace.re=4*(A*A).trace.re+4*(B*B).trace.re+(10/3)*b^2 := by
    change (onPacket (joint A B b)*onPacket (joint A B b)).trace.re=_
    rw [packet_joint_trace A B b ha hb]
    norm_num [Complex.add_re,Complex.mul_re,pow_two]
  rw [hr] at h
  norm_num [CarrierActions.Packet,CarrierRepresentation.V,Fintype.card_sum,PMAction.CarrierEvents.carrier_card] at h
  exact h

end PMConstants.GaugeTraceNormalization
