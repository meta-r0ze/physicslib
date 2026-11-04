import PMConstants.GaugeReadoutWeights

/-! A paired carrier-reflection action tests the six-type preparation freedom.
Its availability does not imply invariance of the selected vacuum readout.
The result keeps that symmetry hypothesis and the raw-ledger interpretation
explicit. No physical coupling formula is changed. -/
noncomputable section
namespace PMConstants.PrimitiveReadoutSymmetry
open CarrierActions CarrierReadoutOrbits GaugeReadoutWeights RequirementTable

/-- Simultaneous lift of Paper II's carrier reflection to both vector-class
sectors. It swaps axes 0 and 1 in each. The paired action is not assigned the
cost of a single primitive E8 event. -/
def root : Equiv.Perm Packet := Equiv.sumCongr
  (PMAction.CarrierEvents.reflect 0) (PMAction.CarrierEvents.reflect 0)

/-- Sector-local lifts, kept separate for primitive-event accounting. -/
def leftRoot : Equiv.Perm Packet := Equiv.sumCongr
  (PMAction.CarrierEvents.reflect 0) (Equiv.refl CarrierRepresentation.V)
def rightRoot : Equiv.Perm Packet := Equiv.sumCongr
  (Equiv.refl CarrierRepresentation.V) (PMAction.CarrierEvents.reflect 0)

theorem paired_decomposition : leftRoot.trans rightRoot=root := by
  ext v; cases v <;> rfl

def rootIndex : Fin 16 → Fin 16 := ![12,13,2,3,4,5,15,7,8,14,10,11,0,1,9,6]

lemma root_index : ∀ v : Packet, index (root v)=rootIndex (index v) := by decide +kernel

lemma typed_root_index (w : Ty → ℝ) (i : Fin 16) :
    typed w (root (enumeration.symm i))=w (ty (rootIndex i)) := by
  unfold typed
  rw [← type_preserved,root_index]
  have hi : index (enumeration.symm i)=i := enumeration.apply_symm_apply i
  rw [hi]

/-- The existing root action equates the lepton/colour weights within the
left sector and within each right-sector sign. No sector exchange is assumed. -/
theorem root_invariant_iff (w : Ty → ℝ) :
    (∀ v : Packet, typed w (root v)=typed w v) ↔
      (w .Q=w .L ∧ w .u=w .n ∧ w .d=w .e) := by
  constructor
  · intro h
    have hq := h (enumeration.symm 0)
    have hu := h (enumeration.symm 6)
    have hd := h (enumeration.symm 9)
    rw [typed_root_index] at hq hu hd
    norm_num [typed,enumeration_type,rootIndex,ty] at hq hu hd
    exact ⟨hq.symm,hu.symm,hd.symm⟩
  · rintro ⟨hq,hu,hd⟩
    have hi : ∀ i : Fin 16, typed w (root (enumeration.symm i))=typed w (enumeration.symm i) := by
      intro i
      rw [typed_root_index]
      simp only [typed,enumeration_type]
      fin_cases i <;> norm_num [rootIndex,ty] <;> simp_all
    intro v
    simpa only [enumeration.symm_apply_apply] using hi (enumeration v)

/-- With root-invariant preparation and equal weak/colour response, the
hypercharge/weak ratio 5/3 persists even without uniform carrier sampling. -/
theorem index_ratio_forced (w : Ty → ℝ)
    (hr : ∀ v : Packet, typed w (root v)=typed w v)
    (hc : weakIndex w=colourIndex w) : hyperIndex w=(5/3)*weakIndex w := by
  obtain ⟨hq,_,hd⟩ := (root_invariant_iff w).mp hr
  unfold weakIndex colourIndex at hc
  unfold hyperIndex weakIndex
  rw [← hq] at hc ⊢
  rw [← hd]
  linarith

theorem raw_mixing_forced (w : Ty → ℝ) (hw : 0 < weakIndex w)
    (hr : ∀ v : Packet, typed w (root v)=typed w v)
    (hc : weakIndex w=colourIndex w) : mixing w=5547/37777 := by
  have hy := index_ratio_forced w hr hc
  rw [mixing,hy]
  have hn : weakIndex w ≠ 0 := hw.ne'
  norm_num [footprint,overhead]
  field_simp
  ring

/-- Equal positive weak/colour/hypercharge response must break invariance of
this root action within the supplied incoherent preparation model. -/
theorem equal_response_breaks_root (w : Ty → ℝ) (hw : 0 < weakIndex w)
    (hc : weakIndex w=colourIndex w) (hy : weakIndex w=hyperIndex w) :
    ¬ ∀ v : Packet, typed w (root v)=typed w v := by
  intro hr
  have he := index_ratio_forced w hr hc
  linarith

/-- Relative strong/electric response under the same raw ledgers and common
calibration. This definition exposes the index factors rather than absorbing
them into the supplied workloads. -/
def relativeStrong (w : Ty → ℝ) : ℝ :=
  (weakIndex w*43+hyperIndex w*(footprint-43))/
    (colourIndex w*ColourChannels.colourLedger)

/-- The relative strong expression is the actual ratio supplied by the existing
common-stiffness/electric matching, with response indices kept in the work. -/
theorem relativeStrong_from_stiffness (w : Ty → ℝ) {c : ℝ} (hc : 0 < c)
    (hw : 0 < weakIndex w) (hy : 0 < hyperIndex w) (hcol : 0 < colourIndex w) :
    let W := weakIndex w*43
    let Y := hyperIndex w*(footprint-43)
    let C := colourIndex w*ColourChannels.colourLedger
    GaugeStiffness.gsq (c*C)/
      (GaugeStiffness.gsq (c*W)*GaugeStiffness.gsq (c*Y)/
        (GaugeStiffness.gsq (c*W)+GaugeStiffness.gsq (c*Y)))=relativeStrong w := by
  intro W Y C
  have hL : (0 : ℝ)<footprint-43 := by norm_num [footprint,overhead]
  have hK : (0 : ℝ)<ColourChannels.colourLedger := by norm_num [ColourChannels.colourLedger,overhead]
  have hW : 0 < W := by dsimp [W]; positivity
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  rw [GaugeStiffness.electric hc hW hY]
  change (1/(2*(c*C)))/(1/(2*(c*(W+Y))))=(W+Y)/C
  field_simp

lemma weak_matching_indices (w : Ty → ℝ) (hw : 0 < weakIndex w) (hy : 0 < hyperIndex w)
    (hm : mixing w=clockRatio) : weakIndex w=hyperIndex w := by
  have he := (target_mixing_iff w hw hy).mp hm
  unfold weakIndex hyperIndex
  linarith

theorem strong_matching_iff (w : Ty → ℝ) (hc : 0 < colourIndex w)
    (hew : weakIndex w=hyperIndex w) :
    relativeStrong w=footprint/ColourChannels.colourLedger ↔ weakIndex w=colourIndex w := by
  have hf : (0 : ℝ)<footprint := by norm_num [footprint,overhead]
  have hl : (0 : ℝ)<ColourChannels.colourLedger := by norm_num [ColourChannels.colourLedger,overhead]
  rw [relativeStrong,← hew,div_eq_div_iff (mul_pos hc hl).ne' hl.ne']
  constructor
  · intro he
    have hz : (weakIndex w-colourIndex w)*(footprint*ColourChannels.colourLedger)=0 := by
      linear_combination he
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (mul_pos hf hl).ne')
  · intro he; rw [he]; ring

/-- Simultaneously recovering the proposed weak and strong readouts from these
raw ledgers and one calibration requires breaking the specified root invariance. -/
theorem current_readouts_break_root (w : Ty → ℝ) (hw : 0 < weakIndex w)
    (hy : 0 < hyperIndex w) (hc : 0 < colourIndex w)
    (hm : mixing w=clockRatio)
    (hs : relativeStrong w=footprint/ColourChannels.colourLedger) :
    ¬ ∀ v : Packet, typed w (root v)=typed w v := by
  have hew := weak_matching_indices w hw hy hm
  have hec := (strong_matching_iff w hc hew).mp hs
  exact equal_response_breaks_root w hw hec hew

end PMConstants.PrimitiveReadoutSymmetry
