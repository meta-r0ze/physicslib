import PMConstants.ColourRefreshCadence
import PMConstants.CarrierPhaseResponse
import PMConstants.EventStiffness

/-! Phase-response constraints on maintenance weights. Three balanced diagonal
colour phases act on four copies of the colour triplet in the actual packet.
The comparison law is inherited; this does not derive a physical probe ensemble,
repair length, field weight or reference-preparation cost. -/
set_option maxHeartbeats 1000000
noncomputable section
namespace PMConstants.ColourPhaseMaintenance
open Matrix Finset CarrierActions CarrierSwapSchedule
open PMAction.InterferenceReadout

/-- Four copies of the three colour addresses, with four colourless labels. -/
def address : Fin 16 → Option (Fin 3) :=
  ![some 0,some 0,some 1,some 1,some 2,some 2,
    some 0,some 1,some 2,some 0,some 1,some 2,none,none,none,none]

/-- The lookup is the actual non-lepton carrier axis under the proved index. -/
theorem address_from_carriers : ∀ v : Packet,
    (address (index v)).map colourAxis=
      if CarrierRepresentation.onLepton (carried v) then none else some (axis (carried v)) := by
  decide +kernel

theorem address_equivariant : ∀ (a b : Fin 3) (v : Packet),
    address (index (colour a b v))=(address (index v)).map (Equiv.swap a b) := by
  decide +kernel

def phaseAt (θ : Fin 3 → ℝ) (i : Fin 16) : ℝ :=
  match address i with | some a => θ a | none => 0

def link (θ : Fin 3 → ℝ) : Matrix Packet Packet ℂ :=
  diagonal (fun v => Complex.exp ((phaseAt θ (index v) : ℂ)*Complex.I))

def axisLink (θ : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  diagonal (fun a => Complex.exp ((θ a : ℂ)*Complex.I))

lemma diagonal_phase_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] (θ : ι → ℝ) :
    diagonal (fun a => Complex.exp ((θ a : ℂ)*Complex.I)) ∈ unitary (Matrix ι ι ℂ) := by
  constructor
  · change (diagonal (fun a => Complex.exp ((θ a : ℂ)*Complex.I)))ᴴ *
      diagonal (fun a => Complex.exp ((θ a : ℂ)*Complex.I))=1
    simp only [diagonal_conjTranspose, diagonal_mul_diagonal]
    change diagonal (fun a => star (Complex.exp ((θ a : ℂ)*Complex.I))*
      Complex.exp ((θ a : ℂ)*Complex.I))=1
    simp only [CarrierPhaseResponse.phase_unit, diagonal_one]
  · change diagonal (fun a => Complex.exp ((θ a : ℂ)*Complex.I)) *
      (diagonal (fun a => Complex.exp ((θ a : ℂ)*Complex.I)))ᴴ=1
    simp only [diagonal_conjTranspose, diagonal_mul_diagonal]
    have h : ∀ a, Complex.exp ((θ a : ℂ)*Complex.I)*
        star (Complex.exp ((θ a : ℂ)*Complex.I))=1 := by
      intro a; rw [mul_comm]; exact CarrierPhaseResponse.phase_unit _
    change diagonal (fun a => Complex.exp ((θ a : ℂ)*Complex.I)*
      star (Complex.exp ((θ a : ℂ)*Complex.I)))=1
    simp only [h, diagonal_one]

theorem link_unitary (θ : Fin 3 → ℝ) : link θ ∈ unitary (Matrix Packet Packet ℂ) :=
  diagonal_phase_unitary _

theorem balanced_special_unitary (θ : Fin 3 → ℝ) (hθ : ∑ a, θ a=0) :
    axisLink θ ∈ unitary (Matrix (Fin 3) (Fin 3) ℂ) ∧ (axisLink θ).det=1 := by
  refine ⟨diagonal_phase_unitary _, ?_⟩
  rw [axisLink, det_diagonal, ← Complex.exp_sum, ← sum_mul]
  have hs : (∑ a : Fin 3, (θ a : ℂ))=0 := by exact_mod_cast hθ
  rw [hs, zero_mul, Complex.exp_zero]

def flag (x : ℝ) : ℝ := (1-Real.cos x)/2

theorem flag_response (θ : Fin 3 → ℝ) (v : Packet) :
    flagProbability (link θ) v=flag (phaseAt θ (index v)) := by
  rw [flag_formula _ (link_unitary θ)]
  simp only [link, diagonal_apply_eq, Complex.exp_ofReal_mul_I_re, flag]

/-- Weights include the comparison/refresh rate; they are not yet derived costs. -/
def response (w : Fin 16 → ℝ) (θ : Fin 3 → ℝ) : ℝ :=
  ∑ v : Packet, w (index v)*flagProbability (link θ) v

def axisLoad (w : Fin 16 → ℝ) : Fin 3 → ℝ :=
  ![w 0+w 1+w 6+w 9, w 2+w 3+w 7+w 10, w 4+w 5+w 8+w 11]

theorem response_formula (w : Fin 16 → ℝ) (θ : Fin 3 → ℝ) :
    response w θ=∑ a : Fin 3, axisLoad w a*flag (θ a) := by
  unfold response
  simp_rw [flag_response]
  change (∑ v : Packet, (fun i => w i*flag (phaseAt θ i)) (enumeration v))=_
  calc
    _ = ∑ i : Fin 16, w i*flag (phaseAt θ i) := Equiv.sum_comp enumeration _
    _ = _ := by
      simp [phaseAt, address, axisLoad, Fin.sum_univ_succ, flag]
      ring

@[simp] theorem response_zero (w : Fin 16 → ℝ) : response w (fun _ => 0)=0 := by
  rw [response_formula]; simp [flag]

/-- Diagonal determinant-one probes: no independent phase on a lone colour axis
is assumed physically available. -/
def probe (g : Fin 3) : Fin 3 → ℝ :=
  ![![Real.pi,-Real.pi,0], ![Real.pi,0,-Real.pi], ![0,Real.pi,-Real.pi]] g

theorem probe_balanced (g : Fin 3) : ∑ a, probe g a=0 := by
  fin_cases g <;> simp [probe, Fin.sum_univ_succ]

theorem probe_response (w : Fin 16 → ℝ) (g : Fin 3) :
    response w (probe g)=
      (![axisLoad w 0+axisLoad w 1, axisLoad w 0+axisLoad w 2,
        axisLoad w 1+axisLoad w 2] : Fin 3 → ℝ) g := by
  rw [response_formula]
  fin_cases g <;> simp [probe, flag, Fin.sum_univ_succ]

/-- Equality for every allowed diagonal colour phase determines the three
aggregate weights, but not the four individual weights in each aggregate. -/
theorem response_tomography (w z : Fin 16 → ℝ) :
    (∀ θ : Fin 3 → ℝ, (∑ a, θ a)=0 → response w θ=response z θ) ↔
      ∀ a, axisLoad w a=axisLoad z a := by
  constructor
  · intro h
    have h0 := h (probe 0) (probe_balanced 0)
    have h1 := h (probe 1) (probe_balanced 1)
    have h2 := h (probe 2) (probe_balanced 2)
    rw [probe_response, probe_response] at h0 h1 h2
    change axisLoad w 0+axisLoad w 1=axisLoad z 0+axisLoad z 1 at h0
    change axisLoad w 0+axisLoad w 2=axisLoad z 0+axisLoad z 2 at h1
    change axisLoad w 1+axisLoad w 2=axisLoad z 1+axisLoad z 2 at h2
    intro a; fin_cases a
    · change axisLoad w 0=axisLoad z 0
      linarith only [h0,h1,h2]
    · change axisLoad w 1=axisLoad z 1
      linarith only [h0,h1,h2]
    · change axisLoad w 2=axisLoad z 2
      linarith only [h0,h1,h2]
  · intro h θ _; simp_rw [response_formula, h]

/-- A phase-independent baseline cannot conceal a different response weight. -/
theorem baseline_tomography (B C : ℝ) (w z : Fin 16 → ℝ) :
    (∀ θ : Fin 3 → ℝ, (∑ a, θ a)=0 → B+response w θ=C+response z θ) ↔
      B=C ∧ ∀ a, axisLoad w a=axisLoad z a := by
  constructor
  · intro h
    have hb : B=C := by simpa using h (fun _ => 0) (by simp)
    refine ⟨hb, (response_tomography w z).mp ?_⟩
    intro θ hθ
    have hh := h θ hθ
    rw [hb] at hh
    exact add_left_cancel hh
  · rintro ⟨rfl,h⟩ θ hθ
    rw [(response_tomography w z).mpr h θ hθ]

def meanFlag (θ : Fin 3 → ℝ) : ℝ := (∑ a, flag (θ a))/3

/-- The factor twelve has an exact response interpretation for uniform weights:
four triplets times the mean three-axis phase response. Uniformity and weight
normalization are exposed rather than inferred from field support alone. -/
theorem uniform_response (k : ℝ) (θ : Fin 3 → ℝ) :
    response (fun _ => k) θ=(12*k)*meanFlag θ := by
  rw [response_formula]
  simp [axisLoad, meanFlag, Fin.sum_univ_succ]
  ring

/-- The averaging convention is exactly the existing uniform carrier readout
on the three-axis unitary, not an additional fitted factor. -/
theorem mean_flag_readout (θ : Fin 3 → ℝ) :
    meanFlag θ=PMAction.InterferenceReadout.meanFlag (axisLink θ) := by
  change (∑ a, flag (θ a))/3=(∑ a, flagProbability (axisLink θ) a)/3
  congr 1
  apply sum_congr rfl
  intro a _
  rw [flag_formula (axisLink θ) (diagonal_phase_unitary θ)]
  simp only [axisLink, diagonal_apply_eq, Complex.exp_ofReal_mul_I_re, flag]

def cosineMean (θ : Fin 3 → ℝ) : ℝ := (∑ a, (1-Real.cos (θ a)))/3

/-- Exact compatibility with the existing stiffness prefactor. Its twelve
comes from four triplets; k is still the assumed effective per-label weight. -/
theorem uniform_repair_cost (toll : ℝ) (m : ℕ) (k : ℝ) (θ : Fin 3 → ℝ) :
    toll*m*response (fun _ => k) θ=
      (EventStiffness.c0 toll m*(12*k))*cosineMean θ := by
  rw [uniform_response]
  simp [EventStiffness.c0, meanFlag, cosineMean, flag, Fin.sum_univ_succ]
  ring

/-- A redistribution among the four identical triplets cannot be identified
by these shared colour probes, even though some fields receive zero weight. -/
def concentrated (k : ℝ) (i : Fin 16) : ℝ :=
  if i=0 ∨ i=2 ∨ i=4 then 4*k else 0

theorem concentrated_load (k : ℝ) : ∀ a : Fin 3,
    axisLoad (concentrated k) a=axisLoad (fun _ => k) a := by
  intro a; fin_cases a <;> norm_num [axisLoad, concentrated] <;> ring

theorem concentrated_indistinguishable (k : ℝ) (θ : Fin 3 → ℝ) :
    response (concentrated k) θ=response (fun _ => k) θ := by
  simp_rw [response_formula, concentrated_load]

def axisSet (a : Fin 3) : Finset (Fin 16) := univ.filter (fun i => address i=some a)

lemma axis_set_card : ∀ a : Fin 3, (axisSet a).card=4 := by decide +kernel

lemma axis_load_sum (w : Fin 16 → ℝ) (a : Fin 3) :
    axisLoad w a=∑ i ∈ axisSet a, w i := by
  unfold axisSet
  rw [sum_filter]
  fin_cases a <;> simp [address, axisLoad, Fin.sum_univ_succ] <;> ring

lemma uniform_axis_load (k : ℝ) : ∀ a : Fin 3, axisLoad (fun _ => k) a=4*k := by
  intro a; fin_cases a <;> simp [axisLoad] <;> ring

lemma coloured_has_address : ∀ i : Fin 16, i ∈ ResourceLedger.colouredSet →
    ∃ a, address i=some a := by decide +kernel

/-- With a genuine per-label upper capacity k, saturation of all three
aggregate response weights forces every coloured label to attain k. This
capacity bound is an additional physical obligation, not readout tomography. -/
theorem capped_response_forces_full (w : Fin 16 → ℝ) (k : ℝ)
    (hcap : ∀ i, w i ≤ k)
    (hresponse : ∀ θ : Fin 3 → ℝ, (∑ a, θ a)=0 →
      response w θ=response (fun _ => k) θ) :
    ∀ i ∈ ResourceLedger.colouredSet, w i=k := by
  have hload := (response_tomography w (fun _ => k)).mp hresponse
  intro i hi
  obtain ⟨a,ha⟩ := coloured_has_address i hi
  have his : i ∈ axisSet a := by simp [axisSet,ha]
  have hz : (∑ j ∈ axisSet a, (k-w j))=0 := by
    rw [sum_sub_distrib, sum_const, axis_set_card, nsmul_eq_mul, ← axis_load_sum,
      hload, uniform_axis_load]
    ring
  have hn : ∀ j ∈ axisSet a, 0 ≤ k-w j := fun j _ => sub_nonneg.mpr (hcap j)
  have he := (sum_eq_zero_iff_of_nonneg hn).mp hz i his
  linarith

/-- Unchanged link transport has zero phase flag. This does not set reference
preparation, storage or an independently required comparison baseline to zero. -/
theorem identity_no_flag (v : Packet) : flagProbability (link (fun _ => 0)) v=0 := by
  rw [flag_response]; simp [phaseAt, flag]; cases address (index v) <;> simp

/-- Additive time response; independent balanced phase probes at distinct ticks
are an explicit hypothesis of the identification theorem below. -/
def historyResponse {T : Type*} [Fintype T]
    (w : T → Fin 16 → ℝ) (θ : T → Fin 3 → ℝ) : ℝ := ∑ t, response (w t) (θ t)

lemma localized_response {T : Type*} [Fintype T] [DecidableEq T]
    (w : T → Fin 16 → ℝ) (t : T) (θ : Fin 3 → ℝ) :
    historyResponse w (fun s => if s=t then θ else fun _ => 0)=response (w t) θ := by
  simp [historyResponse, apply_ite]

/-- Matching the full response to independently variable per-tick phases
requires matching the three effective colour weights at each tick. -/
theorem time_tomography {T : Type*} [Fintype T] [DecidableEq T]
    (w z : T → Fin 16 → ℝ) :
    (∀ θ : T → Fin 3 → ℝ, (∀ t, (∑ a, θ t a)=0) →
      historyResponse w θ=historyResponse z θ) ↔
      ∀ t a, axisLoad (w t) a=axisLoad (z t) a := by
  constructor
  · intro h t
    apply (response_tomography (w t) (z t)).mp
    intro θ hθ
    have hh := h (fun s => if s=t then θ else fun _ => 0) (by
      intro s; by_cases hs : s=t <;> simp [hs,hθ])
    simpa only [localized_response] using hh
  · intro h θ hθ
    apply sum_congr rfl
    intro t _
    exact (response_tomography (w t) (z t)).mpr (h t) (θ t) (hθ t)

/-- Only the fields used by one exchange receive the assumed weight η. -/
def exchangeWeights (g : Fin 3) (i : Fin 16) : ℝ :=
  if i ∈ touched (colourPairs g) then overhead else 0

def detector (g : Fin 3) : Fin 3 → ℝ := probe (![1,0,0] g)

theorem detector_balanced (g : Fin 3) : (∑ a, detector g a)=0 := probe_balanced _

theorem detector_response (g : Fin 3) :
    response (exchangeWeights g) (detector g)=4*overhead ∧
      response (fun _ => overhead) (detector g)=8*overhead := by
  fin_cases g <;> simp only [detector,
    probe_response] <;>
    norm_num [axisLoad, exchangeWeights, touched, colourPairs, overhead]

theorem exchange_not_full_response (g : Fin 3) :
    ¬ ∀ θ : Fin 3 → ℝ, (∑ a, θ a)=0 →
      response (exchangeWeights g) θ=response (fun _ => overhead) θ := by
  intro h
  have hh := h (detector g) (detector_balanced g)
  rw [(detector_response g).1, (detector_response g).2] at hh
  norm_num [overhead] at hh

end PMConstants.ColourPhaseMaintenance
