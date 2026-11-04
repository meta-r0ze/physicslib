import PMConstants.GaugeReadoutWeights

/-! Price supplied type-dependent integer repairs using the actual comparison
flags. Desired-ratio constraints imply arithmetic lower bounds, not a derivation
of the repair protocol. A sum of conditional repair lengths is distinguished
from actual expected executed work. -/
noncomputable section
namespace PMConstants.TypedRepairWork
open Finset CarrierActions CarrierReadoutOrbits GaugeReadoutWeights RequirementTable
open PMAction PMAction.InterferenceReadout

structure Repairs where
  q : ℕ
  u : ℕ
  d : ℕ
  l : ℕ
  e : ℕ
  n : ℕ

def count (r : Repairs) : Ty → ℕ
  | .Q => r.q | .u => r.u | .d => r.d | .L => r.l | .e => r.e | .n => r.n

/-- Positive repair lengths for every gauge-active type; no lower bound is
inferred for the neutral right-sector channel, which has no direct gauge flag. -/
def Positive (r : Repairs) : Prop :=
  1 ≤ r.q ∧ 1 ≤ r.u ∧ 1 ≤ r.d ∧ 1 ≤ r.l ∧ 1 ≤ r.e

/-- Uniform basis preparation times the number of events per flagged repair.
This is an effective work intensity, not a normalized preparation probability. -/
def weights (r : Repairs) (t : Ty) : ℝ := (count r t : ℝ)/16

lemma weights_nonneg (r : Repairs) (t : Ty) : 0 ≤ weights r t := by
  unfold weights; positivity

/-- Pricing the actual flags produces these effective weights. A repair is
charged its integer number of primitive events only when the flag occurs. -/
theorem priced_score (r : Repairs) (toll : ℝ) (U : Matrix Packet Packet ℂ) :
    (∑ v : Packet, (1/16 : ℝ)*CommonResponse.responseCost toll (count r (CarrierActions.channelType v))
      (flagProbability U v))=
      toll*WeightedReadoutResponse.score (typed (weights r)) U := by
  simp only [CommonResponse.responseCost,WeightedReadoutResponse.score,mul_sum,typed,weights]
  apply sum_congr rfl
  intro v _; ring

/-- The sterile repair length does not enter these direct gauge indices. -/
theorem index_values (r : Repairs) :
    weakIndex (weights r)=((3*r.q+r.l : ℕ) : ℝ)/32 ∧
    colourIndex (weights r)=((2*r.q+r.u+r.d : ℕ) : ℝ)/32 ∧
    hyperIndex (weights r)=((r.q : ℝ)/6+4*r.u/3+r.d/3+r.l/2+r.e)/16 := by
  norm_num [weakIndex,colourIndex,hyperIndex,weights,count]
  constructor
  · ring
  constructor <;> ring

theorem weak_hyper_positive (r : Repairs) (hr : Positive r) :
    0 < weakIndex (weights r) ∧ 0 < hyperIndex (weights r) := by
  rcases hr with ⟨hq,hu,hd,hl,he⟩
  have hq' : (0 : ℝ)<r.q := by exact_mod_cast (by omega : 0<r.q)
  have hu' : (0 : ℝ)<r.u := by exact_mod_cast (by omega : 0<r.u)
  have hd' : (0 : ℝ)<r.d := by exact_mod_cast (by omega : 0<r.d)
  have hl' : (0 : ℝ)<r.l := by exact_mod_cast (by omega : 0<r.l)
  have he' : (0 : ℝ)<r.e := by exact_mod_cast (by omega : 0<r.e)
  constructor <;> simp only [weakIndex,hyperIndex,weights,count] <;> positivity

/-- The proposed mixing imposes a Diophantine condition on integer repairs;
it does not select these repairs from the substrate. -/
theorem target_iff (r : Repairs) (hr : Positive r) :
    mixing (weights r)=clockRatio ↔ 4*r.q=4*r.u+r.d+3*r.e := by
  obtain ⟨hw,hy⟩ := weak_hyper_positive r hr
  rw [target_mixing_iff _ hw hy]
  simp only [weights,count]
  constructor
  · intro h
    have he : 4*(r.q : ℝ)=4*r.u+r.d+3*r.e := by linarith
    exact_mod_cast he
  · intro h
    have he : 4*(r.q : ℝ)=4*r.u+r.d+3*r.e := by exact_mod_cast h
    linarith

theorem equal_indices_condition (r : Repairs) :
    (weakIndex (weights r)=colourIndex (weights r) ∧
      weakIndex (weights r)=hyperIndex (weights r)) ↔
      (r.q+r.l=r.u+r.d ∧ 4*r.q=4*r.u+r.d+3*r.e) := by
  rw [equal_indices_iff]
  simp only [weights,count]
  constructor
  · rintro ⟨h1,h2⟩
    have he1 : (r.q : ℝ)+r.l=r.u+r.d := by linarith
    have he2 : 4*(r.q : ℝ)=4*r.u+r.d+3*r.e := by linarith
    exact ⟨by exact_mod_cast he1,by exact_mod_cast he2⟩
  · rintro ⟨h1,h2⟩
    have he1 : (r.q : ℝ)+r.l=r.u+r.d := by exact_mod_cast h1
    have he2 : 4*(r.q : ℝ)=4*r.u+r.d+3*r.e := by exact_mod_cast h2
    constructor <;> linarith

/-- Sum of conditional repair lengths over the fifteen gauge-active labels.
It is not expected executed work and contains no flag probabilities. -/
def activeBudget (r : Repairs) : ℕ := 6*r.q+3*r.u+3*r.d+2*r.l+r.e

theorem baseline_bound (r : Repairs) (hr : Positive r) : 15 ≤ activeBudget r := by
  rcases hr with ⟨hq,hu,hd,hl,he⟩
  unfold activeBudget; omega

theorem baseline_unique (r : Repairs) (hr : Positive r) (hb : activeBudget r=15) :
    r.q=1 ∧ r.u=1 ∧ r.d=1 ∧ r.l=1 ∧ r.e=1 := by
  rcases hr with ⟨hq,hu,hd,hl,he⟩
  unfold activeBudget at hb
  omega

theorem target_budget_bound (r : Repairs) (hr : Positive r)
    (ht : 4*r.q=4*r.u+r.d+3*r.e) : 21 ≤ activeBudget r := by
  rcases hr with ⟨hq,hu,hd,hl,he⟩
  unfold activeBudget; omega

theorem target_budget_unique (r : Repairs) (hr : Positive r)
    (ht : 4*r.q=4*r.u+r.d+3*r.e) (hb : activeBudget r=21) :
    r.q=2 ∧ r.u=1 ∧ r.d=1 ∧ r.l=1 ∧ r.e=1 := by
  rcases hr with ⟨hq,hu,hd,hl,he⟩
  unfold activeBudget at hb
  omega

theorem all_equal_budget_bound (r : Repairs) (hr : Positive r)
    (hc : r.q+r.l=r.u+r.d) (ht : 4*r.q=4*r.u+r.d+3*r.e) :
    43 ≤ activeBudget r := by
  rcases hr with ⟨hq,hu,hd,hl,he⟩
  have hl3 : 3 ≤ r.l := by omega
  unfold activeBudget; omega

theorem all_equal_budget_unique (r : Repairs) (hr : Positive r)
    (hc : r.q+r.l=r.u+r.d) (ht : 4*r.q=4*r.u+r.d+3*r.e)
    (hb : activeBudget r=43) : r.q=3 ∧ r.u=1 ∧ r.d=5 ∧ r.l=3 ∧ r.e=1 := by
  rcases hr with ⟨hq,hu,hd,hl,he⟩
  have hl3 : 3 ≤ r.l := by omega
  unfold activeBudget at hb
  omega

/-- Attainment witnesses for the arithmetic bounds only, not selected physical
repair words or implementations. Neutral repair length is not constrained. -/
def weakWitness : Repairs := ⟨2,1,1,1,1,0⟩
def equalWitness : Repairs := ⟨3,1,5,3,1,0⟩

theorem witnesses :
    Positive weakWitness ∧ activeBudget weakWitness=21 ∧
    4*weakWitness.q=4*weakWitness.u+weakWitness.d+3*weakWitness.e ∧
    Positive equalWitness ∧ activeBudget equalWitness=43 ∧
    equalWitness.q+equalWitness.l=equalWitness.u+equalWitness.d ∧
    4*equalWitness.q=4*equalWitness.u+equalWitness.d+3*equalWitness.e := by
  norm_num [Positive,activeBudget,weakWitness,equalWitness]

/-- A common positive repair length cannot give the target mixing. -/
theorem common_repair_cannot_match (r : Repairs) (hr : Positive r)
    (hu : r.u=r.q) (hd : r.d=r.q) (he : r.e=r.q) :
    mixing (weights r) ≠ clockRatio := by
  intro ht
  have hc := (target_iff r hr).mp ht
  rcases hr with ⟨hq,_,_,_,_⟩
  omega

/-- A precisely specified primitive task: undo the actual E8-induced carrier
reflection on every input by repeating that allowed reflection. -/
def UndoesRoot (c : Fin 3) (length : ℕ) : Prop :=
  ∀ v : PMAction.CarrierEvents.Carrier c,
    (PMAction.CarrierEvents.reflect c)^[length] (PMAction.CarrierEvents.reflect c v)=v

/-- Every glue class has the same least repair length one for this task.
This does not identify an interference flag's repair with undoing a root. -/
theorem root_undo_minimum (c : Fin 3) : IsLeast {n : ℕ | UndoesRoot c n} 1 := by
  constructor
  · intro v
    simpa only [Function.iterate_one] using PMAction.CarrierEvents.reflection_involutive c v
  · intro n hn
    by_contra h
    have hz : n=0 := by omega
    subst n
    have he : PMAction.CarrierEvents.active c=∅ := by
      ext v
      have hv : PMAction.CarrierEvents.reflect c v=v := by simpa [UndoesRoot] using hn v
      simp [PMAction.CarrierEvents.active,hv]
    have hc := PMAction.CarrierEvents.active_card c
    rw [he] at hc
    norm_num at hc

end PMConstants.TypedRepairWork
