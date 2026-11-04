import PMConstants.ColourPhaseMaintenance
import PMConstants.ChannelDirectionLoad
import PMConstants.ExclusionLawAudit
import PMConstants.AvailabilityAudit

/-! Actual carrier quadratic load restricted to colour, under the existing
intensive reference-star contract. Geometry is checked first; identifying this
load with physical comparison work remains an operational premise. -/
set_option maxHeartbeats 1000000
noncomputable section
namespace PMConstants.ColourGeometricLoad
open Finset CarrierActions CarrierRepresentation ColourPhaseMaintenance
open PMConstants.General.ReferenceCapacity

/-- Doubled-coordinate quadratic load of the actual packet's colour-axis fibre. -/
def quadratic (a : Fin 3) (d : Fin 4) : ℤ :=
  ∑ v : Packet, if address (index v)=some a then (coord (carried v) d)^2 else 0

theorem quadratic_geometry : ∀ (a : Fin 3) (d : Fin 4),
    quadratic a d=if d=colourAxis a then 16 else 0 := by decide +kernel

def rowLoad (a : Fin 3) (d : Fin 4) : ℝ := (quadratic a d : ℝ)/4

theorem row_load (a : Fin 3) (d : Fin 4) :
    rowLoad a d=if d=colourAxis a then 4 else 0 := by
  rw [rowLoad, quadratic_geometry]
  split_ifs <;> norm_num

theorem axis_total (a : Fin 3) : (∑ d, rowLoad a d)=4 := by
  simp [row_load]

/-- One reference-star job per address, with the inherited phase-uniform
quadratic density. No η is inserted into this definition. -/
def axisRequired (a : Fin 3) (o : Grid) : ℝ :=
  ∑ x : Grid, ExclusionLawAudit.relJob o x*(rowLoad a x.1/43)

lemma relational_sum (o : Grid) (ρ : Grid → ℝ) :
    (∑ x : Grid, ExclusionLawAudit.relJob o x*ρ x)=(∑ x, ρ x)-ρ o := by
  have hp : ∀ x, ExclusionLawAudit.relJob o x*ρ x=
      ρ x-(if x=o then ρ o else 0) := by
    intro x
    by_cases hx : x=o
    · subst x; simp [ExclusionLawAudit.relJob_self]
    · simp [ExclusionLawAudit.relJob, ExclusionLawAudit.star_adj, hx]
  simp_rw [hp]
  rw [sum_sub_distrib]
  simp

lemma density_total (a : Fin 3) : (∑ x : Grid, rowLoad a x.1/43)=4 := by
  rw [Fintype.sum_prod_type]
  have ht : ∀ d, (∑ _t : Fin 43, rowLoad a d/43)=rowLoad a d := by
    intro d; simp; ring
  simp_rw [ht]
  exact axis_total a

theorem axis_required (a : Fin 3) (o : Grid) :
    axisRequired a o=4-(if o.1=colourAxis a then 4/43 else 0) := by
  rw [axisRequired, relational_sum, density_total, row_load]
  split_ifs <;> norm_num

def colourRequired (o : Grid) : ℝ := ∑ a, axisRequired a o

theorem colour_required (o : Grid) :
    colourRequired o=if o.1=0 then 12 else 12-4/43 := by
  rcases o with ⟨d,t⟩
  fin_cases d <;> norm_num [colourRequired, axis_required, colourAxis, Fin.sum_univ_succ]

/-- Full-packet balance does not imply the same overhead on the colour subset. -/
theorem full_packet_still_balanced (o : Grid) :
    ExclusionLawAudit.intensiveRequired (fun _ => 4) o=16*overhead := by
  simpa [overhead] using ExclusionLawAudit.intensive_required_balanced (fun _ => 4) (fun _ => rfl) o

theorem fixed_reference_not_colour_ledger (o : Grid) : colourRequired o ≠ 12*overhead := by
  rw [colour_required]; split_ifs <;> norm_num [overhead]

theorem fixed_reference_not_target (o : Grid) :
    ¬ ∀ a, axisRequired a o=4*overhead := by
  intro h
  apply fixed_reference_not_colour_ledger o
  simp [colourRequired,h]
  ring

/-- Phase ticking never mixes direction, so it cannot remove this anisotropy. -/
theorem phase_orbit_constant (n : ℕ) (o : Grid) (a : Fin 3) :
    axisRequired a ((gridTick^[n]) o)=axisRequired a o := by
  rw [AvailabilityAudit.tick_iter, axis_required, axis_required]

theorem phase_cycle_not_colour_ledger (o : Grid) :
    (∑ t : Fin 43, colourRequired ((gridTick^[t.val]) o))/43 ≠ 12*overhead := by
  have hc : ∀ n, colourRequired ((gridTick^[n]) o)=colourRequired o := by
    intro n; simp only [colourRequired, phase_orbit_constant]
  simp_rw [hc]
  have he : (∑ _t : Fin 43, colourRequired o)/43=colourRequired o := by simp
  rw [he]
  exact fixed_reference_not_colour_ledger o

/-- An explicit mixture over reference directions; no phase mixing is required
for this aggregate because axisRequired is phase-independent. -/
def meanAxis (p : Fin 4 → ℝ) (a : Fin 3) : ℝ := ∑ d, p d*axisRequired a (d,0)

theorem mean_axis (p : Fin 4 → ℝ) (hp : ∑ d, p d=1) (a : Fin 3) :
    meanAxis p a=4-(4/43)*p (colourAxis a) := by
  have hs : p 0+p 1+p 2+p 3=1 := by simpa [Fin.sum_univ_succ, ← add_assoc] using hp
  fin_cases a <;> simp [meanAxis, axis_required, colourAxis, Fin.sum_univ_succ] <;> linarith

theorem mean_axis_target_iff (p : Fin 4 → ℝ) (hp : ∑ d, p d=1) (a : Fin 3) :
    meanAxis p a=4*overhead ↔ p (colourAxis a)=1/4 := by
  rw [mean_axis p hp]
  norm_num [overhead]
  constructor <;> intro h <;> linarith

/-- The exact missing measure condition in this contract. All three target
axis weights require uniform reference-direction marginals, including the
lepton direction by normalization. Positivity is not needed for the algebra. -/
theorem target_iff_uniform_directions (p : Fin 4 → ℝ) (hp : ∑ d, p d=1) :
    (∀ a, meanAxis p a=4*overhead) ↔ ∀ d, p d=1/4 := by
  constructor
  · intro h
    have h1 := (mean_axis_target_iff p hp 0).mp (h 0)
    have h2 := (mean_axis_target_iff p hp 1).mp (h 1)
    have h3 := (mean_axis_target_iff p hp 2).mp (h 2)
    change p 1=1/4 at h1
    change p 2=1/4 at h2
    change p 3=1/4 at h3
    have hs : p 0+p 1+p 2+p 3=1 := by simpa [Fin.sum_univ_succ, ← add_assoc] using hp
    intro d; fin_cases d
    · change p 0=1/4; linarith
    · exact h1
    · exact h2
    · exact h3
  · intro h a; exact (mean_axis_target_iff p hp a).mpr (h _)

/-- Colour permutations alone cannot select the lepton-direction marginal. -/
def leptonOnly (d : Fin 4) : ℝ := if d=0 then 1 else 0

theorem lepton_only_normalized : (∀ d, 0 ≤ leptonOnly d) ∧ (∑ d, leptonOnly d)=1 := by
  constructor
  · intro d; simp [leptonOnly]; split_ifs <;> norm_num
  · simp [leptonOnly]

theorem lepton_only_colour_symmetric : ∀ (a b : Fin 3) (d : Fin 4),
    leptonOnly (Equiv.swap (colourAxis a) (colourAxis b) d)=leptonOnly d := by
  intro a b d; fin_cases a <;> fin_cases b <;> fin_cases d <;> norm_num [leptonOnly,colourAxis,Equiv.swap_apply_def]

theorem lepton_only_not_target : ¬ ∀ a, meanAxis leptonOnly a=4*overhead := by
  intro h
  have hh := (target_iff_uniform_directions leptonOnly lepton_only_normalized.2).mp h 0
  norm_num [leptonOnly] at hh

/-- Even a strictly positive, colour-symmetric law leaves the temporal/lepton
weight free; this is not merely a zero-probability counterexample. -/
def biased (d : Fin 4) : ℝ := if d=0 then 1/2 else 1/6

theorem biased_normalized : (∀ d, 0 < biased d) ∧ (∑ d, biased d)=1 := by
  constructor
  · intro d; fin_cases d <;> norm_num [biased]
  · norm_num [biased, Fin.sum_univ_succ]

theorem biased_colour_symmetric : ∀ (a b : Fin 3) (d : Fin 4),
    biased (Equiv.swap (colourAxis a) (colourAxis b) d)=biased d := by
  intro a b d; fin_cases a <;> fin_cases b <;> fin_cases d <;>
    norm_num [biased,colourAxis,Equiv.swap_apply_def]

theorem biased_not_target : ¬ ∀ a, meanAxis biased a=4*overhead := by
  intro h
  have hh := (target_iff_uniform_directions biased biased_normalized.2).mp h 0
  norm_num [biased] at hh

theorem biased_grid_law :
    AvailabilityAudit.TickInvariant (AvailabilityAudit.dirMass biased) ∧
    AvailabilityAudit.Normalized (AvailabilityAudit.dirMass biased) ∧
      ∀ x, 0 < AvailabilityAudit.dirMass biased x := by
  refine ⟨AvailabilityAudit.dirMass_invariant biased,
    AvailabilityAudit.dirMass_normalized biased (fun d => (biased_normalized.1 d).le)
      biased_normalized.2, ?_⟩
  intro x
  exact div_pos (biased_normalized.1 x.1) (by norm_num)

/-- The actual eight minimal carriers contain two states on every axis. -/
theorem reference_axis_count : ∀ d : Fin 4,
    (univ.filter (fun v : V => axis v=d)).card=2 := by decide +kernel

/-- A reference-direction sampler using the existing uniform carrier law.
Identifying this with the physical reference process is an explicit bridge;
the phase map is arbitrary and need not sample all 172 grid cells. -/
def sampledReference (phase : V → Fin 43) (v : V) : Grid := (axis v,phase v)

def sampledAxis (phase : V → Fin 43) (a : Fin 3) : ℝ :=
  (∑ v : V, axisRequired a (sampledReference phase v))/8

/-- η is an output here, not a coefficient of the load definition. The
operational inputs are the intensive relational density and this sampler. -/
theorem sampled_axis_target (phase : V → Fin 43) (a : Fin 3) :
    sampledAxis phase a=4*overhead := by
  have hc := reference_axis_count (colourAxis a)
  have hs : (∑ v : V, if axis v=colourAxis a then (4/43 : ℝ) else 0)=2*(4/43) := by
    rw [sum_ite]
    simp [hc]
  unfold sampledAxis
  simp only [axis_required, sampledReference]
  rw [sum_sub_distrib, hs]
  norm_num [PMAction.CarrierEvents.carrier_card, overhead]

def sampledResponse (phase : V → Fin 43) (θ : Fin 3 → ℝ) : ℝ :=
  ∑ a, sampledAxis phase a*flag (θ a)

theorem sampled_response (phase : V → Fin 43) (θ : Fin 3 → ℝ) :
    sampledResponse phase θ=response (fun _ => overhead) θ := by
  simp only [sampledResponse, sampled_axis_target, response_formula, uniform_axis_load]

theorem sampled_repair_cost (phase : V → Fin 43) (θ : Fin 3 → ℝ)
    (toll : ℝ) (m : ℕ) :
    toll*m*sampledResponse phase θ=
      (EventStiffness.c0 toll m*(12*overhead))*cosineMean θ := by
  rw [sampled_response]
  exact uniform_repair_cost toll m overhead θ

end PMConstants.ColourGeometricLoad
