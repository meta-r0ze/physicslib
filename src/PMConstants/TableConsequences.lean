import PMConstants.RequirementComplement
import PMConstants.ReadoutAccounting
import PMConstants.ColourReference

/-!
# What the derived requirement table gives end to end

`RequirementRows` and `RequirementComplement` derive the table from the reserved reference. Here
its consequences are stated with the table as a conclusion rather than a premise. `Premises` bundles
what remains: a refresh assignment of the phase's resources to the electroweak pair, with the clock
row (the reference's row) to weak and weak confined to it.

* `assignment`: the weak set is `reqSU2` and the hypercharge set is `reqY`.
* `weak_mixing`: `s = 43/N_sys = 1849/8295`.
* `strong_coupling`: `0.11799 < α N_sys/L₃ < 0.11800`, with `L₃ = 12η` from per-channel routing.
* `sterile_included`: the sterile payload is in the hypercharge set. Excluding it (`footprint15`) is
  what `ResourceLedger.sterile_counted` puts more than `3.1σ` from the W mass; that is now a check,
  not the selector.
* `electric_partition`: the two sets are disjoint and their ledgers add to the footprint; with
  stiffness proportional to the ledger, `1/e² = 1/g² + 1/g'²` is the sum over that partition
  (`GaugeStiffness.electric`).
The measured `m_Z` W-mass comparison (`w_mass`) lives in
`tools/e8p/E8PConstants/ReadoutPulls.lean`.
-/

noncomputable section
namespace PMConstants.TableConsequences
open PMConstants GaugeLedgers RequirementComplement

structure Premises where
  f : Res → EW
  clock_weak : f .clock = .weak
  weak_confined : ∀ r, f r = .weak → r = .clock

theorem assignment (P : Premises) (r : Res) :
    (P.f r = .weak ↔ r ∈ reqSU2) ∧ (P.f r = .hyper ↔ r ∈ reqY) := by
  refine ⟨⟨fun h => by simp [reqSU2, P.weak_confined r h], fun h => ?_⟩,
    hyper_is_complement P.f P.clock_weak P.weak_confined r⟩
  simp only [reqSU2, Finset.mem_singleton] at h
  subst h; exact P.clock_weak

theorem weak_mixing (_P : Premises) :
    ledger reqSU2 / (ledger reqSU2 + ledger reqY) = 1849 / 8295 := by
  rw [mixing_from_rule]; norm_num [clockRatio, footprint, overhead]

theorem strong_coupling (_P : Premises) :
    (0.11799 : ℝ) < CertifiedConstants.α * (ledger reqSU2 + ledger reqY) / ledger reqColour ∧
      CertifiedConstants.α * (ledger reqSU2 + ledger reqY) / ledger reqColour < 0.11800 := by
  rw [strong_from_rule]; exact ColourReference.strong_from_payload

theorem sterile_included (P : Premises) : P.f (.payload 15) = .hyper := by
  exact ((assignment P _).2).mpr (by simp [reqY])

theorem electric_partition (_P : Premises) {c : ℝ} (hc : 0 < c) :
    Disjoint reqSU2 reqY ∧ ledger (reqSU2 ∪ reqY) = footprint ∧
      GaugeStiffness.gsq (c * ledger reqSU2) * GaugeStiffness.gsq (c * ledger reqY) /
          (GaugeStiffness.gsq (c * ledger reqSU2) + GaugeStiffness.gsq (c * ledger reqY)) =
        GaugeStiffness.gsq (c * footprint) := by
  have hd : Disjoint reqSU2 reqY := by
    rw [Finset.disjoint_left]; intro r hr hr'
    simp only [reqSU2, Finset.mem_singleton] at hr
    subst hr; simp [reqY] at hr'
  refine ⟨hd, ?_, ?_⟩
  · unfold ledger; rw [Finset.sum_union hd]; exact footprint_from_rule
  · rw [← footprint_from_rule]
    exact GaugeStiffness.electric hc (by rw [su2_value]; norm_num)
      (by rw [hyper_value]; norm_num [overhead])

/-- **End to end.** From the premises: the assignment is the table, and the table gives the weak
mixing, the strong coupling and the sterile payload in hypercharge. -/
theorem end_to_end (P : Premises) :
    (∀ r, (P.f r = .weak ↔ r ∈ reqSU2) ∧ (P.f r = .hyper ↔ r ∈ reqY)) ∧
      ledger reqSU2 / (ledger reqSU2 + ledger reqY) = 1849 / 8295 ∧
      ((0.11799 : ℝ) < CertifiedConstants.α * (ledger reqSU2 + ledger reqY) / ledger reqColour ∧
        CertifiedConstants.α * (ledger reqSU2 + ledger reqY) / ledger reqColour < 0.11800) ∧
      P.f (.payload 15) = .hyper :=
  ⟨assignment P, weak_mixing P, strong_coupling P, sterile_included P⟩

/-- The premises are satisfiable. -/
def witness : Premises where
  f := fun r => if r = .clock then .weak else .hyper
  clock_weak := by simp
  weak_confined := by intro r h; by_contra hc; simp [hc] at h

end PMConstants.TableConsequences
