import PMElementaryParticles.HeavyFlipControl
import PMKAutomaton.Interface

/-!
# Native parity, address and clock obstructions for the heavy flip

Modulo-two matched probes and the actual in-band read/undo event tariff
cannot detect the orientation of an antipodal input. The untagged glued
register also aliases each heavy wall with a light wall. Finally, the
clock's closed single-control mask family permits both idle and excursion
schedules. Its clock period alone imposes no heavy-flip cadence.
-/

noncomputable section
namespace PMElementaryParticles.HeavyFlipNativeBoundary

open HeavyFlipControl ControlledGluedRegister GluedRegister
open PMAction PMSubstrate.Lattices
open PMConstants.PacketGaugeActions
open Matrix

/-- Any fixed lattice probe at the substrate's modulo-two resolution
has the same output on opposite orientations. -/
theorem matched_probe_neg (probe z : SubstrateReflection.Lattice) :
    MatchedLatticeProbe.outcome probe (-z) = MatchedLatticeProbe.outcome probe z := by
  have h : pairing (-z) probe = -pairing z probe := by
    simp [pairing, neg_dotProduct]
  simp [MatchedLatticeProbe.outcome, h]

/-- Moving the in-band accumulator by the existing root cannot distinguish
the sign, even when read and undo are priced separately. -/
theorem in_band_tariff_neg {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (sample : Ω → SubstrateReflection.Lattice) (mass : Ω → ℝ) (toll : ℝ) :
    EventAccounting.cost toll mass (InBandRootReadout.events (fun i => -sample i)) =
      EventAccounting.cost toll mass (InBandRootReadout.events sample) := by
  have reflect_neg (z : SubstrateReflection.Lattice) :
      SubstrateReflection.reflect (-z) = -SubstrateReflection.reflect z := by
    rw [SubstrateReflection.reflect_coordinates, SubstrateReflection.reflect_coordinates]
    ext i
    by_cases h : i = 2
    · subst i
      simp [Pi.neg_apply]
      ring
    · simp [Function.update_of_ne h, Pi.neg_apply]
  congr 1
  funext i
  ext ω
  simp only [InBandRootReadout.events, Finset.mem_filter, Finset.mem_univ, true_and,
    reflect_neg]
  split <;> simp

/-- The alias between an untagged heavy root and a light root occurs on
each incoming wall. No common clean ancillary seed can resolve it. -/
theorem no_untagged_heavy_flip (b : Bool) (step : Wt × Wt → Wt × Wt)
    (heavy : ∀ c a, ProtocolInventory.active c = b →
      step (encode 0 c a) = encode 0 (opposite c) a)
    (light : ∀ g : Fin 3, g ≠ 0 → ∀ c a, step (encode g c a) = encode g c a) :
    False := by
  let ca : Channels := .inl (0, 0)
  let cs : Channels := .inr (.inl (0, 0))
  cases b
  · have halias : encode 0 cs 2 = encode 2 ca 2 := by decide +kernel
    have h := heavy cs 2 rfl
    rw [halias, light 2 (by decide) ca 2, ← halias] at h
    exact (by decide +kernel : encode 0 cs 2 ≠ encode 0 (opposite cs) 2) h
  · have halias : encode 0 ca 2 = encode 1 cs 2 := by decide +kernel
    have h := heavy ca 2 rfl
    rw [halias, light 1 (by decide) cs 2, ← halias] at h
    exact (by decide +kernel : encode 0 ca 2 ≠ encode 0 (opposite ca) 2) h

/-- A finite reversible update cannot prepare a clean record from every
wire and record input. Reset must retain the discarded information elsewhere
or be restricted to a prepared domain. -/
theorem no_closed_cleaning (reset : Equiv.Perm (Wire × Record)) :
    ¬ ∀ w : Wire × Record, (reset w).2 = (false, false) := by
  intro clean
  let c : Channels := .inl (0, 0)
  obtain ⟨w, hw⟩ := reset.surjective ((0, c, 0), (true, false))
  have h := clean w
  rw [hw] at h
  cases h

/-! ### Closure and firing for a supplied flip at mask boundaries -/

abbrev State := (Wire × Record) × Fin PMSubstrate.E8Values.Delta

/-- The same clock rebase used for a native reflection, now on the
mathematically admitted record-controlled endpoint permutation. -/
def rebase (r : Record) (mask : Fin PMSubstrate.E8Values.Delta → Bool) : Equiv.Perm State :=
  Equiv.prodCongrLeft fun t => if mask t then controlledFlip r else Equiv.refl _

def tick (r : Record) (mask : Fin PMSubstrate.E8Values.Delta → Bool) : Equiv.Perm State :=
  (rebase r mask).symm.trans ((Equiv.prodCongr (Equiv.refl _) (finRotate PMSubstrate.E8Values.Delta)).trans (rebase r mask))

theorem tick_rebased (r : Record) (mask : Fin PMSubstrate.E8Values.Delta → Bool) (w : Wire × Record) (t : Fin PMSubstrate.E8Values.Delta) :
    tick r mask (rebase r mask (w, t)) = rebase r mask (w, finRotate PMSubstrate.E8Values.Delta t) := by
  simp [tick]

theorem cycle_closes (r : Record) (mask : Fin PMSubstrate.E8Values.Delta → Bool) (s : State) :
    (tick r mask)^[PMSubstrate.E8Values.Delta] s = s := by
  have run (n : ℕ) (w : Wire × Record) (t : Fin PMSubstrate.E8Values.Delta) :
      (tick r mask)^[n] (rebase r mask (w, t)) =
        rebase r mask (w, (finRotate PMSubstrate.E8Values.Delta)^[n] t) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, tick_rebased, Function.iterate_succ_apply']
  obtain ⟨⟨w, t⟩, rfl⟩ := (rebase r mask).surjective s
  rw [run, CarrierReferenceCycle.clock_closes]

/-- For a ready heavy input on either wall, a boundary is exactly an
endpoint flip. The test is the same for both orientations. -/
theorem boundary_flips (c : Channels) (a : Fin 8) :
    controlledFlip (labelRecord c) ((0, c, a), labelRecord c) =
      ((0, opposite c, a), labelRecord c) := by
  simp [controlledFlip, direct_iff]

private theorem rebase_fst (r : Record) (mask : Fin PMSubstrate.E8Values.Delta → Bool) (w : Wire × Record)
    (t : Fin PMSubstrate.E8Values.Delta) :
    (rebase r mask (w, t)).1 = if mask t then controlledFlip r w else w := by
  rw [rebase, Equiv.prodCongrLeft_apply]
  cases mask t <;> rfl

theorem tick_event_iff (r : Record) (mask : Fin PMSubstrate.E8Values.Delta → Bool) (w : Wire × Record) (t : Fin PMSubstrate.E8Values.Delta) :
    (tick r mask (rebase r mask (w, t))).1 ≠ (rebase r mask (w, t)).1 ↔
      t ∈ CarrierReferenceCycle.boundaries mask ∧ controlledFlip r w ≠ w := by
  rw [tick_rebased, rebase_fst, rebase_fst]
  simp only [CarrierReferenceCycle.boundaries, Finset.mem_filter, Finset.mem_univ, true_and]
  cases mask t <;> cases mask (finRotate PMSubstrate.E8Values.Delta t)
  · change w ≠ w ↔ false ≠ false ∧ controlledFlip r w ≠ w
    simp only [ne_eq, not_true_eq_false, false_and]
  · change controlledFlip r w ≠ w ↔ true ≠ false ∧ controlledFlip r w ≠ w
    simp only [ne_eq, Bool.true_eq_false, not_false_eq_true, true_and]
  · change w ≠ controlledFlip r w ↔ false ≠ true ∧ controlledFlip r w ≠ w
    simpa only [ne_eq, Bool.false_eq_true, not_false_eq_true, true_and] using
      (ne_comm : w ≠ controlledFlip r w ↔ controlledFlip r w ≠ w)
  · change controlledFlip r w ≠ controlledFlip r w ↔ true ≠ true ∧ controlledFlip r w ≠ w
    simp only [ne_eq, not_true_eq_false, false_and]

open scoped Classical in
/-- The idle and excursion schedules have the same 43-tick closure. Their
pointwise endpoint activity differs on every ready heavy wall input. -/
theorem idle_and_excursion_counts (c : Channels) (a : Fin 8) :
    let r := labelRecord c
    let w : Wire × Record := ((0, c, a), r)
    (Finset.univ.filter (fun t : Fin PMSubstrate.E8Values.Delta =>
      (tick r (fun _ => false) (rebase r (fun _ => false) (w, t))).1 ≠
        (rebase r (fun _ => false) (w, t)).1)).card = 0 ∧
    (Finset.univ.filter (fun t : Fin PMSubstrate.E8Values.Delta =>
      (tick r CarrierReferenceCycle.excursionMask
        (rebase r CarrierReferenceCycle.excursionMask (w, t))).1 ≠
        (rebase r CarrierReferenceCycle.excursionMask (w, t)).1)).card = 2 := by
  have hc : opposite c ≠ c := by
    intro h
    have ha := opposite_active c
    rw [h] at ha
    cases h' : ProtocolInventory.active c <;> simp [h'] at ha
  dsimp only
  simp_rw [tick_event_iff, boundary_flips]
  have hz : CarrierReferenceCycle.boundaries (fun _ => false) = ∅ := by
    simp [CarrierReferenceCycle.boundaries]
  have filter_eq (m : Fin PMSubstrate.E8Values.Delta → Bool) :
      Finset.univ.filter (fun t =>
        t ∈ CarrierReferenceCycle.boundaries m ∧
          (((0 : Fin 3), opposite c, a), labelRecord c) ≠ (((0 : Fin 3), c, a), labelRecord c)) =
        CarrierReferenceCycle.boundaries m := by
    ext t
    simp [hc]
  rw [filter_eq, filter_eq, hz, CarrierReferenceCycle.excursion_boundaries]
  decide

end PMElementaryParticles.HeavyFlipNativeBoundary
