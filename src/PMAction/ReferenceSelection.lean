import PMAction.PersistentBackground
import PMAction.HomogeneousRouting

/-!
# The reference is selected, not prepared

The open item "prepared initial reference" asked for dynamics that prepares the reference
background. The boundary results show closed internal controls cannot do it
(`ReferenceSourceBoundary`, `PrimitiveRecordBoundary.cannot_prepare`). Persistence Mechanics does
not ask for preparation. Its survival law selects: what is observed is what persisted, and the
most persistent configuration is the one of least excess price (`PersistenceSelection`). This
module collects the chain that settles the reference by selection and maintenance.

* `selected_reference`: the most persistent reference configuration is exactly a uniform
  background, every live and record cell holding the same reference value
  (`PersistentBackground.persistent_background`). This is the reference's origin: selection.
* `one_record_per_tick`: the per-tick ledger at the coupling site. Each tick the live value is
  replaced by the record arriving from upstream, and the departing live value (any disturbance) is
  written into the record leaving downstream: one clean record consumed and one record exported
  per tick.
* `consumed_records_distinct`: on an orbit that never returns, the records consumed at different
  ticks start at different sites, so `T` ticks of exact maintenance consume `T` distinct clean
  records.
* `reference_forever`: with the uniform background as the record supply, a homogeneous routing
  that moves the coupling site keeps the reference exact at every tick
  (`HomogeneousRouting.homogeneous_forever`).
* `needs_unbounded`: exact maintenance forever needs an infinite substrate
  (`HomogeneousRouting.forever_needs_infinite`): the record supply is the unbounded background.

The identification used: the uniform background's record cells are the record stream of
`RecordSupply` (`hrec : ∀ x, (s x).2 = r` in `reference_forever`). The actual initial state of the
universe, if asked for, is a cosmological question (Paper VI), not a PMAction one.
-/

noncomputable section
namespace PMAction.ReferenceSelection
open RecordSupply

/-- **The reference's origin is selection.** -/
theorem selected_reference {X : Type*} [Fintype X] [DecidableEq X] {A : Type*} [DecidableEq A]
    (o : X) (e : Equiv.Perm X) (hc : NativeReferenceBackground.Connected o e) (toll β : ℝ)
    (ht : 0 < toll) (hβ : 0 < β) (a : A) (s : NativeCarrierState.Config X A) :
    (∀ t : NativeCarrierState.Config X A,
        Real.exp (-β * NativeReferenceBackground.price o e toll t) ≤
          Real.exp (-β * NativeReferenceBackground.price o e toll s)) ↔
      ∃ r : Fin 2 → A, ∀ x i,
        s (x, ActualRootRepair.label (.inl i)) = r i ∧
        s (x, ActualRootRepair.label (.inr i)) = r i :=
  PersistentBackground.persistent_background o e hc toll β ht hβ a s

/-- **The per-tick ledger.** At the coupling site, one tick consumes the record arriving from
`e o` and exports the departing live value into the record leaving toward `e⁻¹ o`. -/
theorem one_record_per_tick {X A : Type*} [DecidableEq X] (o : X) (e : Equiv.Perm X)
    (s : X → A × A) (t : ℕ) :
    (run o e (t + 1) s o).1 = (run o e t s (e o)).2 ∧
      (run o e (t + 1) s o).2 = (run o e t s (e⁻¹ o)).1 := by
  refine ⟨?_, disturbance_exported o e s t⟩
  simp [run_succ, step]

/-- **Distinct records per tick.** On an orbit that never returns, `eᵐ o ≠ eⁿ o` for `m ≠ n`. -/
theorem consumed_records_distinct {X : Type*} (o : X) (e : Equiv.Perm X)
    (hopen : ∀ m, 1 ≤ m → (e ^ m) o ≠ o) (m n : ℕ) (hmn : m ≠ n) :
    (e ^ m) o ≠ (e ^ n) o := by
  intro h
  rcases Nat.lt_or_gt_of_ne hmn with hlt | hlt
  · apply hopen (n - m) (by omega)
    apply (e ^ m).injective
    rw [← Equiv.Perm.mul_apply, ← pow_add, show m + (n - m) = n by omega, h]
  · apply hopen (m - n) (by omega)
    apply (e ^ n).injective
    rw [← Equiv.Perm.mul_apply, ← pow_add, show n + (m - n) = m by omega, h]

/-- **Maintained forever from the selected background.** -/
theorem reference_forever {d : ℕ} (e : Equiv.Perm (Fin d → ℤ))
    (hcomm : ∀ w x, e (x + w) = e x + w) (o : Fin d → ℤ) (hmove : e o ≠ o) {A : Type*}
    (s : (Fin d → ℤ) → A × A) (r : A) (hrec : ∀ x, (s x).2 = r) (t : ℕ) (ht : 1 ≤ t) :
    (run o e t s o).1 = r :=
  HomogeneousRouting.homogeneous_forever e hcomm o hmove s r hrec t ht

/-- **The supply is unbounded.** -/
theorem needs_unbounded {X A : Type*} [DecidableEq X] (o : X) (e : Equiv.Perm X) (r d : A)
    (hd : d ≠ r)
    (h : ∀ s : X → A × A, (∀ x, (s x).2 = r) → ∀ t, 1 ≤ t → (run o e t s o).1 = r) :
    Infinite X :=
  HomogeneousRouting.forever_needs_infinite o e r d hd h

end PMAction.ReferenceSelection
