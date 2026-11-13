import PMConstants.WeakLocality
import PMConstants.TableConsequences

/-!
# Weak is confined to the clock: the weak fraction end to end

`TableConsequences.Premises` asks for a refresh assignment in which weak refreshes the clock row
and nothing else. `WeakLocality` shows what weak's own events can do for each resource:

* the clock row: reached (`weak_covers_iff`, `μ = 0`);
* the spatial rows: not reached, weak's events do not move (`weak_covers_iff`);
* the wires: not reached, a wire is displaced along a root (`weak_misses_wires`);
* a payload channel: nothing left to restore once the reference is, since every weak displacement
  that fixes the reference is the identity (`reference_restores_all`).

`WeakReach` collects these, and `weakReach_iff` shows weak can do something only for the clock.

* `premises_from_reach`: an assignment that gives weak the clock and gives weak a resource only
  where weak can do something is exactly a `TableConsequences.Premises`.
* `weak_fraction`: so the weak fraction is `1849/8295`, with the strong coupling and the sterile
  payload in hypercharge (`TableConsequences.end_to_end`).

Premise: a sector refreshes a resource only where its own events reach or restore something (the
abelian phase rides on events that occur), the reading `PMAction.FactorRepair` uses.
-/

namespace PMConstants.WeakConfinement
open PMConstants GaugeLedgers RequirementComplement WeakLocality

/-- What weak's own events can do for each resource. -/
def WeakReach : Res → Prop
  | .clock => WeakCovers 0
  | .space => ∃ μ : Fin 4, μ ≠ 0 ∧ WeakCovers μ
  | .wires => ∃ (r : Fin 4 → ℤ), (∃ i j, i ≠ j ∧ r i ≠ 0 ∧ r j ≠ 0) ∧
      ∃ (t : ℕ) (L : List (Fin 4 → ℤ)), (∀ d ∈ L, d = 0) ∧ (t : ℤ) • e 0 + L.sum = r
  | .payload _ => ∃ (n : ℕ) (ref : CarrierRepresentation.V),
      (CarrierActions.weak ^ n) (Sum.inl ref) = Sum.inl ref ∧ CarrierActions.weak ^ n ≠ 1

/-- **Weak can do something only for the clock.** -/
theorem weakReach_iff (r : Res) : WeakReach r ↔ r = .clock := by
  cases r with
  | clock => exact ⟨fun _ => rfl, fun _ => (weak_covers_iff 0).2 rfl⟩
  | space =>
    refine ⟨fun ⟨μ, hμ, h⟩ => absurd ((weak_covers_iff μ).1 h) hμ, fun h => ?_⟩
    cases h
  | wires =>
    refine ⟨fun ⟨r, hr, t, L, hL, h⟩ => absurd h (weak_misses_wires r hr t L hL), fun h => ?_⟩
    cases h
  | payload i =>
    refine ⟨fun ⟨n, ref, h, hn⟩ => absurd (reference_restores_all n ref h) hn, fun h => ?_⟩
    cases h

/-- **The premises of the requirement table, from weak's reach.** -/
def premises_from_reach (f : Res → EW) (hclock : f .clock = .weak)
    (hcap : ∀ r, f r = .weak → WeakReach r) : TableConsequences.Premises where
  f := f
  clock_weak := hclock
  weak_confined := fun r h => (weakReach_iff r).1 (hcap r h)

/-- **The weak fraction, end to end.** -/
theorem weak_fraction (f : Res → EW) (hclock : f .clock = .weak)
    (hcap : ∀ r, f r = .weak → WeakReach r) :
    (∀ r, (f r = .weak ↔ r ∈ reqSU2) ∧ (f r = .hyper ↔ r ∈ reqY)) ∧
      ledger reqSU2 / (ledger reqSU2 + ledger reqY) = 1849 / 8295 ∧
      ((0.11799 : ℝ) < CertifiedConstants.α * (ledger reqSU2 + ledger reqY) / ledger reqColour ∧
        CertifiedConstants.α * (ledger reqSU2 + ledger reqY) / ledger reqColour < 0.11800) ∧
      f (.payload 15) = .hyper :=
  TableConsequences.end_to_end (premises_from_reach f hclock hcap)

end PMConstants.WeakConfinement
