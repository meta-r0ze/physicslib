import PMAction.Machine.ReferenceMaintenance
import PMAction.Machine.CarrierWeyl

/-!
# Refresh events are root events

`ReferenceMaintenance` is a reversible task model: each job has a discrepancy bit and a record bit,
and its event swaps them. It is not identified with E8 events there. Here it is.

A job lives at its own site, in a cell of two carriers `v` and `s v`, where `s` is a simple root
reflection of the carrier sector (`CarrierWeyl.simple`, a certified E8 reflection) that moves `v`.
The discrepancy is the occupation of `v`, the record the occupation of `s v` (`encode`).

* `moved_exists`: every simple reflection moves some carrier, so every job has a cell.
* `encode_swap`: the root reflection, acting on the cell's occupation, swaps discrepancy and
  record. That is the task model's event.
* `encode_injective`: the encoding is faithful.
* `event_is_root`, `run_is_root`: a job's event is the root reflection at its site, and every
  schedule is the corresponding word of site root events.
* `canonical_is_root`: the minimal restoring schedule (each required job once,
  `ReferenceMaintenance.canonical_restores`, at the Economy-minimal cost
  `minimum_executable_cost`) is a word of root events, one per required resource, and it clears
  every required discrepancy.

So the refresh events of the ledgers are substrate primitives: one root reflection per refreshed
resource. Which resources a sector must refresh (the requirement table) is separate.
-/

namespace PMAction.RootMaintenance
open CarrierEvents CarrierWeyl ReferenceMaintenance

lemma ss (c : Fin 3) (j : Fin 4) (x : Carrier c) : simple c j (simple c j x) = x :=
  Subtype.ext (simple_twice j x.1)

/-- **Every simple reflection moves some carrier.** -/
theorem moved_exists : ∀ (c : Fin 3) (j : Fin 4), ∃ v : Carrier c, simple c j v ≠ v := by
  decide +kernel

/-- A job's two bits as the occupation of its cell `{v, s v}`. -/
def encode (c : Fin 3) (j : Fin 4) (v : Carrier c) (b : Bool × Bool) : Carrier c → Bool :=
  fun x => if x = v then b.1 else if x = simple c j v then b.2 else false

/-- **The root reflection swaps discrepancy and record.** -/
theorem encode_swap (c : Fin 3) (j : Fin 4) (v : Carrier c) (hv : simple c j v ≠ v)
    (b : Bool × Bool) :
    encode c j v (b.2, b.1) = fun x => encode c j v b (simple c j x) := by
  funext x
  simp only [encode]
  by_cases h1 : x = v
  · subst h1; simp [hv]
  · by_cases h2 : x = simple c j v
    · subst h2; simp [hv, ss]
    · have h3 : simple c j x ≠ v := fun h => h2 (by rw [← h, ss])
      have h4 : simple c j x ≠ simple c j v := fun h => h1 ((simple c j).injective h)
      simp [h1, h2, h3, h4]

/-- **The encoding is faithful.** -/
theorem encode_injective (c : Fin 3) (j : Fin 4) (v : Carrier c) (hv : simple c j v ≠ v) :
    Function.Injective (encode c j v) := by
  intro a b h
  have h1 := congrFun h v
  have h2 := congrFun h (simple c j v)
  simp only [encode] at h1
  simp only [encode, hv, ↓reduceIte] at h2
  exact Prod.ext h1 (by simpa using h2)

variable {R : Type*} [DecidableEq R]

/-- The encoded state: job `r` at its own site, in the cell of reflection `jr r`. -/
def encodeState (c : Fin 3) (jr : R → Fin 4) (v : R → Carrier c) (s : State R) :
    R → Carrier c → Bool := fun r => encode c (jr r) (v r) (s r)

/-- The root event at site `r`: its reflection acts on that site's occupation only. -/
def siteEvent (c : Fin 3) (jr : R → Fin 4) (r : R) (occ : R → Carrier c → Bool) :
    R → Carrier c → Bool :=
  fun q => if q = r then fun x => occ q (simple c (jr q) x) else occ q

/-- A word of site root events. -/
def runSites (c : Fin 3) (jr : R → Fin 4) : List R → (R → Carrier c → Bool) →
    (R → Carrier c → Bool)
  | [], occ => occ
  | r :: L, occ => siteEvent c jr r (runSites c jr L occ)

/-- **A job's event is the root reflection at its site.** -/
theorem event_is_root (c : Fin 3) (jr : R → Fin 4) (v : R → Carrier c)
    (hv : ∀ r, simple c (jr r) (v r) ≠ v r) (r : R) (s : State R) :
    encodeState c jr v (event r s) = siteEvent c jr r (encodeState c jr v s) := by
  funext q
  by_cases h : q = r
  · subst h
    have e : event q s q = ((s q).2, (s q).1) := by simp [event]
    simp only [encodeState, siteEvent, e]
    exact encode_swap c (jr q) (v q) (hv q) (s q)
  · have e : event r s q = s q := by simp [event, h]
    simp only [encodeState, siteEvent, h, ↓reduceIte, e]

/-- **Every schedule is a word of site root events.** -/
theorem run_is_root (c : Fin 3) (jr : R → Fin 4) (v : R → Carrier c)
    (hv : ∀ r, simple c (jr r) (v r) ≠ v r) (L : List R) (s : State R) :
    encodeState c jr v (run L s) = runSites c jr L (encodeState c jr v s) := by
  induction L with
  | nil => rfl
  | cons r L ih =>
    simp only [run, runSites]
    rw [event_is_root c jr v hv, ih]

/-- **The minimal restoring schedule is one root event per required resource**, and it clears
every required discrepancy. -/
theorem canonical_is_root (c : Fin 3) (jr : R → Fin 4) (v : R → Carrier c)
    (hv : ∀ r, simple c (jr r) (v r) ≠ v r) (req : Finset R) (d : R → Bool) (r : R)
    (hr : r ∈ req) :
    runSites c jr req.toList (encodeState c jr v (prepare d)) r (v r) = false := by
  rw [← run_is_root c jr v hv]
  simp [encodeState, encode, canonical_record req d r hr]

end PMAction.RootMaintenance
