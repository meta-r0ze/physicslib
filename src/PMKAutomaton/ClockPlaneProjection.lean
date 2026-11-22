import PMKAutomaton.ClockAlignment

/-!
# Clock-plane projection of the E8 root cosets

For a root `r`, `proj r = (⟨r,cu⟩, ⟨r,cv⟩)` is its projection to the clock
plane.  The spacetime ring step (a spacetime `D₄` root reading `+1`) projects
to `stepS`.  This file records, for the certified placement, how the three
glue cosets project (`glueKey`):

* conjugate spinor `(1,0)` (library class `g = 1`): reading `+1` projects to
  `stepS`; the eight silent roots project to `(0,0)` (internal);
* spinor `(1,1)` (`g = 2`): reading `+1` projects to `stepS - p(cu)`; no
  silent roots;
* vector `(0,1)` (`g = 0`): reading `+1` projects to `stepS - p(cu)`; the two
  silent roots are exactly `cu` and `-cu`, projecting to `±p(cu)` (transverse).

The Step 2 results are linear corollaries: a lap of root events with net clock
reading `43` drifts by `0` in the conjugate-spinor coset, by `-43·p(cu)` in the
spinor coset, and the vector coset can cancel `-43·p(cu)` with `43` copies of
`cu`.  Thus the only coset whose own silent roots can cancel the lap drift
(transverse closure) is the vector coset `g = 0`.
-/

noncomputable section
namespace PMKAutomaton.ClockPlaneProjection
open PMKAutomaton.ClockRing
open PMKAutomaton.ClockAlignment
open PMSubstrate

/-- Clock-plane projection `p(r) = (⟨r,cu⟩, ⟨r,cv⟩)`. -/
def proj (r : V) : ℤ × ℤ := (pair r ClockPlane.cu, pair r ClockPlane.cv)

/-- The projection of the spacetime ring step (a spacetime `D₄` root reading `1`). -/
def stepS : ℤ × ℤ := (1, 0)

/-- The projection of the clock-plane vector `cu`. -/
def pcu : ℤ × ℤ := proj ClockPlane.cu

theorem proj_neg (r : V) : proj (-r) = -proj r := by
  simp [proj, pair_neg_left]

theorem proj_neg_cu : proj (-ClockPlane.cu) = -pcu := by
  rw [proj_neg, pcu]

/-! ## Step 1: coset projections (`List.all`, not a `Finset.filter`) -/

theorem spacetimeStep :
    clockAxisRoots.all (fun r => decide (clockReading r = 1 → proj r = stepS)) = true := by
  decide +kernel

theorem cospinor_plus :
    (rootsOfKey (1,0)).all (fun r => decide (clockReading r = 1 → proj r = stepS)) = true := by
  decide +kernel

theorem cospinor_silent :
    (rootsOfKey (1,0)).all (fun r => decide (clockReading r = 0 → proj r = (0,0))) = true := by
  decide +kernel

theorem spinor_plus :
    (rootsOfKey (1,1)).all (fun r => decide (clockReading r = 1 → proj r = stepS - pcu)) = true := by
  decide +kernel

theorem spinor_no_silent :
    (rootsOfKey (1,1)).all (fun r => decide (clockReading r ≠ 0)) = true := by
  decide +kernel

theorem vector_plus :
    (rootsOfKey (0,1)).all (fun r => decide (clockReading r = 1 → proj r = stepS - pcu)) = true := by
  decide +kernel

theorem vector_silent :
    (rootsOfKey (0,1)).all
      (fun r => decide (clockReading r = 0 → r = ClockPlane.cu ∨ r = -ClockPlane.cu)) = true := by
  decide +kernel

/-! ## Step 2: per-lap drift -/

/-- Integer ring-step reading: `1` for a ring step, `0` for a silent root. -/
def readStep (r : V) : ℤ := if clockReading r = 1 then 1 else 0

def projSum (w : List V) : ℤ × ℤ := (w.map proj).sum

def readSum (w : List V) : ℤ := (w.map readStep).sum

/-- A silent root's transverse correction: `±p(cu)` for `±cu`, `0` otherwise. -/
def silentCorr (r : V) : ℤ × ℤ :=
  if clockReading r = 0 then (if r = ClockPlane.cu then pcu else -pcu) else 0

def silentSum (w : List V) : ℤ × ℤ := (w.map silentCorr).sum

/-- Lap drift: projection of the word minus `43·stepS`. -/
def drift (w : List V) : ℤ × ℤ := projSum w - (43 : ℤ) • stepS

theorem cospinor_step (r : V) (hr : r ∈ rootsOfKey (1,0))
    (h : clockReading r = 1 ∨ clockReading r = 0) :
    proj r = readStep r • stepS := by
  rcases h with h | h
  · have hall := (List.all_eq_true.mp cospinor_plus) r hr
    rw [readStep, ite_eq_left h]
    simpa using (of_decide_eq_true hall) h
  · have hall := (List.all_eq_true.mp cospinor_silent) r hr
    rw [readStep, ite_eq_right (by rw [h]; decide)]
    simp [of_decide_eq_true hall h]

theorem cospinor_word (w : List V)
    (hmem : ∀ r ∈ w, r ∈ rootsOfKey (1,0))
    (hr : ∀ r ∈ w, clockReading r = 1 ∨ clockReading r = 0) :
    projSum w = readSum w • stepS := by
  induction w with
  | nil => simp [projSum, readSum]
  | cons r w ih =>
    have hp : proj r = readStep r • stepS :=
      cospinor_step r (hmem r (by simp)) (hr r (by simp))
    have ih' := ih (fun x hx => hmem x (by simp [hx])) (fun x hx => hr x (by simp [hx]))
    simp only [projSum, readSum, List.map_cons, List.sum_cons] at ih' ⊢
    rw [hp, ih', add_smul]

/-- **Conjugate-spinor lap: zero drift.** -/
theorem cospinor_lap (w : List V)
    (hmem : ∀ r ∈ w, r ∈ rootsOfKey (1,0))
    (hr : ∀ r ∈ w, clockReading r = 1 ∨ clockReading r = 0)
    (hnet : readSum w = 43) :
    drift w = 0 := by
  simp [drift, cospinor_word w hmem hr, hnet]

theorem spinor_step (r : V) (hr : r ∈ rootsOfKey (1,1)) (h : clockReading r = 1) :
    proj r = readStep r • (stepS - pcu) := by
  have hall := (List.all_eq_true.mp spinor_plus) r hr
  rw [readStep, ite_eq_left h]
  simpa using (of_decide_eq_true hall) h

theorem spinor_word (w : List V)
    (hmem : ∀ r ∈ w, r ∈ rootsOfKey (1,1))
    (hr : ∀ r ∈ w, clockReading r = 1) :
    projSum w = readSum w • (stepS - pcu) := by
  induction w with
  | nil => simp [projSum, readSum]
  | cons r w ih =>
    have hp : proj r = readStep r • (stepS - pcu) :=
      spinor_step r (hmem r (by simp)) (hr r (by simp))
    have ih' := ih (fun x hx => hmem x (by simp [hx])) (fun x hx => hr x (by simp [hx]))
    simp only [projSum, readSum, List.map_cons, List.sum_cons] at ih' ⊢
    rw [hp, ih', add_smul]

/-- **Spinor lap: fixed drift `-43·p(cu)`.** -/
theorem spinor_lap (w : List V)
    (hmem : ∀ r ∈ w, r ∈ rootsOfKey (1,1))
    (hr : ∀ r ∈ w, clockReading r = 1)
    (hnet : readSum w = 43) :
    drift w = - (43 : ℤ) • pcu := by
  rw [drift, spinor_word w hmem hr, hnet, smul_sub]
  abel

theorem neg_cu_ne_cu : (-ClockPlane.cu : V) ≠ ClockPlane.cu := by decide +kernel

theorem vector_step (r : V) (hr : r ∈ rootsOfKey (0,1))
    (h : clockReading r = 1 ∨ clockReading r = 0) :
    proj r = readStep r • (stepS - pcu) + silentCorr r := by
  rcases h with h | h
  · have hall := (List.all_eq_true.mp vector_plus) r hr
    rw [readStep, ite_eq_left h, silentCorr, ite_eq_right (by rw [h]; decide)]
    simpa using (of_decide_eq_true hall) h
  · have hall := (List.all_eq_true.mp vector_silent) r hr
    have hmem := of_decide_eq_true hall h
    rw [readStep, ite_eq_right (by rw [h]; decide), silentCorr, ite_eq_left h]
    rcases hmem with he | he
    · subst he; simp [pcu]
    · subst he; rw [proj_neg_cu]; simp [neg_cu_ne_cu]

theorem vector_word (w : List V)
    (hmem : ∀ r ∈ w, r ∈ rootsOfKey (0,1))
    (hr : ∀ r ∈ w, clockReading r = 1 ∨ clockReading r = 0) :
    projSum w = readSum w • (stepS - pcu) + silentSum w := by
  induction w with
  | nil => simp [projSum, readSum, silentSum]
  | cons r w ih =>
    have hp : proj r = readStep r • (stepS - pcu) + silentCorr r :=
      vector_step r (hmem r (by simp)) (hr r (by simp))
    have ih' := ih (fun x hx => hmem x (by simp [hx])) (fun x hx => hr x (by simp [hx]))
    simp only [projSum, readSum, silentSum, List.map_cons, List.sum_cons] at ih' ⊢
    rw [hp, ih', add_smul]
    abel

/-! ## Vector coset: a self-closing lap using `±cu` -/

def vecPlus : V := ((rootsOfKey (0,1)).filter fun r => clockReading r = 1).headD 0

theorem vecPlus_mem : vecPlus ∈ rootsOfKey (0,1) := by decide +kernel
theorem vecPlus_reading : clockReading vecPlus = 1 := by decide +kernel
theorem cu_mem : ClockPlane.cu ∈ rootsOfKey (0,1) := by decide +kernel
theorem cu_silent : clockReading ClockPlane.cu = 0 := by decide +kernel
theorem readStep_cu : readStep ClockPlane.cu = 0 := by decide +kernel
theorem readStep_vecPlus : readStep vecPlus = 1 := by decide +kernel
theorem silentCorr_cu : silentCorr ClockPlane.cu = pcu := by decide +kernel
theorem silentCorr_vecPlus : silentCorr vecPlus = 0 := by decide +kernel

/-- **Vector lap: a self-closing word.**  `43` copies of `cu` cancel the
`-43·p(cu)` drift of `43` vector ring steps. -/
theorem vector_self_closing :
    ∃ w : List V, (∀ r ∈ w, r ∈ rootsOfKey (0,1)) ∧
      (∀ r ∈ w, clockReading r = 1 ∨ clockReading r = 0) ∧
      readSum w = 43 ∧ drift w = 0 := by
  let w := List.replicate 43 ClockPlane.cu ++ List.replicate 43 vecPlus
  have hmem : ∀ r ∈ w, r ∈ rootsOfKey (0,1) := by
    intro r hr
    simp only [w, List.mem_append, List.mem_replicate] at hr
    rcases hr with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact cu_mem
    · exact vecPlus_mem
  have hread : ∀ r ∈ w, clockReading r = 1 ∨ clockReading r = 0 := by
    intro r hr
    simp only [w, List.mem_append, List.mem_replicate] at hr
    rcases hr with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · right; exact cu_silent
    · left; exact vecPlus_reading
  have hsum : readSum w = 43 := by decide +kernel
  have hsilent : silentSum w = (43 : ℤ) • pcu := by decide +kernel
  refine ⟨w, hmem, hread, hsum, ?_⟩
  rw [drift, vector_word w hmem hread, hsum, hsilent, smul_sub]
  abel

/-! ## Self-closing is iff `g = 0` -/

/-- A coset is *self-closing* when one of its clock-silent roots has a nonzero
clock-plane projection; those are the roots that can cancel a lap drift. -/
def selfClosing (k : ZMod 2 × ZMod 2) : Bool :=
  (rootsOfKey k).any fun r => decide (clockReading r = 0 ∧ proj r ≠ (0,0))

/-- **Only the vector coset `g = 0` is self-closing.**  The conjugate-spinor
coset's silent roots are internal (projection `0`); the spinor coset has none. -/
theorem self_closing_iff :
    selfClosing (0,1) = true ∧ selfClosing (1,0) = false ∧ selfClosing (1,1) = false := by
  decide +kernel

end PMKAutomaton.ClockPlaneProjection
