import PMKAutomaton.ClockSymmetryGenerators
import PMKAutomaton.ClockSites

/-!
# Which clock-root symmetries act on the native phase reading?

A lattice symmetry acts on phases only if equal clock readings remain equal.
The whole Gplus/Gpm action does NOT descend. Among the elements that do,
the induced images are respectively identity and {identity, negation}.
The proof uses the time axis and a representative of every clock class,
not an assumed action or a selected set of slice generators.

Negation has one fixed phase, zero, and 21 two-element orbits. Its invariant
sets have every size from 0 through 43; the unique invariant singleton is
{0}. Clock advance is a different operation, not an origin-fixing lattice
symmetry: including every phase translation would leave only empty/all sets.
-/
noncomputable section
namespace PMKAutomaton.ClockPhaseSymmetry
open PMKAutomaton.ClockSymmetry PMKAutomaton.ClockRing

abbrev Phase := Fin 43

def negPhase : Equiv.Perm Phase := ⟨fun t => -t,fun t => -t,neg_neg,neg_neg⟩

def Descends (w : Weyl) (sigma : Equiv.Perm Phase) : Prop :=
  ∀ z, ClockSites.site (w.val z) = sigma (ClockSites.site z)

/-- The doubled time axis reads 2 mod 43; 22 is its multiplicative inverse. -/
def representative (t : Phase) : V := (22*(t.val : ℤ)) • axis 0

theorem representative_sites : ∀ t : Phase,
    ClockSites.site (representative t) = t ∧ ClockSites.site (-representative t) = -t := by
  decide +kernel

theorem representative_image {reverse : Bool} (w : fullGroup reverse) (b : Bool)
    (hw : w.val.val PMSubstrate.ClockPlane.cu = signed b PMSubstrate.ClockPlane.cu) (t : Phase) :
    w.val.val (representative t) = signed b (representative t) := by
  unfold representative
  have ha : w.val.val (axis 0) = signed b (axis 0) := by
    simpa [timeIndex] using time_axes w b hw false
  rw [map_smul,ha]
  cases b <;> simp [signed]

theorem descended_action {reverse : Bool} (w : fullGroup reverse) (b : Bool)
    (hw : w.val.val PMSubstrate.ClockPlane.cu = signed b PMSubstrate.ClockPlane.cu)
    (sigma : Equiv.Perm Phase) (h : Descends w.val sigma) (t : Phase) :
    sigma t = if b then -t else t := by
  have he := h (representative t)
  rw [representative_image w b hw t,(representative_sites t).1] at he
  cases b
  · simpa [signed,(representative_sites t).1] using he.symm
  · simpa [signed,(representative_sites t).2] using he.symm

def induced (reverse : Bool) : Set (Equiv.Perm Phase) :=
  {sigma | ∃ w : fullGroup reverse, Descends w.val sigma}

theorem positive_image : induced false = {1} := by
  ext sigma
  constructor
  · rintro ⟨w,h⟩
    have he : sigma = 1 := by
      apply Equiv.ext
      exact descended_action w false (positive_clock w) sigma h
    exact he
  · intro h
    have he : sigma = 1 := h
    subst sigma
    exact ⟨1,fun _ => rfl⟩

theorem full_image : induced true = {1,negPhase} := by
  ext sigma
  constructor
  · rintro ⟨w,h⟩
    rcases w.property.2 with hw | ⟨_,hw⟩
    · left
      apply Equiv.ext
      exact descended_action w false hw sigma h
    · right
      apply Equiv.ext
      exact descended_action w true hw sigma h
  · rintro (rfl | rfl)
    · exact ⟨1,fun _ => rfl⟩
    · refine ⟨reversingElement,?_⟩
      intro z
      change ClockSites.site (reversingWeyl.val z) = -ClockSites.site z
      rw [reversing_neg]
      change toFin (clockReading (-z)) = -toFin (clockReading z)
      rw [clockReading_neg]
      rfl

/-- A full-group action on phases cannot be assumed: this existing element has no descent. -/
theorem swap_has_no_phase_action : ¬ ∃ sigma, Descends (swapElement false).val sigma := by
  rintro ⟨sigma,h⟩
  have he : sigma ∈ induced false := ⟨swapElement false,h⟩
  rw [positive_image] at he
  have hs : sigma = 1 := he
  have hc := h (basis 2)
  rw [hs] at hc
  exact swap_changes_clockReading hc

/-- The outer swap can take a zero-reading vector to any phase. It is not a phase permutation. -/
def kernelRepresentative (t : Phase) : V :=
  (t.val : ℤ) • (16 : ℤ) • (basis 2 - (22 : ℤ) • basis 1)

theorem kernel_representative_sites : ∀ t : Phase,
    ClockSites.site (kernelRepresentative t) = 0 ∧
      ClockSites.site (swapWeyl.val (kernelRepresentative t)) = t := by decide +kernel

/-- If the ENTIRE root stabilizer is imposed on a phase-only scalar, it forces constancy.
Restricting to descending clock symmetries requires retaining the actual clock structure. -/
theorem full_root_invariance_constant {A : Type*} (f : Phase → A)
    (h : ∀ z, f (ClockSites.site (swapWeyl.val z)) = f (ClockSites.site z)) : ∀ t, f t = f 0 := by
  intro t
  have he := h (kernelRepresentative t)
  rw [(kernel_representative_sites t).1,(kernel_representative_sites t).2] at he
  exact he

def Invariant (s : Finset Phase) : Prop := ∀ t, t ∈ s ↔ -t ∈ s
instance (s : Finset Phase) : Decidable (Invariant s) := inferInstanceAs (Decidable (∀ _, _))

def phaseOrbits : Finset (Finset Phase) := Finset.univ.image fun t => {t,-t}

theorem phase_orbits_card : phaseOrbits.card = 22 := by decide +kernel

theorem neg_fixed_iff_zero : ∀ t : Phase, -t = t ↔ t = 0 := by decide +kernel

theorem invariant_singleton : ∀ t : Phase, Invariant {t} ↔ t = 0 := by decide +kernel

theorem orbit_disjoint_or_equal : ∀ t u : Phase,
    Disjoint ({t,-t} : Finset Phase) {u,-u} ∨ ({t,-t} : Finset Phase) = {u,-u} := by decide +kernel

theorem invariant_iff_orbit_closed (s : Finset Phase) :
    Invariant s ↔ ∀ t ∈ s, ({t,-t} : Finset Phase) ⊆ s := by
  constructor
  · intro h t ht u hu
    simp only [Finset.mem_insert,Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact ht
    · exact (h t).mp ht
  · intro h t
    constructor
    · intro ht; exact h t ht (by simp)
    · intro ht
      have := h (-t) ht (by simp : t ∈ ({-t,-(-t)} : Finset Phase))
      exact this

/-- One witness of each invariant cardinality; no preferred gate cardinality is assumed. -/
def sizedInvariant (k : Fin 44) : Finset Phase := Finset.univ.filter fun t =>
  if t = 0 then k.val % 2 = 1 else min t.val (43-t.val) ≤ k.val/2

theorem all_invariant_sizes : ∀ k : Fin 44,
    Invariant (sizedInvariant k) ∧ (sizedInvariant k).card = k.val := by decide +kernel

theorem orbit_selector_count : Fintype.card (Fin 22 → Bool) = 4194304 := by norm_num

end PMKAutomaton.ClockPhaseSymmetry
