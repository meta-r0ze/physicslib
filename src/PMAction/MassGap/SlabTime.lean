import PMAction.MassGap.SlabGeometry
import PMAction.MassGap.ContourGas

/-!
# Time geometry of slab contours

`τ e` is the later tick of an edge's endpoints: `t` for a spatial edge in slice `t`, `s + 1` for the
temporal edge from `s` to `s + 1`.

* `tau_adj`: edges sharing a slab plaquette differ in `τ` by at most `1`.
* `animal_tau`: in a contour (an animal in the plaquette graph), any two edges differ in `τ` by
  at most `|γ| − 1`.
* `tau_incompat`: if contour `r` is incompatible with contour `a` (shares or touches an edge),
  every edge of `r` has `τ ≤ max τ(a) + |r|`.

These turn incompatibility steps into time steps: a chain of contours from slice `0` to slice `L`
has total size at least `L`.
-/

namespace PMAction.MassGap.SlabTime
open Finset SimpleGraph ContourRepresentation ContourGas SlabGeometry

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (L : ℕ)

/-- The later tick of an edge. -/
def tau : Sym2 (V × Fin (L + 1)) → ℕ :=
  Sym2.lift ⟨fun x y => max x.2.val y.2.val, fun _ _ => max_comm _ _⟩

omit [Fintype V] [DecidableEq V] in
@[simp] lemma tau_mk (x y : V × Fin (L + 1)) : tau L s(x, y) = max x.2.val y.2.val := rfl

omit [Fintype V] [DecidableEq V] in
lemma tau_le (e : Sym2 (V × Fin (L + 1))) : tau L e ≤ L := by
  induction e using Sym2.ind with
  | h x y => simp only [tau_mk]; have := x.2.isLt; have := y.2.isLt; omega

/-- **Plaquette-adjacent edges differ in `τ` by at most one.** -/
theorem tau_adj (plaqG : Finset (Finset (Sym2 V))) {e e' : Sym2 (V × Fin (L + 1))}
    (h : (plaqGraph (slabPlaq G L plaqG)).Adj e e') :
    tau L e' ≤ tau L e + 1 := by
  obtain ⟨-, P, hP, he, he'⟩ := h
  rcases mem_union.mp hP with hs | hs
  · obtain ⟨⟨Q, t⟩, -, rfl⟩ := mem_image.mp hs
    obtain ⟨e0, -, rfl⟩ := mem_image.mp he
    obtain ⟨e1, -, rfl⟩ := mem_image.mp he'
    induction e0 using Sym2.ind with
    | h a b =>
      induction e1 using Sym2.ind with
      | h c d => simp
  · obtain ⟨⟨⟨u, v⟩, s⟩, -, rfl⟩ := mem_image.mp hs
    simp only [square, tE, mem_insert, mem_singleton] at he he'
    have h1 : (s.castSucc : Fin (L + 1)).val = s.val := rfl
    have h2 : (s.succ : Fin (L + 1)).val = s.val + 1 := rfl
    rcases he with rfl | rfl | rfl | rfl <;> rcases he' with rfl | rfl | rfl | rfl <;>
      simp only [tau_mk, h1, h2] <;> omega

/-- **A contour spans at most `|γ| − 1` ticks.** -/
theorem animal_tau (plaqG : Finset (Finset (Sym2 V))) {e : Sym2 (V × Fin (L + 1))}
    {γ : Finset (Sym2 (V × Fin (L + 1)))}
    (h : ContourCount.Animal (plaqGraph (slabPlaq G L plaqG)) e γ) :
    ∀ e' ∈ γ, tau L e' + 1 ≤ tau L e + γ.card ∧ tau L e + 1 ≤ tau L e' + γ.card := by
  induction h with
  | single => intro e' he'; simp at he'; subst he'; simp
  | @grow S t u hS ht hadj hu ih =>
    intro e' he'
    rw [card_insert_of_notMem hu]
    rcases mem_insert.mp he' with rfl | he'
    · have h1 := ih t ht
      have h2 := tau_adj G L plaqG hadj
      have h3 := tau_adj G L plaqG hadj.symm
      omega
    · have := ih e' he'; omega

/-- Any two edges of a contour differ in `τ` by at most `|γ| − 1`. -/
theorem contour_span (plaqG : Finset (Finset (Sym2 V))) (Γ' : SimpleGraph (V × Fin (L + 1)))
    [DecidableRel Γ'.Adj] (γ : Contour Γ' (slabPlaq G L plaqG)) {e e' : Sym2 (V × Fin (L + 1))}
    (he : e ∈ γ.1) (he' : e' ∈ γ.1) : tau L e' + 1 ≤ tau L e + γ.1.card := by
  obtain ⟨u, hu⟩ := γ.2.2.2.1
  have hr := PolymerBridge.Animal.reroot hu he
  exact (animal_tau G L plaqG hr e' he').1

/-- **Incompatible contours are close in time.** If `r` is incompatible with `a`, every edge of
`r` lies within `|r|` ticks above some edge of `a`. -/
theorem tau_incompat (plaqG : Finset (Finset (Sym2 V))) (Γ' : SimpleGraph (V × Fin (L + 1)))
    [DecidableRel Γ'.Adj] {a r : Contour Γ' (slabPlaq G L plaqG)}
    (h : Incompat Γ' (slabPlaq G L plaqG) a r) :
    ∃ e ∈ a.1, ∀ e' ∈ r.1, tau L e' ≤ tau L e + r.1.card := by
  rcases h with hd | ⟨e, he, f, hf, hadj⟩
  · obtain ⟨e, hea, her⟩ := Finset.not_disjoint_iff.mp hd
    refine ⟨e, hea, fun e' he' => ?_⟩
    have := contour_span G L plaqG Γ' r her he'
    omega
  · refine ⟨e, he, fun e' he' => ?_⟩
    have h1 := tau_adj G L plaqG hadj
    have h2 := contour_span G L plaqG Γ' r hf he'
    omega

end PMAction.MassGap.SlabTime
