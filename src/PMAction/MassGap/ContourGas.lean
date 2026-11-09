import PMAction.MassGap.ContourRepresentation
import PMAction.MassGap.PolymerBridge

/-!
# The PM history sum is exactly a contour gas

With `ContourRepresentation` (cuts = even edge sets; plaquette-closed pieces of cuts are cuts),
this file proves the exact identity between the even-edge-set sum and the polymer partition
function of contours, so `GapChain.contour_decay` applies to PM's spacetime model as it stands.

Setting: a connected graph `Γ` (spacetime sites), a family `plaq` of plaquettes generating the
cycle space, and the **plaquette graph** on edges: two edges are adjacent when some plaquette
contains both.

* A **contour** is a nonempty set of graph edges that is even (meets every closed walk evenly)
  and connected in the plaquette graph (an animal there).
* Two contours are **incompatible** when they share an edge or contain plaquette-adjacent edges.
* `contour_gas_eq`: for every `q`,
  `Σ_{C even edge set} q^|C| = Σ_{compatible families I of contours} Π_{γ∈I} q^|γ|`.
  The bijection sends a family to its union and an even set to its plaquette-closed components.
* With `ContourRepresentation.exists_potential` / `potential_unique`, the left side is the sum
  over vacuum-rooted histories of `q^cost`, which is PM's history sum with `q = e^{−β}`
  (`SpacetimeCost.history_weight`).
-/

namespace PMAction.MassGap.ContourGas
open Finset ContourRepresentation

variable {X : Type*} [Fintype X] [DecidableEq X] (Γ : SimpleGraph X) [DecidableRel Γ.Adj]
  (plaq : Finset (Finset (Sym2 X)))

/-- The plaquette graph on edges. -/
def plaqGraph : SimpleGraph (Sym2 X) where
  Adj e e' := e ≠ e' ∧ ∃ P ∈ plaq, e ∈ P ∧ e' ∈ P
  symm := ⟨fun _ _ ⟨h, P, hP, h1, h2⟩ => ⟨h.symm, P, hP, h2, h1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A contour: a nonempty, even set of graph edges, connected in the plaquette graph. -/
def IsContour (γ : Finset (Sym2 X)) : Prop :=
  γ.Nonempty ∧ γ ⊆ Γ.edgeFinset ∧ (∃ e, ContourCount.Animal (plaqGraph plaq) e γ) ∧
    EvenCycles Γ γ

/-- Contours as a type. -/
def Contour := {γ : Finset (Sym2 X) // IsContour Γ plaq γ}

noncomputable instance : Fintype (Contour Γ plaq) := by
  classical exact Subtype.fintype _

noncomputable instance : DecidableEq (Contour Γ plaq) := Classical.decEq _

/-- Incompatibility: sharing an edge or touching through a plaquette. -/
def Incompat (γ γ' : Contour Γ plaq) : Prop :=
  ¬ Disjoint γ.1 γ'.1 ∨ ∃ e ∈ γ.1, ∃ e' ∈ γ'.1, (plaqGraph plaq).Adj e e'

noncomputable instance : DecidableRel (Incompat Γ plaq) := Classical.decRel _

lemma incompat_symm (a b : Contour Γ plaq) : Incompat Γ plaq a b → Incompat Γ plaq b a := by
  rintro (h | ⟨e, he, e', he', hadj⟩)
  · exact Or.inl (fun hd => h hd.symm)
  · exact Or.inr ⟨e', he', e, he, hadj.symm⟩

/-- `A` is closed within `C` under plaquette adjacency. -/
def Closed (A C : Finset (Sym2 X)) : Prop :=
  ∀ e ∈ A, ∀ e' ∈ C, (plaqGraph plaq).Adj e e' → e' ∈ A

omit [Fintype X] [DecidableEq X] in
/-- Closedness in the plaquette graph gives closedness in the plaquette form. -/
lemma closed_plaq {A C : Finset (Sym2 X)} (h : Closed plaq A C) :
    ∀ e ∈ A, ∀ e' ∈ C, (∃ P ∈ plaq, e ∈ P ∧ e' ∈ P) → e' ∈ A := by
  intro e he e' he' ⟨P, hP, h1, h2⟩
  by_cases hee : e = e'
  · rw [← hee]; exact he
  · exact h e he e' he' ⟨hee, P, hP, h1, h2⟩

omit [Fintype X] in
/-- A closed set containing a site of an animal inside `C` contains the whole animal. -/
lemma animal_sub_closed {A C γ : Finset (Sym2 X)} {e : Sym2 X}
    (hγ : ContourCount.Animal (plaqGraph plaq) e γ) (hγC : γ ⊆ C) (hA : Closed plaq A C)
    (he : e ∈ A) : γ ⊆ A := by
  induction hγ with
  | single => simpa using he
  | @grow S t u hS ht hadj hu ih =>
    have hSC : S ⊆ C := fun x hx => hγC (mem_insert_of_mem hx)
    have hSA := ih hSC
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hA t (hSA ht) x (hγC (mem_insert_self _ _)) hadj
    · exact hSA hx

/-- Two closed contour pieces of `C` that share an edge are equal. -/
lemma closed_eq {C : Finset (Sym2 X)} {γ γ' : Contour Γ plaq} (h1 : γ.1 ⊆ C) (h2 : γ'.1 ⊆ C)
    (c1 : Closed plaq γ.1 C) (c2 : Closed plaq γ'.1 C) {e : Sym2 X} (he : e ∈ γ.1)
    (he' : e ∈ γ'.1) : γ = γ' := by
  obtain ⟨u, hu⟩ := γ.2.2.2.1
  obtain ⟨u', hu'⟩ := γ'.2.2.2.1
  have r := PolymerBridge.Animal.reroot hu he
  have r' := PolymerBridge.Animal.reroot hu' he'
  apply Subtype.ext
  exact le_antisymm (animal_sub_closed plaq r h1 c2 he') (animal_sub_closed plaq r' h2 c1 he)

/-- The union of a family. -/
def union (I : Finset (Contour Γ plaq)) : Finset (Sym2 X) := I.biUnion fun γ => γ.1

lemma mem_union_iff {I : Finset (Contour Γ plaq)} {e : Sym2 X} :
    e ∈ union Γ plaq I ↔ ∃ γ ∈ I, e ∈ γ.1 := by
  simp [union]

/-- Members of an independent family are closed in its union. -/
lemma closed_in_union {I : Finset (Contour Γ plaq)}
    (hI : PolymerConvergence.Independent (Incompat Γ plaq) I) {γ : Contour Γ plaq} (hγ : γ ∈ I) :
    Closed plaq γ.1 (union Γ plaq I) := by
  intro e he e' he' hadj
  obtain ⟨γ', hγ', he'γ'⟩ := (mem_union_iff Γ plaq).mp he'
  by_cases h : γ = γ'
  · rw [h]; exact he'γ'
  · exact absurd (Or.inr ⟨e, he, e', he'γ', hadj⟩) (hI γ hγ γ' hγ' h)

/-- The components of an edge set: contours inside it, closed within it. -/
noncomputable def comps (C : Finset (Sym2 X)) : Finset (Contour Γ plaq) := by
  classical exact univ.filter fun γ => γ.1 ⊆ C ∧ Closed plaq γ.1 C

lemma mem_comps {C : Finset (Sym2 X)} {γ : Contour Γ plaq} :
    γ ∈ comps Γ plaq C ↔ γ.1 ⊆ C ∧ Closed plaq γ.1 C := by
  classical
  simp [comps]

/-- Left inverse: the components of the union of an independent family are the family. -/
theorem comps_union {I : Finset (Contour Γ plaq)}
    (hI : PolymerConvergence.Independent (Incompat Γ plaq) I) : comps Γ plaq (union Γ plaq I) = I := by
  ext γ
  rw [mem_comps]
  constructor
  · rintro ⟨hsub, hcl⟩
    obtain ⟨e, he⟩ := γ.2.1
    obtain ⟨γ', hγ', he'⟩ := (mem_union_iff Γ plaq).mp (hsub he)
    have hsub' : γ'.1 ⊆ union Γ plaq I := fun x hx => (mem_union_iff Γ plaq).mpr ⟨γ', hγ', hx⟩
    rw [closed_eq Γ plaq hsub hsub' hcl (closed_in_union Γ plaq hI hγ') he he']
    exact hγ'
  · intro hγ
    exact ⟨fun x hx => (mem_union_iff Γ plaq).mpr ⟨γ, hγ, hx⟩, closed_in_union Γ plaq hI hγ⟩

/-- Components of any set are pairwise compatible. -/
theorem comps_independent (C : Finset (Sym2 X)) :
    PolymerConvergence.Independent (Incompat Γ plaq) (comps Γ plaq C) := by
  intro a ha b hb hab hinc
  rw [mem_comps] at ha hb
  rcases hinc with h | ⟨e, he, e', he', hadj⟩
  · obtain ⟨e, hea, heb⟩ := Finset.not_disjoint_iff.mp h
    exact hab (closed_eq Γ plaq ha.1 hb.1 ha.2 hb.2 hea heb)
  · have : e' ∈ a.1 := ha.2 e he e' (hb.1 he') hadj
    exact hab (closed_eq Γ plaq ha.1 hb.1 ha.2 hb.2 this he')

/-! ### Every edge of an even set lies in a component -/

/-- The plaquette graph restricted to `C`. -/
def within (C : Finset (Sym2 X)) : SimpleGraph (Sym2 X) where
  Adj e e' := (plaqGraph plaq).Adj e e' ∧ e ∈ C ∧ e' ∈ C
  symm := ⟨fun _ _ ⟨h, h1, h2⟩ => ⟨h.symm, h2, h1⟩⟩
  loopless := ⟨fun _ h => h.1.1 rfl⟩

omit [Fintype X] [DecidableEq X] in
lemma within_le (C : Finset (Sym2 X)) : within plaq C ≤ plaqGraph plaq := fun _ _ h => h.1

/-- The edges of `C` reachable from `e` inside `C`. -/
noncomputable def reach (C : Finset (Sym2 X)) (e : Sym2 X) : Finset (Sym2 X) := by
  classical exact C.filter fun e' => (within plaq C).Reachable e e'

omit [Fintype X] [DecidableEq X] in
lemma mem_reach {C : Finset (Sym2 X)} {e e' : Sym2 X} :
    e' ∈ reach plaq C e ↔ e' ∈ C ∧ (within plaq C).Reachable e e' := by
  classical
  simp [reach]

omit [Fintype X] in
lemma walk_support_sub {C : Finset (Sym2 X)} {e x : Sym2 X} (he : e ∈ C)
    (p : (within plaq C).Walk e x) : p.support.toFinset ⊆ reach plaq C e := by
  intro y hy
  rw [List.mem_toFinset] at hy
  rw [mem_reach]
  refine ⟨?_, ⟨p.takeUntil y hy⟩⟩
  -- every vertex of a walk in `within C` other than the start lies in `C`
  induction p with
  | nil => simp at hy; rw [hy]; exact he
  | @cons a b c h q ih =>
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact he
    · exact ih h.2.2 hy

omit [Fintype X] in
/-- The reachable set from `e` is an animal rooted at `e`. -/
lemma reach_animal {C : Finset (Sym2 X)} {e : Sym2 X} (he : e ∈ C) :
    ContourCount.Animal (plaqGraph plaq) e (reach plaq C e) := by
  classical
  have key : ∀ T : Finset (Sym2 X), T ⊆ reach plaq C e →
      ∃ A, ContourCount.Animal (plaqGraph plaq) e A ∧ T ⊆ A ∧ A ⊆ reach plaq C e := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨{e}, ContourCount.Animal.single, empty_subset _, ?_⟩
      intro x hx; rw [mem_singleton] at hx; rw [hx, mem_reach]; exact ⟨he, SimpleGraph.Reachable.refl e⟩
    | @insert x T hx ih =>
      intro hT
      obtain ⟨A, hA, hTA, hAR⟩ := ih fun y hy => hT (mem_insert_of_mem hy)
      have hxR := hT (mem_insert_self x T)
      obtain ⟨p⟩ := ((mem_reach plaq).mp hxR).2
      let p' := p.mapLe (within_le plaq C)
      have hA' := PolymerBridge.Animal.grow_walk p' A hA hA.root_mem
      refine ⟨A ∪ p'.support.toFinset, hA', ?_, ?_⟩
      · intro y hy
        rcases mem_insert.mp hy with rfl | hy
        · apply mem_union_right
          rw [List.mem_toFinset, SimpleGraph.Walk.support_mapLe_eq_support]
          exact p.end_mem_support
        · exact mem_union_left _ (hTA hy)
      · intro y hy
        rcases mem_union.mp hy with hy | hy
        · exact hAR hy
        · rw [List.mem_toFinset, SimpleGraph.Walk.support_mapLe_eq_support] at hy
          exact walk_support_sub plaq he p (List.mem_toFinset.mpr hy)
  obtain ⟨A, hA, h1, h2⟩ := key (reach plaq C e) subset_rfl
  have : A = reach plaq C e := le_antisymm h2 h1
  rwa [this] at hA

omit [Fintype X] [DecidableEq X] in
lemma reach_closed {C : Finset (Sym2 X)} (e : Sym2 X) : Closed plaq (reach plaq C e) C := by
  intro x hx y hy hadj
  rw [mem_reach] at hx ⊢
  exact ⟨hy, hx.2.trans (SimpleGraph.Adj.reachable ⟨hadj, hx.1, hy⟩)⟩

/-- Right inverse: an even edge set is the union of its components. -/
theorem union_comps (hconn : Γ.Connected) (r : X) (hgen : PlaquettesGenerate Γ plaq)
    (hplaq : ∀ P ∈ plaq, IsPlaquette Γ P) {C : Finset (Sym2 X)} (hCE : C ⊆ Γ.edgeFinset)
    (hC : EvenCycles Γ C) : union Γ plaq (comps Γ plaq C) = C := by
  apply le_antisymm
  · intro x hx
    obtain ⟨γ, hγ, hx⟩ := (mem_union_iff Γ plaq).mp hx
    exact ((mem_comps Γ plaq).mp hγ).1 hx
  · intro e he
    obtain ⟨σ, -, hσ⟩ := exists_potential hconn r C hC
    have hsub : reach plaq C e ⊆ C := fun x hx => ((mem_reach plaq).mp hx).1
    obtain ⟨τ, -, hτ⟩ := closed_piece_is_cut hconn r plaq hplaq hgen hσ hsub
      (closed_plaq plaq (reach_closed plaq e))
    have hcont : IsContour Γ plaq (reach plaq C e) :=
      ⟨⟨e, (mem_reach plaq).mpr ⟨he, SimpleGraph.Reachable.refl e⟩⟩, hsub.trans hCE,
        ⟨e, reach_animal plaq he⟩, cut_even hτ⟩
    let γ : Contour Γ plaq := ⟨reach plaq C e, hcont⟩
    exact (mem_union_iff Γ plaq).mpr ⟨γ, (mem_comps Γ plaq).mpr ⟨hsub, reach_closed plaq e⟩,
      (mem_reach plaq).mpr ⟨he, SimpleGraph.Reachable.refl e⟩⟩

/-! ### Even sets are closed under disjoint unions -/

omit [Fintype X] in
lemma countP_union {l : List (Sym2 X)} {A B : Finset (Sym2 X)} (hAB : Disjoint A B) :
    l.countP (fun e => decide (e ∈ A ∪ B)) =
      l.countP (fun e => decide (e ∈ A)) + l.countP (fun e => decide (e ∈ B)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons, mem_union, Bool.decide_or] at ih ⊢
    rw [ih]
    by_cases ha : a ∈ A <;> by_cases hb : a ∈ B
    · exact absurd hb (Finset.disjoint_left.mp hAB ha)
    all_goals simp [ha, hb]; try omega

omit [Fintype X] [DecidableRel Γ.Adj] in
lemma even_union {A B : Finset (Sym2 X)} (hAB : Disjoint A B) (hA : EvenCycles Γ A)
    (hB : EvenCycles Γ B) : EvenCycles Γ (A ∪ B) := by
  intro v p
  unfold hits
  rw [countP_union hAB]
  exact (hA v p).add (hB v p)

lemma union_even {I : Finset (Contour Γ plaq)}
    (hI : PolymerConvergence.Independent (Incompat Γ plaq) I) :
    EvenCycles Γ (union Γ plaq I) ∧ union Γ plaq I ⊆ Γ.edgeFinset := by
  induction I using Finset.induction_on with
  | empty =>
    refine ⟨fun v p => ?_, by simp [union]⟩
    simp [union, hits]
  | @insert a I ha ih =>
    have hI' : PolymerConvergence.Independent (Incompat Γ plaq) I :=
      fun x hx y hy hxy => hI x (mem_insert_of_mem hx) y (mem_insert_of_mem hy) hxy
    obtain ⟨h1, h2⟩ := ih hI'
    have hdisj : Disjoint a.1 (union Γ plaq I) := by
      rw [Finset.disjoint_left]
      intro e hea heI
      obtain ⟨b, hb, heb⟩ := (mem_union_iff Γ plaq).mp heI
      have hab : a ≠ b := fun h => ha (h ▸ hb)
      exact hI a (mem_insert_self a I) b (mem_insert_of_mem hb) hab
        (Or.inl (Finset.not_disjoint_iff.mpr ⟨e, hea, heb⟩))
    have hu : union Γ plaq (insert a I) = a.1 ∪ union Γ plaq I := by simp [union]
    rw [hu]
    exact ⟨even_union Γ hdisj a.2.2.2.2 h1, union_subset a.2.2.1 h2⟩

/-! ### The identity -/

open Classical in
/-- **The PM history sum is a contour gas.** -/
theorem contour_gas_eq (hconn : Γ.Connected) (r : X) (hgen : PlaquettesGenerate Γ plaq)
    (hplaq : ∀ P ∈ plaq, IsPlaquette Γ P) (q : ℝ) :
    (∑ C ∈ Γ.edgeFinset.powerset.filter (fun C => EvenCycles Γ C), q ^ C.card) =
      PolymerConvergence.Z (Incompat Γ plaq) (fun γ => q ^ γ.1.card) univ := by
  classical
  unfold PolymerConvergence.Z
  symm
  apply Finset.sum_nbij' (union Γ plaq) (comps Γ plaq)
  · intro I hI
    simp only [mem_filter, mem_powerset] at hI ⊢
    obtain ⟨h1, h2⟩ := union_even Γ plaq hI.2
    exact ⟨h2, h1⟩
  · intro C hC
    simp only [mem_filter, mem_powerset] at hC ⊢
    exact ⟨subset_univ _, comps_independent Γ plaq C⟩
  · intro I hI
    simp only [mem_filter] at hI
    exact comps_union Γ plaq hI.2
  · intro C hC
    simp only [mem_filter, mem_powerset] at hC
    exact union_comps Γ plaq hconn r hgen hplaq hC.1 hC.2
  · intro I hI
    simp only [mem_filter] at hI
    rw [prod_pow_eq_pow_sum, union, card_biUnion]
    intro a ha b hb hab
    by_contra hd
    exact hI.2 a ha b hb hab (Or.inl hd)

end PMAction.MassGap.ContourGas
