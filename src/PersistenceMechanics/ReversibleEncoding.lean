import Mathlib.Tactic

/-!
# Nested Rule 2: Reversible Encoding

The encoding rule of Nested Persistence (`PM-3-Nested/paper/2_nested_persistence.tex`,
"Reversible Encoding"). A coarse description `q : X → Q` may merge states that remain
distinguishable. Conservation then requires metadata `m : X → M` that separates every pair
`q` merges: the combined encoding `E x = (q x, m x)` must be injective.

* `encode_injective_iff`: `E` is injective exactly when `m` separates every fibre of `q`.
* `fiber_card_le`: then every fibre of `q` has at most `|M|` elements.
* `card_le_mul`: and `|X| ≤ |Q| · |M|`.
* `relational_injective`: for group-valued data on sites, the reference value together with
  the differences from it is a reversible encoding.
* `differences_eq_iff`: the differences alone identify two configurations exactly when they
  differ by a constant. Dropping the reference value merges precisely the global shifts.

This is an information-capacity statement. It does not price the retained data or set its
maintenance frequency. No substrate is assumed here.
-/

namespace PersistenceMechanics.ReversibleEncoding

variable {X Q M : Type*}

/-- The combined encoding: coarse description plus metadata. -/
def encode (q : X → Q) (m : X → M) (x : X) : Q × M := (q x, m x)

/-- **Reversibility criterion.** The encoding is injective exactly when the metadata separates
every pair of states the coarse description merges. -/
theorem encode_injective_iff (q : X → Q) (m : X → M) :
    Function.Injective (encode q m) ↔ ∀ x y, q x = q y → m x = m y → x = y := by
  constructor
  · intro h x y hq hm
    exact h (Prod.ext hq hm)
  · intro h x y hxy
    exact h x y (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)

/-- **Fibre bound.** Each fibre of the coarse description has at most `|M|` states. -/
theorem fiber_card_le [Fintype X] [Fintype M] [DecidableEq Q] (q : X → Q) (m : X → M)
    (h : Function.Injective (encode q m)) (a : Q) :
    (Finset.univ.filter fun x => q x = a).card ≤ Fintype.card M := by
  classical
  rw [← Finset.card_univ]
  refine Finset.card_le_card_of_injOn m (by simp) ?_
  intro x hx y hy hxy
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  exact h (Prod.ext (hx.trans hy.symm) hxy)

/-- **Total bound.** `|X| ≤ |Q| · |M|`. -/
theorem card_le_mul [Fintype X] [Fintype Q] [Fintype M] (q : X → Q) (m : X → M)
    (h : Function.Injective (encode q m)) :
    Fintype.card X ≤ Fintype.card Q * Fintype.card M := by
  have := Fintype.card_le_of_injective (encode q m) h
  rwa [Fintype.card_prod] at this

/-- The relational encoding of site data: the reference value and the differences from it. -/
def relational {ι G : Type*} [AddGroup G] (o : ι) (x : ι → G) : G × (ι → G) :=
  (x o, fun i => x i - x o)

/-- **The relational encoding is reversible.** -/
theorem relational_injective {ι G : Type*} [AddGroup G] (o : ι) :
    Function.Injective (relational (G := G) o) := by
  intro x y h
  simp only [relational, Prod.mk.injEq] at h
  obtain ⟨h0, h1⟩ := h
  funext i
  have hi : x i - x o = y i - y o := congrFun h1 i
  rw [h0] at hi
  exact sub_left_injective hi

/-- **Dropping the reference merges exactly the global shifts.** -/
theorem differences_eq_iff {ι G : Type*} [AddCommGroup G] (o : ι) (x y : ι → G) :
    (fun i => x i - x o) = (fun i => y i - y o) ↔ ∃ c : G, ∀ i, x i = y i + c := by
  constructor
  · intro h
    refine ⟨x o - y o, fun i => ?_⟩
    have hi : x i - x o = y i - y o := congrFun h i
    calc x i = (x i - x o) + x o := by abel
      _ = (y i - y o) + x o := by rw [hi]
      _ = y i + (x o - y o) := by abel
  · rintro ⟨c, hc⟩
    funext i
    rw [hc i, hc o]
    abel

/-- Reversibility is equivalent to an actual partial decoder on label/metadata
pairs. Impossible codes can return `none`; every encoded state is recovered. -/
theorem encode_injective_iff_decoder (coarse : X → Q) (metadata : X → M) :
    Function.Injective (encode coarse metadata) ↔
      ∃ decode : Q × M → Option X,
        ∀ x, decode (encode coarse metadata x) = some x := by
  classical
  constructor
  · intro h
    refine ⟨fun code => if hc : ∃ x, encode coarse metadata x = code
      then some hc.choose else none, ?_⟩
    intro x
    dsimp only
    split_ifs with hc
    · exact congrArg some (h hc.choose_spec)
    · exact (hc ⟨x, rfl⟩).elim
  · rintro ⟨decode, hd⟩ x y he
    have h := congrArg decode he
    rw [hd, hd] at h
    exact Option.some.inj h


/-- If a coarse label has k independent possible remainders, storing fewer
than k metadata states cannot preserve all those states. -/
theorem remainder_capacity (k : ℕ) [Fintype M] (q : Q)
    (metadata : Q × Fin k → M)
    (h : Function.Injective (encode Prod.fst metadata)) : k ≤ Fintype.card M := by
  have hinj : Function.Injective (fun i : Fin k => metadata (q, i)) := by
    intro i j he
    have hpair := (encode_injective_iff Prod.fst metadata).mp h (q, i) (q, j) rfl he
    exact congrArg Prod.snd hpair
  simpa using Fintype.card_le_of_injective _ hinj

/-- Renaming metadata preserves the information. A physical interpretation
of that metadata requires additional structure beyond reversibility. -/
theorem metadata_relabel {M' : Type*} (coarse : X → Q)
    (metadata : X → M) (e : M ≃ M')
    (h : Function.Injective (encode coarse metadata)) :
    Function.Injective (encode coarse (e ∘ metadata)) := by
  apply (encode_injective_iff _ _).mpr
  intro x y hc hm
  exact (encode_injective_iff _ _).mp h x y hc (e.injective hm)


/-- Subtype and Finset presentations count the same coarse fibre. -/
theorem fiber_card_eq [Fintype X] [DecidableEq Q] (q : X → Q) (a : Q) :
    Nat.card {x : X // q x = a} = (Finset.univ.filter fun x => q x = a).card := by
  classical
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Nonself coordinates are a total chart: omit the redundant zero self-difference.
Restriction of `relational` gives this chart; its inverse restores the reference. -/
def relativeEquiv {I A : Type*} [AddGroup A] [DecidableEq I] (o : I) :
    (I → A) ≃ A × ({i : I // i ≠ o} → A) where
  toFun x := (x o, fun i => x i-x o)
  invFun p i := if h : i = o then p.1 else p.2 ⟨i,h⟩+p.1
  left_inv x := by
    funext i
    by_cases hi : i = o <;> simp [hi]
  right_inv p := by
    rcases p with ⟨r,d⟩
    apply Prod.ext
    · simp
    · funext i; simp [i.property]

theorem relative_restrict {I A : Type*} [AddGroup A] [DecidableEq I] (o : I) (x : I → A) :
    relativeEquiv o x = ((relational o x).1, fun i : {i : I // i ≠ o} => (relational o x).2 i) := rfl

theorem differences_without_reference_not_injective {I A : Type*} [AddGroup A]
    [Nontrivial A] (o : I) :
    ¬ Function.Injective (fun x : I → A => fun i : {i : I // i ≠ o} => x i-x o) := by
  intro h
  obtain ⟨a,b,hab⟩ := exists_pair_ne A
  have he : (fun _ : I => a) = (fun _ : I => b) := h (by funext i; simp)
  exact hab (congrFun he o)

end PersistenceMechanics.ReversibleEncoding
