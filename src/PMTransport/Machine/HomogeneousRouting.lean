import PMTransport.Machine.RecordSupply

/-!
# Why the record routing is a lattice translation

`RecordSupply.lattice_forever` takes the backward routing to be a translation along a nonzero
vector. This module derives that from two properties of the update.

* **Homogeneity.** The routing rule is the same at every site, which means it commutes with every
  lattice translation. `equivariant_is_translation`: such a permutation of `ℤᵈ` is the translation
  by `e 0`. No other routing is homogeneous.
* **The routing moves records.** `fixed_routing_returns`: if the routing leaves the coupling site
  where it is, the orbit is a ring of length one. The disturbance entering at tick `1` is back on
  the live output at tick `2` (`RecordSupply.ring_returns`), so this pair cannot
  supply uninterrupted repair.
  A routing that supplies the site has `e o ≠ o`. For a translation, that means the vector is
  nonzero.
* `homogeneous_forever`: a homogeneous routing that moves the coupling site gives exact
  maintenance at every tick on `ℤᵈ`.
* `torus_returns`: on a finite periodic lattice `(ZMod N)ᵈ`, every translation returns after `N`
  steps, so the retained-route supply is finite (`ring_returns`). Exact maintenance
  forever by this route requires an open orbit.

Without homogeneity:

* `forever_iff_open`: exact maintenance forever against every live disturbance holds exactly
  when the coupling site's backward orbit never returns under the specified retained update.
* `finite_closes`, `forever_needs_infinite`: on a finite domain every permutation orbit closes.
  The exact arbitrary-disturbance restoration condition forces an infinite domain for this update.

The result assumes the same reversible stream routing for every visit. An update
with boundary disposal and a fresh supplied reference has different hypotheses.
Homogeneity characterizes the allowed translation routings.
-/

noncomputable section
namespace PMAction.HomogeneousRouting
open RecordSupply

/-- **A homogeneous routing is a translation.** -/
theorem equivariant_is_translation {d : ℕ} (e : Equiv.Perm (Fin d → ℤ))
    (hcomm : ∀ w x, e (x + w) = e x + w) : e = Equiv.addRight (e 0) := by
  ext x i
  have := hcomm x 0
  rw [zero_add] at this
  simp [this, add_comm]

/-- **A fixed routing never repairs.** If the coupling site is fixed by the routing, the live
value entering at tick `1` is back at the site's live output at tick `2`. -/
theorem fixed_routing_returns {X A : Type*} [DecidableEq X] (o : X) (e : Equiv.Perm X)
    (s : X → A × A) (hfix : e o = o) : (run o e 2 s o).1 = (s (e⁻¹ o)).1 :=
  ring_returns o e s 1 le_rfl (by simpa using hfix) (fun m hm h => by omega)

/-- **Homogeneous and moving gives exact maintenance forever.** -/
theorem homogeneous_forever {d : ℕ} (e : Equiv.Perm (Fin d → ℤ))
    (hcomm : ∀ w x, e (x + w) = e x + w) (o : Fin d → ℤ) (hmove : e o ≠ o) {A : Type*}
    (s : (Fin d → ℤ) → A × A) (r : A) (hrec : ∀ x, (s x).2 = r) (t : ℕ) (ht : 1 ≤ t) :
    (run o e t s o).1 = r := by
  have he := equivariant_is_translation e hcomm
  have hv : e 0 ≠ 0 := by
    intro h0
    apply hmove
    rw [he, h0]
    simp
  rw [he]
  exact lattice_forever (e 0) hv o s r hrec t ht

/-- **A finite periodic lattice returns.** Every translation of `(ZMod N)ᵈ` closes after `N`
steps. -/
theorem torus_returns {d N : ℕ} (v : Fin d → ZMod N) (o : Fin d → ZMod N) :
    ((Equiv.addRight v) ^ N) o = o := by
  have h : ∀ n : ℕ, ((Equiv.addRight v) ^ n) o = o + n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ_apply, ih]; simp [add_smul, add_assoc]
  rw [h]
  funext i
  simp

/-! ## Openness for the retained update

Homogeneity is not needed. Exact maintenance forever, for every live disturbance, holds exactly
when the backward orbit of the coupling site never returns. A finite substrate always has a
returning orbit. -/

/-- **On a finite substrate every orbit closes.** -/
theorem finite_closes {X : Type*} [Finite X] (e : Equiv.Perm X) (o : X) :
    ∃ N, 1 ≤ N ∧ (e ^ N) o = o ∧ ∀ m, 1 ≤ m → m < N → (e ^ m) o ≠ o := by
  classical
  have hex : ∃ N, 1 ≤ N ∧ (e ^ N) o = o :=
    ⟨orderOf e, (isOfFinOrder_of_finite e).orderOf_pos, by rw [pow_orderOf_eq_one]; rfl⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun m hm hlt h => ?_⟩
  exact Nat.find_min hex hlt ⟨hm, h⟩

/-- **Exact maintenance forever is an open orbit.** For a value type with two distinct values,
the site holds the reference at every tick, for every state whose records are at the reference
(whatever the live stream carries), exactly when the backward orbit never returns. -/
theorem forever_iff_open {X A : Type*} [DecidableEq X] (o : X) (e : Equiv.Perm X) (r d : A)
    (hd : d ≠ r) :
    (∀ s : X → A × A, (∀ x, (s x).2 = r) → ∀ t, 1 ≤ t → (run o e t s o).1 = r) ↔
      ∀ m, 1 ≤ m → (e ^ m) o ≠ o := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have hex : ∃ N, 1 ≤ N ∧ (e ^ N) o = o := hc
    classical
    let N := Nat.find hex
    have hN := Nat.find_spec hex
    have hmin : ∀ m, 1 ≤ m → m < N → (e ^ m) o ≠ o :=
      fun m hm hlt hmo => Nat.find_min hex hlt ⟨hm, hmo⟩
    let s : X → A × A := fun _ => (d, r)
    have hret := ring_returns o e s N hN.1 hN.2 hmin
    have := h s (fun _ => rfl) (N + 1) (by omega)
    rw [hret] at this
    exact hd this
  · intro hopen s hrec t ht
    exact open_orbit_forever o e s r hrec hopen t ht

/-- Exact arbitrary-disturbance restoration forever by the specified retained update forces an infinite domain. -/
theorem forever_needs_infinite {X A : Type*} [DecidableEq X] (o : X) (e : Equiv.Perm X) (r d : A)
    (hd : d ≠ r)
    (h : ∀ s : X → A × A, (∀ x, (s x).2 = r) → ∀ t, 1 ≤ t → (run o e t s o).1 = r) :
    Infinite X := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  obtain ⟨N, hN, hc, -⟩ := finite_closes e o
  exact (forever_iff_open o e r d hd).mp h N hN hc

end PMAction.HomogeneousRouting
