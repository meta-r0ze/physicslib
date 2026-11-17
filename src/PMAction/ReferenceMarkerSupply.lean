import PMAction.ReferenceMarkerExport

/-!
# Repeated native class writing with transported blank supply

Each cycle applies the existing blank-to-class-marker root word at one site,
then the complete marker export circuit. The whole cycle is a permutation of
actual carrier labels and sites; no field is overwritten with a prepared value.
A supplied sequence of class inputs controls the writes. The path theorem holds
for every such sequence, and pointwise for coherently retained history labels.
It does not select that sequence or supply its physical control.

If neither the blank nor tag lookup routes return to the writing site during
T cycles, prepared incoming modes in the initial field give a clean local
amplitude port throughout that horizon. No per-cycle clean-record assumption
is made. Nonzero lattice translations supply open routes, using `RecordSupply`.
The incoming field, its preparation/normalization, bank allocation, prices and
clock are still supplied. Infinite configuration fields here are not claimed
to be normalized one-particle states or independently prepared site registers.
-/
noncomputable section
namespace PMAction.ReferenceMarkerSupply
open Matrix VectorEvenFrame ReferenceMarkerExport

section Dynamics
variable {X : Type*} [DecidableEq X]

/-- The existing class-marker root word is applied at the write site only. -/
def writeAt (o : X) (c : Fin 3) : Equiv.Perm (X × C) where
  toFun p := (p.1, if p.1 = o then axisSwap c.succ p.2 else p.2)
  invFun p := (p.1, if p.1 = o then axisSwap c.succ p.2 else p.2)
  left_inv p := by
    rcases p with ⟨x,v⟩
    by_cases h : x = o <;> simp [h]
    exact axis_swap_twice c.succ v
  right_inv p := by
    rcases p with ⟨x,v⟩
    by_cases h : x = o <;> simp [h]
    exact axis_swap_twice c.succ v

theorem write_is_root_word (o : X) (c : Fin 3) (v : C) :
    (writeAt o c (o,v)).2 = ((word c.succ).map (CarrierWeyl.simple 0)).prod v := by
  simpa [writeAt] using (root_word c.succ v).symm

/-- A clean local amplitude port is written to the same class marker as `ReferenceRootRecord`. -/
theorem write_blank (o : X) (c : Fin 3) (ψ : X × C → ℂ) (a : ℂ)
    (hψ : ∀ v, ψ (o,v) = a * marker 0 v) (v : C) :
    ψ (writeAt o c (o,v)) = a * marker c.succ v := by
  have hw : writeAt o c (o,v) = (o, axisSwap c.succ v) := by simp [writeAt]
  rw [hw, hψ]
  have hm := congrFun (write_marker c.succ) v
  rw [permMatrix_mulVec] at hm
  exact congrArg (fun z => a*z) hm

/-- Pullback lookup: forward amplitude evolution writes first, then exports. -/
def cycle (o : X) (e : Equiv.Perm X) (c : Fin 3) : Equiv.Perm (X × C) :=
  (exportCycle e).trans (writeAt o c)

/-- The actual carrier-dependent lookup route between writes. -/
def route (e : Equiv.Perm X) (v : C) : Equiv.Perm X := e ^ exportLane v

lemma cycle_away (o : X) (e : Equiv.Perm X) (c : Fin 3) (x : X) (v : C)
    (h : route e v x ≠ o) : cycle o e c (x,v) = (route e v x,v) := by
  change (e ^ exportLane v) x ≠ o at h
  rw [cycle, export_eq]
  simp [Equiv.trans_apply, routed, writeAt, route, h]

/-- Successive native updates on a supplied initial amplitude/configuration field. -/
def run (o : X) (e : Equiv.Perm X) (classes : ℕ → Fin 3) :
    ℕ → (X × C → ℂ) → X × C → ℂ
  | 0, ψ => ψ
  | t+1, ψ => fun p => run o e classes t ψ (cycle o e (classes t) p)

/-- Reversible lookup for the entire supplied history, not a succession of resets. -/
def history (o : X) (e : Equiv.Perm X) (classes : ℕ → Fin 3) : ℕ → Equiv.Perm (X × C)
  | 0 => Equiv.refl _
  | t+1 => (cycle o e (classes t)).trans (history o e classes t)

theorem run_history (o : X) (e : Equiv.Perm X) (classes : ℕ → Fin 3)
    (t : ℕ) (ψ : X × C → ℂ) (p : X × C) :
    run o e classes t ψ p = ψ (history o e classes t p) := by
  induction t generalizing p with
  | zero => rfl
  | succ t ih => exact ih _

/-- Histories can themselves be retained coherently; their labels are not measured here. -/
def controlledHistory {H : Type*} (o : X) (e : Equiv.Perm X)
    (classes : H → ℕ → Fin 3) (t : ℕ) : Equiv.Perm (H × (X × C)) where
  toFun p := (p.1, history o e (classes p.1) t p.2)
  invFun p := (p.1, (history o e (classes p.1) t).symm p.2)
  left_inv p := Prod.ext rfl ((history o e (classes p.1) t).symm_apply_apply p.2)
  right_inv p := Prod.ext rfl ((history o e (classes p.1) t).apply_symm_apply p.2)

/-- Until a path reaches the write site, no write affects that incoming mode. -/
theorem incoming_path (o : X) (e : Equiv.Perm X) (classes : ℕ → Fin 3)
    (t : ℕ) (ψ : X × C → ℂ) (x : X) (v : C)
    (hclear : ∀ m, 1 ≤ m → m ≤ t → ((route e v)^m) x ≠ o) :
    run o e classes t ψ (x,v) = ψ (((route e v)^t) x,v) := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    have hfirst : route e v x ≠ o := by
      simpa using hclear 1 (by omega) (by omega)
    have htail : ∀ m, 1 ≤ m → m ≤ t → ((route e v)^m) (route e v x) ≠ o := by
      intro m hm hmt
      have hh := hclear (m+1) (by omega) (by omega)
      simpa only [pow_succ, Equiv.Perm.mul_apply] using hh
    change run o e classes t ψ (cycle o e (classes t) (x,v)) = _
    rw [cycle_away o e (classes t) x v hfirst, ih (route e v x) htail]
    rw [pow_succ, Equiv.Perm.mul_apply]

/-- Only the initial incoming modes on the specified finite horizon need preparation. -/
theorem finite_supply (o : X) (e : Equiv.Perm X) (classes : ℕ → Fin 3)
    (T : ℕ) (ψ : X × C → ℂ) (a : ℂ)
    (hsource : ∀ v m, m ≤ T → ψ (((route e v)^m) o,v) = a * marker 0 v)
    (hclear : ∀ v m, 1 ≤ m → m ≤ T → ((route e v)^m) o ≠ o)
    (t : ℕ) (ht : t ≤ T) (v : C) :
    run o e classes t ψ (o,v) = a * marker 0 v := by
  rw [incoming_path o e classes t ψ o v (fun m hm hmt => hclear v m hm (by omega))]
  exact hsource v t ht

end Dynamics

/-! ## Open routes from the existing lattice result -/
section OpenRoutes
variable {X : Type*}

def NoReturn (e : Equiv.Perm X) (o : X) : Prop :=
  ∀ m : ℕ, 0 < m → (e^m) o ≠ o

theorem noReturn_inv (e : Equiv.Perm X) (o : X) (h : NoReturn e o) : NoReturn e⁻¹ o := by
  intro m hm he
  apply h m hm
  have hc : (e^m) (((e⁻¹)^m) o) = o := by
    rw [_root_.inv_pow]
    exact (e^m).apply_symm_apply o
  have hh := congrArg (fun x => (e^m) x) he
  exact hh.symm.trans hc

theorem noReturn_pow (e : Equiv.Perm X) (o : X) (h : NoReturn e o)
    (k : ℕ) (hk : 0 < k) : NoReturn (e^k) o := by
  intro m hm
  rw [← _root_.pow_mul]
  exact h (k*m) (Nat.mul_pos hk hm)

/-- Open neighbour routing makes both the tag and the three-step blank route open. -/
theorem lane_open (e : Equiv.Perm X) (o : X) (h : NoReturn e o) (v : C) :
    NoReturn (route e v) o := by
  unfold route exportLane
  split_ifs
  · have hi := noReturn_pow e⁻¹ o (noReturn_inv e o h) 3 (by decide)
    simpa [NoReturn, inv_pow] using hi
  · simpa using h

/-- Before the first return, every donor site is distinct, including the initial local site. -/
theorem donors_injective (r : Equiv.Perm X) (o : X) (T : ℕ)
    (hclear : ∀ m, 1 ≤ m → m ≤ T → (r^m) o ≠ o) :
    Function.Injective (fun n : Fin (T+1) => (r^n.val) o) := by
  have different : ∀ i j : ℕ, i < j → j ≤ T → (r^i) o ≠ (r^j) o := by
    intro i j hij hj he
    have hreturn : (r^(j-i)) o = o := by
      apply (r^i).injective
      calc
        (r^i) ((r^(j-i)) o) = (r^j) o := by
          rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_of_le (by omega : i ≤ j)]
        _ = (r^i) o := he.symm
    exact hclear (j-i) (by omega) (by omega) hreturn
  intro i j he
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact different i.val j.val hij (by omega) he
  · exact different j.val i.val hji (by omega) he.symm

/-- A horizon of T fresh arrivals requires at least T+1 distinct bank sites.
This is a bound for this routing/supply contract, not a universal memory optimum. -/
theorem finite_site_bound [Fintype X] (r : Equiv.Perm X) (o : X) (T : ℕ)
    (hclear : ∀ m, 1 ≤ m → m ≤ T → (r^m) o ≠ o) : T+1 ≤ Fintype.card X := by
  simpa using Fintype.card_le_of_injective _ (donors_injective r o T hclear)

end OpenRoutes

section Supply
variable {X : Type*} [DecidableEq X]

/-- Prepared incoming background plus open routing suffices for every finite cycle count.
The source is supplied once, not re-assumed clean after each write. -/
theorem open_supply (o : X) (e : Equiv.Perm X) (h : NoReturn e o)
    (classes : ℕ → Fin 3) (ψ : X × C → ℂ) (a : ℂ)
    (hsource : ∀ x v, ψ (x,v) = a * marker 0 v) (t : ℕ) (v : C) :
    run o e classes t ψ (o,v) = a * marker 0 v :=
  finite_supply o e classes t ψ a (fun v m _ => hsource _ v)
    (fun v m hm _ => lane_open e o h v m (by omega)) t le_rfl v

/-- Nonzero lattice translations meet the no-return condition, using the existing theorem.
The uniform incoming amplitude field remains an explicit source contract. -/
theorem lattice_supply {d : ℕ} (w : Fin d → ℤ) (hw : w ≠ 0) (o : Fin d → ℤ)
    (classes : ℕ → Fin 3) (ψ : ((Fin d → ℤ) × C) → ℂ) (a : ℂ)
    (hsource : ∀ x v, ψ (x,v) = a * marker 0 v) (t : ℕ) (v : C) :
    run o (Equiv.addRight w) classes t ψ (o,v) = a * marker 0 v := by
  apply open_supply o (Equiv.addRight w) _ classes ψ a hsource t v
  intro m hm
  exact RecordSupply.translation_open w hw o m (by omega)

/-- A coherent history-index amplitude has the same clean local mode on every history row. -/
theorem coherent_local {H : Type*} (o : X) (e : Equiv.Perm X) (h : NoReturn e o)
    (classes : H → ℕ → Fin 3) (ψ : H × (X × C) → ℂ) (A : H → ℂ)
    (hsource : ∀ h x v, ψ (h,(x,v)) = A h * marker 0 v)
    (t : ℕ) (h₀ : H) (v : C) :
    ψ (controlledHistory o e classes t (h₀,(o,v))) = A h₀ * marker 0 v := by
  change ψ (h₀, history o e (classes h₀) t (o,v)) = _
  rw [← run_history o e (classes h₀) t (fun p => ψ (h₀,p)) (o,v)]
  exact open_supply o e h (classes h₀) (fun p => ψ (h₀,p)) (A h₀) (hsource h₀) t v

/-- The blank marker has unit population in the existing isometric even frame. -/
theorem blank_norm : CommonResponse.nsq (marker 0) = 1 := by
  unfold CommonResponse.nsq marker
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, VectorEvenFrame.isometry, one_mulVec]
  simp [dotProduct, Pi.single_apply]

/-- Initial population at the blank donor sites, including the initially local blank.
`donors_injective` makes these distinct under the no-return horizon contract. -/
def incomingPopulation (e : Equiv.Perm X) (o : X) (ψ : X × C → ℂ) (T : ℕ) : ℝ :=
  ∑ x ∈ (Finset.univ.image (fun n : Fin (T+1) => ((e ^ (-3 : ℤ)) ^ n.val) o)),
    CommonResponse.nsq (fun v => ψ (x,v))

/-- Prepared incoming blanks carry population; supply is not a free reset. -/
theorem source_population (e : Equiv.Perm X) (o : X) (ψ : X × C → ℂ) (a : ℂ)
    (hsource : ∀ x v, ψ (x,v) = a * marker 0 v) (T : ℕ)
    (hclear : ∀ m, 1 ≤ m → m ≤ T → ((e ^ (-3 : ℤ))^m) o ≠ o) :
    incomingPopulation e o ψ T = (T+1) * Complex.normSq a := by
  have hp : ∀ x, CommonResponse.nsq (fun v => ψ (x,v)) = Complex.normSq a := by
    intro x
    have he : (fun v => ψ (x,v)) = a • marker 0 := funext (hsource x)
    rw [he, ControllerHamiltonian.nsq_smul, blank_norm, mul_one]
  unfold incomingPopulation
  rw [Finset.sum_image]
  · simp [hp]
  · intro i hi j hj he
    exact donors_injective (e ^ (-3 : ℤ)) o T hclear he

/-- A matching nonzero source over arbitrarily long open horizons has unbounded
incoming population. No statement of preparation or creation of this source is made. -/
theorem source_unbounded (e : Equiv.Perm X) (o : X) (h : NoReturn e o)
    (ψ : X × C → ℂ) (a : ℂ)
    (ha : a ≠ 0) (hsource : ∀ x v, ψ (x,v) = a * marker 0 v) (B : ℝ) :
    ∃ T, B < incomingPopulation e o ψ T := by
  have hblank : NoReturn (e ^ (-3 : ℤ)) o := by
    simpa [NoReturn, inv_pow] using noReturn_pow e⁻¹ o (noReturn_inv e o h) 3 (by decide)
  have hp : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha
  obtain ⟨T,hT⟩ := exists_nat_gt (B / Complex.normSq a)
  have hh := (div_lt_iff₀ hp).mp hT
  refine ⟨T, ?_⟩
  rw [source_population e o ψ a hsource T (fun m hm _ => hblank m (by omega))]
  nlinarith

end Supply

section FiniteMatrices
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Finite histories are the amplitude lifts of the actual native label permutations. -/
theorem run_matrix (o : X) (e : Equiv.Perm X) (classes : ℕ → Fin 3)
    (t : ℕ) (ψ : X × C → ℂ) :
    run o e classes t ψ = (history o e classes t).permMatrix ℂ *ᵥ ψ := by
  rw [permMatrix_mulVec]
  funext p
  exact run_history o e classes t ψ p

theorem history_unitary (o : X) (e : Equiv.Perm X) (classes : ℕ → Fin 3) (t : ℕ) :
    (history o e classes t).permMatrix ℂ ∈ unitary (Matrix (X × C) (X × C) ℂ) :=
  CarrierResponse.perm_unitary _

/-- Retaining the finite history-control labels preserves the whole coherent state. -/
theorem controlled_unitary {H : Type*} [Fintype H] [DecidableEq H]
    (o : X) (e : Equiv.Perm X) (classes : H → ℕ → Fin 3) (t : ℕ) :
    (controlledHistory o e classes t).permMatrix ℂ ∈
      unitary (Matrix (H × (X × C)) (H × (X × C)) ℂ) :=
  CarrierResponse.perm_unitary _

end FiniteMatrices
end PMAction.ReferenceMarkerSupply
