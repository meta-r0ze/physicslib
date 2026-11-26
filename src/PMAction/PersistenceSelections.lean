import PMAction.ReferenceNodeBoundary
import PMAction.NativeWallOffset

/-!
# Three selections by the persistence pillars

Three PMAction choices were left between admitted alternatives. Each is settled here by a pillar
already used elsewhere in the library, not by the data.

**1. The restoring node's spectator ports are free (Toll / Economy).**
`ReferenceNodeBoundary`: a free spectator port gives the two-leg series response; a port held by the
host at a fixed potential adds a load `g > 0`, and the response equals the series value exactly
when `g = 0` (`series_iff_no_load`). Holding a port is maintenance: it moves current through the
clamp, which has a positive price for any nonzero load, and nothing is paid for a port no protocol
uses. `free_boundary_selected`: the unique cheapest boundary is zero load, and then the coupling is
the series value; with equal legs `α` (Closure) it is `α/2` (`free_boundary_equal`). This fixes
`ReferenceNode`'s `k/K = α/2`.

**2. The other wall's flip is the coherent event (Economy, squared-energy price).**
`NativeWallOffset.generator_split`: the lazy `β` event is the flip part plus the offset
`c · P_O` (`c = gap/2 > 0`) on its wall; the coherent paired-root and class-blind programs
(`PairedRootFlip`, `ClassBlindFlip`) realize the same net `β` rotation with no offset. Pricing a
state by the squared energy of a term, as for the reference background and the other wall's
resonance (`OtherWallStationary.energyPrice`) and the even complement (`EvenComplement`),
`offset_price_pos`: the offset has positive price on every state with weight on its wall, while the
coherent realization has none. So the coherent event is the cheaper realization of the same flip,
and the light masses are the singular values of the wire's mass (`DetunedWire`, `ReferenceWallFactorization`),
not their squares (`WallOffset`).

**3. The reference occupies one class (Margin, then Economy).**
On the reference's wall the native exchanges are class-blind (`CarrierAdmittance.uniform_hop`), and
`ReferenceClassHop` shows a reference stays a zero mode only if the exchanges out of its support
vanish there. A stationary reference spread over two classes exists (an antisymmetric combination,
whose two class components cancel in the exchange) but relies on a fixed relative phase between
classes. `robust_iff`: a reference stays annihilated by the exchange under every independent phase
of its class components exactly when every exchange column on its support vanishes separately. So a
reference that survives class-dependent phases (Margin) needs every exchange touching its support
suppressed, that is routed through the restoring node. `two_classes_touch_all`: with support on two
or more classes every exchange touches it, while one class leaves the opposite exchange direct
(`one_class_spares_one`). The cheapest robust reference (Economy: fewest exchanges through the
node) is therefore one class, which is `ReferenceClassHop`'s input.
-/

noncomputable section
namespace PMAction.PersistenceSelections
open Matrix

/-! ## 1. The restoring node's boundary -/

/-- **The free port is the unique cheapest boundary, and it gives the series response.** -/
theorem free_boundary_selected (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (price : ℝ → ℝ)
    (h0 : price 0 = 0) (hpos : ∀ g, 0 < g → 0 < price g) :
    (∀ g, 0 ≤ g → price 0 ≤ price g) ∧ (∀ g, 0 ≤ g → price g = price 0 → g = 0) ∧
      ReferenceNodeBoundary.coupling a b 0 = ReferenceNodeBoundary.series a b := by
  refine ⟨fun g hg => ?_, fun g hg he => ?_, ?_⟩
  · rcases hg.eq_or_lt with h | h
    · rw [← h]
    · rw [h0]; exact (hpos g h).le
  · by_contra hne
    have := hpos g (lt_of_le_of_ne hg (Ne.symm hne))
    rw [he, h0] at this; exact lt_irrefl 0 this
  · exact (ReferenceNodeBoundary.series_iff_no_load a b 0 ha hb le_rfl).2 rfl

/-- With equal legs the selected boundary gives `α/2`. -/
theorem free_boundary_equal (α : ℝ) (hα : 0 < α) :
    ReferenceNodeBoundary.coupling α α 0 = α / 2 := by
  rw [(ReferenceNodeBoundary.series_iff_no_load α α 0 hα hα le_rfl).2 rfl]
  exact ReferenceNodeBoundary.equal_floating α hα

/-! ## 2. The flip event -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Squared-energy price of a term `O` on a state `ψ`. -/
def price (O : Matrix (n ⊕ n) (n ⊕ n) ℂ) (ψ : n ⊕ n → ℂ) : ℝ :=
  ∑ i, Complex.normSq ((O *ᵥ ψ) i)

/-- **The lazy event's wall offset has positive price on every state with weight on its wall.** -/
theorem offset_price_pos (c : ℂ) (hc : c ≠ 0) (ψ : n ⊕ n → ℂ) (hψ : ∃ i, ψ (Sum.inl i) ≠ 0) :
    0 < price (c • (NativeWallOffset.projector : Matrix (n ⊕ n) _ ℂ)) ψ := by
  obtain ⟨i, hi⟩ := hψ
  have hterm : 0 < Complex.normSq (((c • (NativeWallOffset.projector : Matrix (n ⊕ n) _ ℂ)) *ᵥ ψ)
      (Sum.inl i)) := by
    have : ((c • (NativeWallOffset.projector : Matrix (n ⊕ n) _ ℂ)) *ᵥ ψ) (Sum.inl i) =
        c * ψ (Sum.inl i) := by
      simp [NativeWallOffset.projector, smul_mulVec, fromBlocks_mulVec]
    rw [this]; exact Complex.normSq_pos.2 (mul_ne_zero hc hi)
  exact lt_of_lt_of_le hterm (Finset.single_le_sum (f := fun j =>
    Complex.normSq (((c • (NativeWallOffset.projector : Matrix (n ⊕ n) _ ℂ)) *ᵥ ψ) j))
    (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ _))

/-- The coherent realization carries no offset: zero price. -/
theorem no_offset_price (ψ : n ⊕ n → ℂ) :
    price ((0 : ℂ) • (NativeWallOffset.projector : Matrix (n ⊕ n) _ ℂ)) ψ = 0 := by
  simp [price]

/-! ## 3. The reference's class -/

/-- **Robust to independent class phases exactly when each exchange column on the support vanishes.** -/
theorem robust_iff (X : Matrix (Fin 3) (Fin 3) ℂ) (u : Fin 3 → ℂ) :
    (∀ φ : Fin 3 → ℂ, (∀ c, ‖φ c‖ = 1) → X *ᵥ (fun c => φ c * u c) = 0) ↔
      ∀ b c, u c ≠ 0 → X b c = 0 := by
  constructor
  · intro h b c hc
    have h1 := h (fun _ => 1) (by simp)
    have h2 := h (Function.update (fun _ => (1 : ℂ)) c (-1)) (by
      intro d; by_cases hd : d = c <;> simp [Function.update, hd])
    have hu' : (fun d => Function.update (fun _ => (1 : ℂ)) c (-1) d * u d) =
        (fun d => (1 : ℂ) * u d) - (2 : ℂ) • Pi.single c (u c) := by
      funext d
      by_cases hd : d = c
      · subst hd; simp; ring
      · simp [Function.update, hd]
    rw [hu', mulVec_sub, h1, zero_sub, mulVec_smul, neg_eq_zero, smul_eq_zero] at h2
    have h3 : X *ᵥ Pi.single c (u c) = 0 := h2.resolve_left (by norm_num)
    have key : X b c * u c = 0 := by
      have := congrFun h3 b
      simpa [mulVec_single] using this
    exact (mul_eq_zero.mp key).resolve_right hc
  · intro h φ _
    funext b
    simp only [mulVec, dotProduct, Pi.zero_apply]
    apply Finset.sum_eq_zero
    intro c _
    by_cases hc : u c = 0
    · simp [hc]
    · simp [h b c hc]

/-- **Support on two or more classes touches every exchange.** -/
theorem two_classes_touch_all : ∀ s : Finset (Fin 3), 2 ≤ s.card →
    ∀ b c : Fin 3, b ≠ c → b ∈ s ∨ c ∈ s := by
  decide

/-- **One class leaves exactly the opposite exchange untouched.** -/
theorem one_class_spares_one : ∀ r b c : Fin 3, b ≠ c →
    (b ∉ ({r} : Finset (Fin 3)) ∧ c ∉ ({r} : Finset (Fin 3)) ↔ b ≠ r ∧ c ≠ r) := by
  decide

end PMAction.PersistenceSelections
