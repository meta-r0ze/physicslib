import PMConstants.ReferenceRestoration
import PMConstants.SectorLinks

/-!
# The scalar link carries the reference's charge

`SectorLinks.forced_by_links` fixes the hypercharges from flux conservation, one unit-charge
inter-sector link and a neutral sterile channel, and `Hypercharge.neutrality_needed` shows the last
premise cannot be dropped. The selected reference supplies it.

**Neutrality from the reference.** The scalar is the regulator of the reference
(`ReferenceDirections`): the link that hops between sectors is the reference's own field. It is
colourless and a weak doublet, as the lepton-doublet type is; matching its unit hypercharge to the
reference type's up to conjugation means `|Y_L| = 1`.

* `neutral_from_reference`: with flux conservation, the unit link and `Y_L = -1` (the link is the
  reference's conjugate), the charges are the standard ones, so `Y_ν = 0`.
* `conjugate_or_same`: with `|Y_L| = 1`, one lepton singlet is neutral either way; the other sign
  only exchanges which singlet is called `e` and which `ν`.
* `unmatched_link_fails`: the family member that `neutrality_needed` exhibits has `Y_L = 0`, so its
  link does not carry the reference's charge.

**The sterile channel is the unique total singlet.**

* `sterile_singlet`: with these charges, every colour, weak and hypercharge generator fixes `ν_R`.
* `sterile_unique`: every other channel is moved by one of them.

**Exactness is load-bearing.** `asymptotic_trace_free`: a restorer that only returns displacements
asymptotically, `K = k·1` with `0 < k < 2`, has `(1 - K)^n → 0` but total gain `3k`, any value in
`(0, 6)`. Only exact (finite-time) restoration fixes the budget at `3`
(`ReferenceRestoration.finite_restore_trace`), and the measured `λ` requires `3`
(`ScalarBudget.budget_unique`).
-/

noncomputable section
namespace PMConstants.ReferenceLink
open PMConstants Matrix Hypercharge GeneratorNormalization PacketTraceForm ReferenceStabilizer

theorem neutral_from_reference (Y : Charges) (hf : Flux Y) (hl : SectorLinks.OneLink Y 1)
    (hr : Y.l = -1) : Y = standard ∧ Y.n = 0 := by
  have hy := (SectorLinks.links_iff_yukawa Y 1).mp hl
  have hn : Y.n = 0 := by have := hy.2.2.2; linarith
  exact ⟨charges_forced Y hf hy hn, hn⟩

theorem conjugate_or_same (Y : Charges) (hl : SectorLinks.OneLink Y 1)
    (hr : Y.l = -1 ∨ Y.l = 1) : Y.n = 0 ∨ Y.e = 0 := by
  have hy := (SectorLinks.links_iff_yukawa Y 1).mp hl
  rcases hr with h | h
  · left; have := hy.2.2.2; linarith
  · right; have := hy.2.2.1; linarith

theorem unmatched_link_fails : (family 0 1).l = 0 := by norm_num [family]

/-- The right-handed sterile carrier. -/
def nuR : PacketGaugeActions.Channels := .inr (.inr (.inr 0))

theorem sterile_singlet (A : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 3) (Fin 3) ℂ) :
    Fixes (weakGen A) nuR ∧ Fixes (colourGen B) nuR ∧ Fixes hyperGen nuR := by
  refine ⟨?_, ?_, ?_⟩ <;> intro c <;> rcases c with q | q | s | s <;>
    simp [weakGen, colourGen, hyperGen, PacketGaugeActions.charge, PacketGaugeActions.block, nuR]
  fin_cases s <;> simp

lemma fixes_diag {G : PacketGaugeActions.M} {c} (h : Fixes G c) : G c c = 0 := h c

theorem sterile_unique (c : PacketGaugeActions.Channels)
    (h : ∀ (A : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 3) (Fin 3) ℂ),
      Fixes (weakGen A) c ∧ Fixes (colourGen B) c ∧ Fixes hyperGen c) : c = nuR := by
  obtain ⟨-, hc, -⟩ := h 0 (Matrix.of fun _ _ => 1)
  obtain ⟨hw, -, hy⟩ := h (Matrix.of fun _ _ => 1) 0
  have hc' := fixes_diag hc
  have hw' := fixes_diag hw
  have hy' := fixes_diag hy
  rcases c with q | q | s | s
  · simp [colourGen, PacketGaugeActions.block, Matrix.kroneckerMap_apply] at hc'
  · simp [colourGen, PacketGaugeActions.block, Matrix.kroneckerMap_apply] at hc'
  · simp [weakGen, PacketGaugeActions.block] at hw'
  · fin_cases s
    · rfl
    · norm_num [hyperGen, PacketGaugeActions.charge, PacketGaugeActions.block] at hy'

theorem asymptotic_trace_free (k : ℝ) (hk0 : 0 < k) (hk2 : k < 2) :
    let K : (ℝ × ℂ) →ₗ[ℝ] (ℝ × ℂ) := k • LinearMap.id
    (∀ n : ℕ, (LinearMap.id - K) ^ n = (1 - k) ^ n • LinearMap.id) ∧
      Filter.Tendsto (fun n : ℕ => (1 - k) ^ n) Filter.atTop (nhds 0) ∧
      LinearMap.trace ℝ (ℝ × ℂ) K = 3 * k := by
  intro K
  refine ⟨fun n => ?_, ?_, ?_⟩
  · have : LinearMap.id - K = (1 - k) • (LinearMap.id : (ℝ × ℂ) →ₗ[ℝ] (ℝ × ℂ)) := by
      exact LinearMap.ext fun x => by simp [K, sub_smul]
    rw [this, smul_pow, ← Module.End.one_eq_id, one_pow]
  · exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by rw [abs_lt]; constructor <;> linarith)
  · simp only [K, map_smul, LinearMap.trace_id, ReferenceDirections.displacement_dim]
    simp [smul_eq_mul]; ring

end PMConstants.ReferenceLink
