import PMCosmology.SubstrateLoad
import PMFlavor.Values
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Bookkeeping and conditional primordial formulas. Channel labels are not
identified with a complete microscopic state space. A tilt, inflationary
history and baryon-number-changing law are not derived from these counts. -/
noncomputable section
namespace PMCosmology.Primordial

/-- The paper's tilt formula uses the same channel-overhead term as the load. -/
theorem tilt_channel_link : scalarIndex = 1-SubstrateLoad.channelStress := by
  norm_num [scalarIndex, SubstrateLoad.channelStress, PMSubstrate.baseline]

/-- If all 32 labels must remain distinguishable, truncation to 16 alone
cannot be reversible. This does not equate mode counts with state counts. -/
theorem truncation_not_injective :
    ¬ ∃ f : Fin 32 → Fin 16, Function.Injective f := by
  rintro ⟨f,hf⟩
  have h := Fintype.card_le_of_injective f hf
  norm_num at h

/-- An explicit retained binary label suffices for reversible relabeling. -/
def retained_label : Fin 32 ≃ (Fin 16 × Fin 2) :=
  Fintype.equivOfCardEq (by simp)

theorem retained_record_required (R : ℕ) (f : Fin 32 → Fin 16 × Fin R)
    (hf : Function.Injective f) : 2 ≤ R := by
  have h := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin, Fintype.card_prod] at h
  omega

/-- The adopted conversion/dilution law, parameterized by its CP input.
It is not obtained from a CP invariant without baryon-changing dynamics. -/
def baryonRatio (J : ℝ) : ℝ :=
  J/(PMSubstrate.baseline.sectorChannels : ℝ) /
    ((Real.pi*PMSubstrate.baseline.period) *
      (PMSubstrate.baseline.intrinsicLoad +
        PMSubstrate.baseline.eulerCharacteristic/(PMSubstrate.baseline.dimension : ℝ)))

theorem baryon_ratio_reduced (J : ℝ) : baryonRatio J = J/(16168*Real.pi) := by
  norm_num [baryonRatio, PMSubstrate.baseline, PMSubstrate.Parameters.intrinsicLoad]
  ring

theorem baryon_ratio_strictMono : StrictMono baryonRatio := by
  intro a b hab
  rw [baryon_ratio_reduced, baryon_ratio_reduced]
  exact div_lt_div_of_pos_right hab (by positivity)

/-- The CKM matrix's invariant and the separate geometric formula give
strictly different primordial outputs under the same conversion rule. -/
theorem cp_input_changes_prediction :
    baryonRatio PMFlavor.Values.jarlskog < baryonRatio PMFlavor.Values.jarlskogGeo := by
  apply baryon_ratio_strictMono
  have h1 := PMFlavor.Values.jarlskog_bounds
  have h2 := PMFlavor.Values.jarlskogGeo_bounds
  linarith

/-- Frozen rational windows, not a likelihood analysis or new measurements. -/
theorem baryon_windows :
    5.94e-10 < baryonRatio PMFlavor.Values.jarlskog ∧
    baryonRatio PMFlavor.Values.jarlskog < 5.97e-10 ∧
    6.07e-10 < baryonRatio PMFlavor.Values.jarlskogGeo ∧
    baryonRatio PMFlavor.Values.jarlskogGeo < 6.08e-10 := by
  have h1 := PMFlavor.Values.jarlskog_bounds
  have h2 := PMFlavor.Values.jarlskogGeo_bounds
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  have hd : 0 < 16168*Real.pi := by positivity
  simp only [baryon_ratio_reduced]
  refine ⟨(lt_div_iff₀ hd).mpr ?_, (div_lt_iff₀ hd).mpr ?_,
    (lt_div_iff₀ hd).mpr ?_, (div_lt_iff₀ hd).mpr ?_⟩ <;> linarith

/-- A conserved baryon label stays fixed at every iterate, whatever the
numerical CP parameter is. CP alone supplies no baryon-number change. -/
theorem conserved_baryon (X : Type*) (update : X → X) (B : X → ℝ)
    (hB : ∀ x, B (update x)=B x) (n : ℕ) (x : X) : B (update^[n] x)=B x := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Function.iterate_succ_apply', hB] using ih

/-- Zero forcing does not force zero homogeneous modes: cos(t) solves
h''+h=0 and has h(0)=1. This is an ODE boundary check, not a derived tensor
perturbation equation or a prediction for gravitational radiation. -/
theorem source_free_nonzero :
    (∀ t : ℝ, HasDerivAt Real.cos (-Real.sin t) t ∧
      HasDerivAt (fun x => -Real.sin x) (-Real.cos t) t) ∧ Real.cos 0 ≠ 0 := by
  refine ⟨fun t => ⟨Real.hasDerivAt_cos t, (Real.hasDerivAt_sin t).neg⟩, ?_⟩
  norm_num

end PMCosmology.Primordial
