import PMConstants.ChannelOccupancy
import PMConstants.ReferenceLink
import PMElementaryParticles.GappedGluedCrossing
import PMKAutomaton.Interface

/-!
# The occupied light projection from the packet gauge action

The absolute hypercharge operator detects exactly the occupied directions
of the glued protocol inventory, including coherent superpositions. Its
range projection removes the single gauge-invisible static slot. Carried
to the wall model, this gives the existing vacancy-truncated static flip.
The isolation result below concerns the label-preserving rest Hamiltonian.
-/

noncomputable section
namespace PMElementaryParticles.VacancyProjection

open Matrix PMConstants.PacketGaugeActions PMConstants.PacketTraceForm
open PMElementaryParticles.ProtocolInventory PMElementaryParticles.ControlledGluedRegister
open scoped Kronecker

/-- Hypercharge is diagonal in the existing packet basis. -/
theorem hyper_diagonal : hyperGen = diagonal (fun c => hyperGen c c) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp
  · rw [Matrix.diagonal_apply_ne _ h]
    exact PMConstants.ReferenceRestoration.hyper_isDiag h

/-- The full hypercharge transport generator in the channel basis. -/
theorem charge_diagonal :
    charge = diagonal (fun c => ((PMConstants.ChannelOccupancy.tag c).2.2 : ℂ) / 3) := by
  have h : (2 : ℂ) • PMConstants.PacketTraceForm.hyperGen = charge := by
    simp [PMConstants.PacketTraceForm.hyperGen, smul_smul]
  calc
    charge = (2 : ℂ) • PMConstants.PacketTraceForm.hyperGen := h.symm
    _ = _ := by
      rw [hyper_diagonal, ← diagonal_smul]
      congr 1
      funext c
      change (2 : ℂ) * PMConstants.PacketTraceForm.hyperGen c c = _
      rw [PMConstants.PacketTraceForm.hyperGen, Matrix.smul_apply, smul_eq_mul,
        PMConstants.ChannelOccupancy.charge_entries]
      ring

/-- The packet hypercharge as real channel charges `tag/3`. -/
theorem charge_real :
    charge = diagonal (fun c => ((((PMConstants.ChannelOccupancy.tag c).2.2 : ℝ) / 3 : ℝ) : ℂ)) := by
  rw [charge_diagonal]
  congr 1
  funext c
  push_cast
  rfl

/-- The packet hypercharge transport is diagonal in the channel basis
(`PMAction.DiagonalReadout.transport_eq_diagonal`). -/
theorem hypercharge_eq_diagonal (t : ℝ) :
    hypercharge t = diagonal (fun c => Complex.exp
      (((t * (((PMConstants.ChannelOccupancy.tag c).2.2 : ℝ) / 3) : ℝ) : ℂ) * Complex.I)) :=
  PMAction.DiagonalReadout.transport_eq_diagonal charge_hermitian _ charge_real t

/-- The flag of the packet hypercharge transport on one channel
(`PMAction.DiagonalReadout.transport_flag`). -/
theorem hypercharge_flag (t : ℝ) (c : Channels) :
    PMAction.InterferenceReadout.flagProbability (hypercharge t) c =
      PMAction.DiagonalReadout.flag (t * (((PMConstants.ChannelOccupancy.tag c).2.2 : ℝ) / 3)) :=
  PMAction.DiagonalReadout.transport_flag charge_hermitian _ charge_real t c

/-- The hypercharge entry vanishes exactly on the inventory vacancy. -/
theorem hyper_entry_zero_iff (c : Channels) :
    hyperGen c c = 0 ↔ baseProtocol c = none := by
  rw [hyperGen, Matrix.smul_apply, smul_eq_mul, PMConstants.ChannelOccupancy.charge_entries]
  rcases c with ⟨i, s⟩ | ⟨i, s⟩ | s | s <;> fin_cases s <;>
    norm_num [PMConstants.ChannelOccupancy.tag, baseProtocol]

/-- The result applies to all amplitudes, so linear combinations of occupied
channels cannot produce additional invisible directions. -/
theorem hyper_kernel_iff (v : Channels → ℂ) :
    hyperGen *ᵥ v = 0 ↔ ∀ c, baseProtocol c ≠ none → v c = 0 := by
  conv_lhs => rw [hyper_diagonal]
  constructor
  · intro h c hc
    have hcoord := congrFun h c
    rw [Matrix.mulVec_diagonal, Pi.zero_apply] at hcoord
    exact (mul_eq_zero.mp hcoord).resolve_left (fun hz => hc ((hyper_entry_zero_iff c).mp hz))
  · intro h
    funext c
    rw [Matrix.mulVec_diagonal, Pi.zero_apply]
    by_cases hc : baseProtocol c = none
    · rw [(hyper_entry_zero_iff c).mpr hc, zero_mul]
    · rw [h c hc, mul_zero]

private theorem vacancy_iff : ∀ c : Channels,
    baseProtocol c = none ↔ c = PMConstants.ReferenceLink.nuR := by
  decide +kernel

/-- The only gauge-invisible direction is the static sterile basis line. -/
theorem invisible_line (v : Channels → ℂ) :
    hyperGen *ᵥ v = 0 ↔
      ∃ z : ℂ, v = Pi.single PMConstants.ReferenceLink.nuR z := by
  rw [hyper_kernel_iff]
  constructor
  · intro h
    refine ⟨v PMConstants.ReferenceLink.nuR, ?_⟩
    funext c
    by_cases hc : c = PMConstants.ReferenceLink.nuR
    · subst c
      simp
    · rw [h c (fun hv => hc ((vacancy_iff c).mp hv))]
      simp [hc]
  · rintro ⟨z, rfl⟩ c hc
    have hn : c ≠ PMConstants.ReferenceLink.nuR := fun h => hc ((vacancy_iff c).mpr h)
    simp [hn]

/-- Projection onto the directions visible to absolute hypercharge. -/
def occupied : M := diagonal fun c => if hyperGen c c = 0 then 0 else 1

theorem occupied_eq_inventory :
    occupied = diagonal (fun c => if baseProtocol c = none then 0 else 1) := by
  unfold occupied
  simp only [hyper_entry_zero_iff]

theorem occupied_hermitian : occupied.IsHermitian := by
  rw [occupied_eq_inventory]
  change (diagonal _)ᴴ = diagonal _
  rw [diagonal_conjTranspose]
  congr 1
  funext c
  by_cases hc : baseProtocol c = none <;> simp [hc]

theorem occupied_idempotent : occupied * occupied = occupied := by
  rw [occupied_eq_inventory, diagonal_mul_diagonal]
  congr 1
  funext c
  by_cases hc : baseProtocol c = none <;> simp [hc]

/-- The existing weak and colour updates preserve the occupied sector for
arbitrary coherent packet amplitudes. -/
theorem gauge_updates_preserve (U : Matrix (Fin 2) (Fin 2) ℂ)
    (V : Matrix (Fin 3) (Fin 3) ℂ) :
    Commute occupied (weak U) ∧ Commute occupied (PMConstants.PacketGaugeActions.colour V) := by
  have hb : occupied = block 1 1 1 (diagonal (![0, 1] : Fin 2 → ℂ)) := by
    have hmask (i : Fin 2) : (if i = 0 then (0 : ℂ) else 1) = ![0, 1] i := by
      fin_cases i <;> rfl
    rw [occupied_eq_inventory]
    ext i j
    rcases i with i | i | i | i <;> rcases j with j | j | j | j <;>
      simp [block, Matrix.diagonal_apply, Matrix.one_apply, baseProtocol, hmask]
    split_ifs <;> simp_all
  constructor
  · show occupied * weak U = weak U * occupied
    simp [hb, weak, block_mul]
  · show occupied * PMConstants.PacketGaugeActions.colour V =
        PMConstants.PacketGaugeActions.colour V * occupied
    simp [hb, PMConstants.PacketGaugeActions.colour, block_mul]

/-- The fixed space of the projector is exactly the range of the existing
hypercharge generator. The inverse on each occupied coordinate is explicit. -/
theorem occupied_fixed_iff (v : Channels → ℂ) :
    occupied *ᵥ v = v ↔ ∃ u : Channels → ℂ, hyperGen *ᵥ u = v := by
  have hApply (u : Channels → ℂ) (c : Channels) :
      (hyperGen *ᵥ u) c = hyperGen c c * u c := by
    calc
      (hyperGen *ᵥ u) c = (diagonal (fun i => hyperGen i i) *ᵥ u) c :=
        congrArg (fun M : Matrix Channels Channels ℂ => (M *ᵥ u) c) hyper_diagonal
      _ = _ := Matrix.mulVec_diagonal _ _ _
  constructor
  · intro hv
    refine ⟨fun c => v c / hyperGen c c, ?_⟩
    funext c
    rw [hApply]
    have he := congrFun hv c
    change (occupied *ᵥ v) c = v c at he
    rw [occupied, Matrix.mulVec_diagonal] at he
    by_cases hc : hyperGen c c = 0
    · have hv0 : v c = 0 := by simpa [hc] using he.symm
      simp [hc, hv0]
    · field_simp
  · rintro ⟨u, rfl⟩
    unfold occupied
    funext c
    rw [Matrix.mulVec_diagonal, hApply]
    by_cases hc : hyperGen c c = 0 <;> simp [hc]

open PMElementaryParticles.GappedGluedCrossing PMAction

/-- On the static wall, reuse the gauge-derived inventory projector at every
generation, in the transported signed-label frame. -/
def staticLight : Matrix Payload Payload ℂ :=
  diagonal fun p => if p.2 = 0 then 0 else 1

theorem staticLight_agrees (g : Fin 3) (c : Channels) (hc : active c = false) :
    staticLight (g, labelIndex c) (g, labelIndex c) = occupied c c := by
  rw [staticLight, occupied_eq_inventory, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
  have h := static_occupied_iff c hc
  by_cases hz : labelIndex c = 0
  · have hnone := not_ne_iff.mp (fun hn => (h.mpr hn) hz)
    simp [hz, hnone]
  · simp [hz, h.mp hz]

/-- Projecting the static light output yields exactly the existing truncated
flip. Only the static light row is projected. -/
theorem projected_static_flip (A : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ) :
    staticLight * blockDiagonal A = blockDiagonal (staticFlip A) := by
  ext ⟨g,a⟩ ⟨h,b⟩
  rw [staticLight, Matrix.diagonal_mul]
  by_cases hab : a = b
  · subst b
    by_cases ha : a = 0 <;> simp [staticFlip, blockDiagonal, ha]
  · simp [staticFlip, blockDiagonal, hab]

/-- The projected rest generator cannot source a static-vacancy light
amplitude. The gapped coordinates of that label remain in the model. -/
theorem static_vacancy_component_zero (y : Fin 3 → ℂ)
    (A : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ) (B : Matrix Payload Payload ℂ)
    (ψ : ((Payload ⊕ Payload) ⊕ (Payload ⊕ Payload)) → ℂ) (g : Fin 3) :
    (ExactZeroMode.H (gapLink y) (blockDiagonal (staticFlip A)) B *ᵥ ψ)
        (.inl (.inl (g, 0))) = 0 := by
  rw [ExactZeroMode.H, fromBlocks_mulVec]
  simp only [zero_mulVec, zero_add, Sum.elim_inl]
  rw [CompositeMass.V2, fromBlocks_mulVec]
  simp only [zero_mulVec, add_zero, Sum.elim_inl]
  rw [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro i _
  rcases i with ⟨h,b⟩
  simp [blockDiagonal, staticFlip]

/-- The vacant light directions are stationary and do not feed any other
coordinate in the projected rest Hamiltonian. -/
theorem static_vacancy_basis_zero (y : Fin 3 → ℂ)
    (A : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ) (B : Matrix Payload Payload ℂ) (g : Fin 3) :
    ExactZeroMode.H (gapLink y) (blockDiagonal (staticFlip A)) B *ᵥ
      Pi.single (.inl (.inl (g, 0))) 1 = 0 := by
  let H := ExactZeroMode.H (gapLink y) (blockDiagonal (staticFlip A)) B
  have hh : Hᴴ = H := by
    simp [H, ExactZeroMode.H, WallSeesaw.G, fromBlocks_conjTranspose]
  change H *ᵥ Pi.single _ 1 = 0
  rw [Matrix.mulVec_single_one]
  funext i
  have hrow : H (.inl (.inl (g, 0))) i = 0 := by
    have h := static_vacancy_component_zero y A B (Pi.single i 1) g
    rwa [Matrix.mulVec_single_one] at h
  change H i (.inl (.inl (g, 0))) = 0
  rw [← hh, Matrix.conjTranspose_apply, hrow, star_zero]

/-- The neutral basis modes remain exactly massless after expressing the
static-light cutoff as the range projection of the gauge action. -/
theorem neutral_zero_after_projection (y : Fin 3 → ℂ) (hy : ∀ g, y g ≠ 0)
    (A B : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ) (g : Fin 3) :
    ∃ z : Payload ⊕ Payload → ℂ,
      ExactZeroMode.H (gapLink y) (staticLight * blockDiagonal A) (blockDiagonal B) *ᵥ
        Sum.elim (Sum.elim 0 (Pi.single (g, 0) 1)) z = 0 := by
  rw [projected_static_flip]
  exact neutral_exact_zero y hy A B g

end PMElementaryParticles.VacancyProjection
