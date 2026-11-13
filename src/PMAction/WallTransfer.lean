import PMAction.FermionFlip

/-!
# The substrate's chiral anomaly: chirality changes only by transfer between the walls

The two chiral sectors are the two walls (`WallChiralCurrent`, `ChiralityConvention`). For each
flavour `f`, a configuration has `left f` carriers on the left wall and `right f` on the right; the
chirality is `right f − left f`.

* `chirality_change` (Conservation): an update conserves each flavour's carrier number, so the
  chirality changes by exactly twice the net number moved from the left wall to the right,
  `transfer f`. Chirality is not created; it flows between the walls (the inflow form of the
  anomaly).
* `flavour_blind_transfer`: the gauge background acts identically on every flavour's copy, so from
  a flavour-symmetric vacuum every flavour transfers the same number.
* `history_factor`: a history that moves `n` carriers of every flavour from the left wall to the
  right, each through the mass bilinear `M` (the only term joining the walls), multiplies the
  fermionic amplitude by `(det M)ⁿ` (`FermionFlip.flip_amplitude`), whose phase is `e^{i n arg det M}`
  (`FermionFlip.winding_phase`).

So the premise of `PMConstants.ThetaBarSelection` (a winding-`n` history carries the mass phase
`n · arg det M` times a nonnegative weight) holds with the winding read as the substrate's own
transfer count `n`. What remains imported is only the identification of that count with the
lattice topological charge (Lüscher), which `WindingWeights` uses to make the sectors open.
-/

noncomputable section
namespace PMAction.WallTransfer
open Matrix

variable {F : Type*}

/-- Carriers of each flavour on the two walls. -/
structure Config (F : Type*) where
  left : F → ℤ
  right : F → ℤ

/-- Chirality of flavour `f`: right minus left. -/
def chirality (s : Config F) (f : F) : ℤ := s.right f - s.left f

/-- Net carriers of flavour `f` moved from the left wall to the right. -/
def transfer (s s' : Config F) (f : F) : ℤ := s'.right f - s.right f

/-- **Conservation: chirality changes by twice the transfer.** -/
theorem chirality_change (s s' : Config F) (f : F)
    (hcons : s'.left f + s'.right f = s.left f + s.right f) :
    chirality s' f - chirality s f = 2 * transfer s s' f := by
  unfold chirality transfer
  omega

/-- **A flavour-blind background transfers the same number in every flavour.** The update acts on
each flavour's pair `(left, right)` by one map `g`; from a flavour-symmetric state the transfers are
equal. -/
theorem flavour_blind_transfer (g : ℤ × ℤ → ℤ × ℤ) (s : Config F)
    (hsym : ∀ f f', s.left f = s.left f' ∧ s.right f = s.right f') (f f' : F) :
    let s' : Config F := ⟨fun x => (g (s.left x, s.right x)).1, fun x => (g (s.left x, s.right x)).2⟩
    transfer s s' f = transfer s s' f' := by
  intro s'
  obtain ⟨hl, hr⟩ := hsym f f'
  simp only [transfer, s', hl, hr]

/-- **`n` transfers in every flavour carry `(det M)ⁿ`.** Each round moves one carrier of every
flavour through `M`; the alternating amplitude picks up `det M` per round. -/
theorem history_factor {k : ℕ} (ψ : (Fin k → ℂ) [⋀^Fin k]→ₗ[ℂ] ℂ)
    (M : Matrix (Fin k) (Fin k) ℂ) (n : ℕ) (v : Fin k → Fin k → ℂ) :
    ψ (fun i => (M ^ n) *ᵥ v i) = M.det ^ n * ψ v := by
  rw [FermionFlip.flip_amplitude, Matrix.det_pow]

end PMAction.WallTransfer
