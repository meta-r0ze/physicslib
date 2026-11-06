import PMAtoms.BetaLattice
import PMAtoms.CollectiveRate
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.

# Finite collective rate

Replaces the continuum `exp(−barrier)` channel by a finite family of collective
barriers with Boltzmann weights.  This is the alpha/fission analogue of the
finite spectral beta channel.
-/

noncomputable section
namespace PMAtoms

/-- Boltzmann weight of one collective channel. -/
noncomputable def collectiveBarrierWeight (barrier : ℝ) : ℝ :=
  Real.exp (-barrier)

theorem collectiveBarrierWeight_pos (barrier : ℝ) :
    0 < collectiveBarrierWeight barrier := by
  unfold collectiveBarrierWeight
  positivity

/-- Finite collective rate: open barrier weight over total barrier weight. -/
noncomputable def collectiveFiniteRate (β c0 : ℝ) {k : Nat}
    (barriers : Fin k → ℝ) (S : Finset (Fin k)) : ℝ :=
  β * c0 * S.sum (fun i => collectiveBarrierWeight (barriers i)) /
    Finset.univ.sum (fun i => collectiveBarrierWeight (barriers i))

set_option linter.style.haveILetI false in
theorem collectiveFiniteRate_pos (β c0 : ℝ) {k : Nat}
    (barriers : Fin k → ℝ) (S : Finset (Fin k))
    (hβ : 0 < β) (hc0 : 0 < c0) (hk : 0 < k) (hS : S.Nonempty) :
    0 < collectiveFiniteRate β c0 barriers S := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have htotal : 0 < Finset.univ.sum (fun i => collectiveBarrierWeight (barriers i)) := by
    apply Finset.sum_pos
    · intro i _
      exact collectiveBarrierWeight_pos _
    · exact Finset.univ_nonempty
  have hpart : 0 < S.sum (fun i => collectiveBarrierWeight (barriers i)) := by
    apply Finset.sum_pos
    · intro i _
      exact collectiveBarrierWeight_pos _
    · exact hS
  unfold collectiveFiniteRate
  exact div_pos (mul_pos (mul_pos hβ hc0) hpart) htotal

end PMAtoms
