import PMConstants.OnShell

/-!
# External states are on-shell mass eigenstates, from persistence

`TODO` item 1 keeps "positive on-shell energies" of the external states as a
hypothesis. Part of it follows from persistence.

Write a state in an energy eigenbasis of its Hamiltonian, with energies `E j` and
`E j² = p² + m j²` (for the two-wall fermion, `PMAction.WallSpectrumLink.wall_energies`). It evolves by
diagonal phases. A state that persists, staying on its ray for all times, has one frequency on its
support (`PMConstants.OnShell.persistent_single_frequency`, the beats argument). So:

* `persistent_on_shell`: every component of a persisting state has the same energy and the same
  mass. It is on shell with a definite mass: superpositions across mass branches beat, and
  superpositions of `+E` and `−E` beat. A persisting external particle has one sign of energy and
  one mass.

Still inputs: which sign is called the particle (positive energy is a convention once the sign is
single), and the identification of the external particle with a persisting state of the
substrate.

### Charged density and wall leakage

`PMAction.WallRestChirality.chargedPart_is_native_density` identifies the retained `(d, b)`
coordinates of the two-wall model with the native chiral density projector.
At rest, `ExactZeroMode.H` couples only opposite chiralities. Its two chiral
eigenvalue equations force equal squared norms in the two sectors for every
nonzero real eigenvalue. Thus a unit-normalized mode supplies exactly half its
squared norm to the charged density (`PMAction.WallRestChirality.charged_weight_half`).

For orthonormal daughter columns in the full wall space, `daughter_sum_eq_projection`
gives the sum of squared density amplitudes as the squared norm projected onto
their span. With an isometric generation rotation on the charged sector,
`density_strength_eq_half_fraction` gives one half of the projected fraction.
The common half cancels in a ratio of two such unweighted strengths (with
nonzero calibration strength). These identities use no measured mixing entries
or fitted wall weights. `paired_window_strength` proves that a window of
complete nonzero-energy chiral pairs gives twice the unweighted density
strength of its positive-energy subset. The factor cancels against the muon
strength if both windows meet the same conditions. For the factorized contact
model with two massless spectators, `contactWeight_open` supplies the exact
integrated weight for a massive daughter. `contact_channel_pos_iff` gives a
strictly positive contribution exactly for an open channel with nonzero
amplitude (and nonzero contact coupling). For two spectator masses
`m₁, m₂`, `PairInvariantSpectrum.massive_pair_window` proves the open
pair-invariant interval `(m₁ + m₂)² < s < (m − μ)²`. Its interior exists
exactly when `μ + m₁ + m₂ < m` (`massive_channel_open_iff`). The positive
rest momentum of the pair exists at every energy above its threshold.
`MassiveVolume.shell_density_at_energy` supplies the pair shell factor for
all nonnegative spectator masses. `MassivePair.pair_contraction` transports
and contracts the massive tensor. `PairInvariantSpectrum.massive_contact_density`
then multiplies the angularly averaged V–A rate by the recoil measure and
parent flux. Its integrated weight `massiveContactWidth` is a one-dimensional
integral over the physical daughter-energy interval and vanishes for a closed
channel. The two-massless-spectator limit agrees exactly with the earlier
integrated width. The native amplitude and physical state assignment
are still needed to apply these contact weights.
`PMAction.NativeWallOffset.rest_offset_breaks_chirality` shows that a retained
one-wall lazy offset breaks the chiral anticommutation even after a common
energy shift. In that case the off-diagonal model's paired-window factor
requires rechecking against the new spectrum.

**Daughter channels.** The contact-width results apply with supplied physical states and their masses. `ExternalStates.persistent_on_shell` gives the on-shell relation. The admitted current, state assignment and open channels are needed for a decay calculation.


-/

noncomputable section
namespace PMElementaryParticles.ExternalStates
open Complex

/-- **Persisting states are on shell with one mass and one energy.** -/
theorem persistent_on_shell {n : Type*} (E : n → ℝ) (msq : n → ℝ) (p : ℝ)
    (hshell : ∀ j, E j ^ 2 = p ^ 2 + msq j) (c : n → ℂ)
    (hpersist : ∀ t : ℝ, ∃ k : ℂ, ∀ j, c j * exp (-((E j * t : ℝ) : ℂ) * I) = k * c j)
    (i j : n) (hi : c i ≠ 0) (hj : c j ≠ 0) : E i = E j ∧ msq i = msq j := by
  have hE := PMConstants.OnShell.persistent_single_frequency E c hpersist i j hi hj
  refine ⟨hE, ?_⟩
  have := hshell i
  rw [hE, hshell j] at this
  linarith

/-- **Two wall branches with different masses do not form a persisting state.** -/
theorem branches_do_not_persist (E1 E2 : ℝ) (c1 c2 : ℂ) (h1 : c1 ≠ 0) (h2 : c2 ≠ 0)
    (hne : E1 ≠ E2) :
    ¬ ∀ t : ℝ, ∃ k : ℂ, c1 * exp (-((E1 * t : ℝ) : ℂ) * I) = k * c1 ∧
      c2 * exp (-((E2 * t : ℝ) : ℂ) * I) = k * c2 := by
  rw [PMConstants.OnShell.beats c1 c2 E1 E2 hne]
  tauto

end PMElementaryParticles.ExternalStates
