import PMAction.CarrierAdmittance

/-!
# The reference's stationarity forbids direct exchange into or out of its class on its wall

`CarrierAdmittance`: every conserving exchange is scalar on the reference and the native exchange is
the same for the three classes, so exchange amplitudes alone do not separate the classes. This
module finds what does: the reference itself.

Setup. A wire state has a class index (`Fin 3`, the three nontrivial glue classes) and the two-wall
Dirac components (`Sites`). Each class carries the wall Hamiltonian `hamiltonian 0 0`
(`CarrierVacuumSector`: every class realizes the same Dirac structure). On the reference's wall
(the second wall, `ChiralityConvention.physicalBackground`) a single-wall exchange moves class `a`
to class `b` with a Dirac block `X a b`, conserving (it commutes with `Γ` and `Σⱼ`,
`CarrierAdmittance.commutant_chiral`); the on-site part is the wall Hamiltonian, so `X a a = 0`.
The reference is class-definite, indexed here by `0` (the vector class:
`PMConstants.CarrierRepresentation`, `GenerationLabel`'s `v`); this module uses that premise and
nothing about the other wall. One class is selected in `PersistenceSelections` (3): a reference
spread over classes survives class-dependent phases only with every exchange on its support
suppressed, and one class is the cheapest such support.

* `act_reference`: on the reference the wall part vanishes (`physicalBackground_kernel`) and each
  exchange out of class `0` gives `X 0 b 2 2` times the reference in class `b`
  (`CarrierAdmittance.scalar_on_reference`).
* `stationary_iff`: for a nonzero reference, it stays a zero mode exactly when `X 0 b 2 2 = 0` for
  both other classes.
* `out_of_reference_chiral`: then the exchange out of class `0` is `X 0 b 0 0 · (1 + Γ)/2`: it is
  zero on the reference wall's whole `−Γ` sector, where that wall's light modes live. With the
  exchange Hermitian (`X b 0 = (X 0 b)ᴴ`), the same holds into class `0`.

**For the light mass.** `GenerationMass`: generation `g`'s carrier on a wall moves class `g + 1` to
`g − 1`, a change by its label `g`. On the reference wall this involves class `0` exactly when
`g ≠ 0` (`touches_reference_class`). So the reference's stationarity forbids the direct
insertion for the two generations labelled `s`, `c`, and allows it for the generation labelled `v`:
`κ_R = (K, 0, 0)` at first order, the triality broken by the reference's class. Their mass must
come from a process that restores the reference (through its node), at higher order. The other
wall carries no reference and its exchanges stay class-blind (`CarrierAdmittance.uniform_hop`).
The size of the restoring process (`NodeAmplitude`'s leg count) is the open part.
-/

noncomputable section
namespace PMAction.ReferenceClassHop
open Matrix ConcreteFermion

/-- The second wall's four components of a two-wall vector. -/
def wall2 (ψ : Sites → ℂ) : Fin 4 → ℂ := fun i => ψ (Sum.inr i)

/-- The wire action: the wall Hamiltonian in every class, plus the reference wall's class exchange. -/
def act (X : Fin 3 → Fin 3 → Spin) (ψ : Fin 3 → Sites → ℂ) : Fin 3 → Sites → ℂ :=
  fun b => hamiltonian 0 0 *ᵥ ψ b +
    Sum.elim (fun _ => 0) (∑ a, X a b *ᵥ wall2 (ψ a))

/-- The reference, in class `0`. -/
def reference (r : Fin 2 → ℂ) : Fin 3 → Sites → ℂ :=
  fun b => if b = 0 then ChiralityConvention.physicalBackground r else 0

theorem wall2_reference (r : Fin 2 → ℂ) :
    wall2 (ChiralityConvention.physicalBackground r) =
      ![0, 0, (Real.sqrt 2 : ℂ) * r 0, (Real.sqrt 2 : ℂ) * r 1] := by
  ext i; simp [wall2, ChiralityConvention.physicalBackground_apply]

theorem wall2_ne_zero (r : Fin 2 → ℂ) (hr : r ≠ 0) :
    wall2 (ChiralityConvention.physicalBackground r) ≠ 0 := by
  rw [wall2_reference]
  intro h
  apply hr
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 2 := by positivity
    exact_mod_cast this.ne'
  ext i; fin_cases i
  · simpa [hs] using h2
  · simpa [hs] using h3

/-- Conserving: commutes with the chirality and the spin. -/
def Conserving (Y : Spin) : Prop :=
  Y * gamma = gamma * Y ∧ ∀ j, Y * ConfinedAxialCurrent.Sigma j = ConfinedAxialCurrent.Sigma j * Y

/-- **On the reference, only the exchange out of its class acts, as a number times the reference.** -/
theorem act_reference (X : Fin 3 → Fin 3 → Spin) (hX : ∀ a b, Conserving (X a b))
    (r : Fin 2 → ℂ) (b : Fin 3) :
    act X (reference r) b =
      Sum.elim (fun _ => 0) (X 0 b 2 2 • wall2 (ChiralityConvention.physicalBackground r)) := by
  have hk := ChiralityConvention.physicalBackground_kernel r
  have hsum : (∑ a, X a b *ᵥ wall2 (reference r a)) =
      X 0 b *ᵥ wall2 (ChiralityConvention.physicalBackground r) := by
    have hz : wall2 (0 : Sites → ℂ) = 0 := rfl
    rw [Fin.sum_univ_three]
    simp [reference, hz]
  have hsc := CarrierAdmittance.scalar_on_reference (X 0 b) (hX 0 b).1 (hX 0 b).2
    (wall2 (ChiralityConvention.physicalBackground r))
    (by simp [wall2_reference]) (by simp [wall2_reference])
  unfold act
  rw [hsum, hsc]
  by_cases hb : b = 0
  · subst hb; simp [reference, hk]
  · simp [reference, hb]

/-- **The reference stays a zero mode exactly when no exchange leaves its class.** -/
theorem stationary_iff (X : Fin 3 → Fin 3 → Spin) (hX : ∀ a b, Conserving (X a b))
    (h00 : X 0 0 = 0) (r : Fin 2 → ℂ) (hr : r ≠ 0) :
    act X (reference r) = 0 ↔ X 0 1 2 2 = 0 ∧ X 0 2 2 2 = 0 := by
  have hne := wall2_ne_zero r hr
  have key : ∀ b, act X (reference r) b = 0 ↔ X 0 b 2 2 = 0 := by
    intro b
    rw [act_reference X hX r b]
    constructor
    · intro h
      by_contra hc
      apply hne
      ext i
      have := congrFun h (Sum.inr i)
      simp only [Sum.elim_inr, Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at this
      exact (mul_eq_zero.mp this).resolve_left hc
    · intro h; ext x; rcases x with i | i <;> simp [h]
  constructor
  · intro h
    exact ⟨(key 1).1 (congrFun h 1), (key 2).1 (congrFun h 2)⟩
  · rintro ⟨h1, h2⟩
    funext b
    fin_cases b
    · exact (key 0).2 (by simp [h00])
    · exact (key 1).2 h1
    · exact (key 2).2 h2

/-- **Then the exchange out of the reference's class lives only on the `+Γ` sector.** -/
theorem out_of_reference_chiral (Y : Spin) (hY : Conserving Y) (h : Y 2 2 = 0) :
    Y = Y 0 0 • CarrierAdmittance.plus := by
  have hc := CarrierAdmittance.commutant_chiral Y hY.1 hY.2
  rw [h, zero_smul, add_zero] at hc
  exact hc

/-- It vanishes on every state of the reference wall's `−Γ` sector (axes `2, 3`). -/
theorem out_of_reference_kills_light (Y : Spin) (hY : Conserving Y) (h : Y 2 2 = 0)
    (v : Fin 4 → ℂ) (h0 : v 0 = 0) (h1 : v 1 = 0) : Y *ᵥ v = 0 := by
  rw [CarrierAdmittance.scalar_on_reference Y hY.1 hY.2 v h0 h1, h, zero_smul]

/-- **Generation `g`'s carrier (`g + 1 → g − 1`) involves class `0` exactly when `g ≠ 0`.** -/
theorem touches_reference_class : ∀ g : Fin 3, (g + 1 = 0 ∨ g - 1 = 0) ↔ g ≠ 0 := by decide

end PMAction.ReferenceClassHop
