import PMTransport.OpenHandoff
import PMAction.StateIdentification

/-!
# An antipodal-odd reference for the open handoff

A single carrier basis label lies outside the antipodal-odd sector.
The existing parity-preserving root phases cannot load such a label
from an odd source. An occupied odd coordinate rest mode gives an
alternative on each wall. One existing root loads the other rest
coordinate on that wall. On the first wall this is an odd reference
in the existing live/record port encoding.
-/

noncomputable section
namespace PMTransport.OddReferenceSource

open Matrix PMAction
open scoped Matrix.Norms.Operator

abbrev Carrier := ActualRootRepair.C

theorem basis_label_not_odd (a : Carrier) :
    NativeSector.N 0 *ᵥ Pi.single a (1 : ℂ) ≠ -(Pi.single a 1) := by
  intro h
  have atSeed := congrFun h a
  rw [Matrix.permMatrix_mulVec] at atSeed
  simp [Function.comp_apply, CarrierParity.no_fixed_antipode] at atSeed

/-- Parity-preserving controls cannot turn an odd carrier into the
single-label seed or the single-label record. -/
theorem no_basis_from_odd (U : Matrix Carrier Carrier ℂ)
    (hU : U * NativeSector.N 0 = NativeSector.N 0 * U)
    (ψ : Carrier → ℂ) (hψ : NativeSector.N 0 *ᵥ ψ = -ψ) (a : Carrier) :
    U *ᵥ ψ ≠ Pi.single a 1 := by
  intro h
  apply basis_label_not_odd a
  rw [← h, Matrix.mulVec_mulVec, ← hU, ← Matrix.mulVec_mulVec, hψ, Matrix.mulVec_neg]

/-- In particular the checked orthogonal-root phase family cannot load
a carrier basis label from an odd source, at any choice of phase times. -/
theorem root_phase_word_no_basis (p : ℝ) (word : List (Fin 4 × ℝ))
    (ψ : Carrier → ℂ) (hψ : NativeSector.N 0 *ᵥ ψ = -ψ) (a : Carrier) :
    (word.map (fun j => RootTransferPhase.phase (OrthogonalRootPhase.event 0 j.1) p j.2)).prod *ᵥ ψ
      ≠ Pi.single a 1 := by
  apply no_basis_from_odd _ _ ψ hψ a
  induction word with
  | nil => simp
  | cons j tail ih =>
    simp only [List.map_cons, List.prod_cons]
    exact NativeSector.comm_mul (NativeSector.phase_commute 0 j.1 p j.2) ih

/-- The two rest axes are 0 and 1 on the first wall, and 2 and 3 on the second. -/
def axis (wall record : Bool) : Fin 4 :=
  if wall then (if record then 3 else 2) else (if record then 1 else 0)

def coordinateSeed (wall record : Bool) : Fin 4 → ℂ := Pi.single (axis wall record) 1

def localMode (c : Fin 3) (wall record : Bool) : CarrierEvents.Carrier c → ℂ :=
  CarrierParity.embedding c *ᵥ coordinateSeed wall record

def wallCoordinate (wall record : Bool) : ConcreteFermion.Sites → ℂ :=
  Pi.single (if wall then Sum.inr (axis wall record) else Sum.inl (axis wall record)) 1

def restMode (c : Fin 3) (wall record : Bool) : CarrierVacuumSector.Labels c → ℂ :=
  CarrierVacuumSector.embedding c *ᵥ wallCoordinate wall record

private theorem rest_kernel (wall record : Bool) :
    ConcreteFermion.hamiltonian 0 0 *ᵥ wallCoordinate wall record = 0 := by
  rw [ConcreteFermion.kernel_coordinates]
  cases wall <;> cases record <;> norm_num [wallCoordinate, axis, Pi.single_apply]

theorem rest_stationary (c : Fin 3) (wall record : Bool) (p : ℝ) (hp : 0 < p) (hp' : p < 1 / 2) :
    NativeSector.nativeHamiltonian c p 0 0 *ᵥ restMode c wall record = 0 := by
  rw [restMode, Matrix.mulVec_mulVec, (NativeSector.native_obs hp hp' 0 0).1,
    ← Matrix.mulVec_mulVec, rest_kernel, Matrix.mulVec_zero]

theorem rest_population (c : Fin 3) (wall record : Bool) :
    CommonResponse.nsq (restMode c wall record) = 1 := by
  unfold restMode CommonResponse.nsq
  rw [star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec, CarrierVacuumSector.isometry,
    Matrix.one_mulVec]
  simp [wallCoordinate, dotProduct, Pi.single_apply]

/-- Stationarity alone does not select a seed axis. The two supplied
unit-population rest states on each wall are distinct. -/
theorem rest_modes_distinct (c : Fin 3) (wall : Bool) :
    restMode c wall false ≠ restMode c wall true := by
  intro h
  have hcoord := congrArg (fun ψ => (CarrierVacuumSector.embedding c)ᴴ *ᵥ ψ) h
  simp only [restMode, Matrix.mulVec_mulVec, CarrierVacuumSector.isometry,
    Matrix.one_mulVec] at hcoord
  cases wall
  · have hx := congrFun hcoord (Sum.inl (0 : Fin 4))
    norm_num [wallCoordinate, axis, Pi.single_apply] at hx
  · have hx := congrFun hcoord (Sum.inr (2 : Fin 4))
    norm_num [wallCoordinate, axis, Pi.single_apply] at hx

/-- The existing reflections in e₀−e₁ and e₂−e₃ supply the loading operations. -/
def loadingRoot (c : Fin 3) (wall : Bool) : Equiv.Perm (CarrierEvents.Carrier c) :=
  OrthogonalRootPhase.event c (if wall then 2 else 0)

theorem load_rest_coordinate (c : Fin 3) (wall record : Bool) :
    (loadingRoot c wall).permMatrix ℂ *ᵥ localMode c wall record =
      localMode c wall (!record) := by
  unfold localMode loadingRoot
  rw [Matrix.mulVec_mulVec, OrthogonalRootPhase.intertwining, ← Matrix.mulVec_mulVec]
  congr 1
  funext i
  cases wall <;> cases record <;> fin_cases i <;>
    norm_num [coordinateSeed, axis, OrthogonalRootPhase.R, OrthogonalRootPhase.realMatrix,
      Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply]

private theorem rest_mode_blocks (c : Fin 3) (wall record : Bool) :
    restMode c wall record = if wall then Sum.elim (0 : CarrierEvents.Carrier c → ℂ) (localMode c wall record)
      else Sum.elim (localMode c wall record) (0 : CarrierEvents.Carrier c → ℂ) := by
  have h₀ (r : Bool) : wallCoordinate false r = Sum.elim (coordinateSeed false r) (0 : Fin 4 → ℂ) := by
    funext j
    rcases j with j | j <;> simp [wallCoordinate, coordinateSeed, Pi.single_apply]
  have h₁ (r : Bool) : wallCoordinate true r = Sum.elim (0 : Fin 4 → ℂ) (coordinateSeed true r) := by
    funext j
    rcases j with j | j <;> simp [wallCoordinate, coordinateSeed, Pi.single_apply]
  cases wall
  · rw [restMode, h₀, CarrierVacuumSector.embedding, fromBlocks_mulVec]
    simp [localMode]
  · rw [restMode, h₁, CarrierVacuumSector.embedding, fromBlocks_mulVec]
    simp [localMode]

/-- Apply the root on the selected wall and hold the other wall fixed. -/
def wallLoader (c : Fin 3) (wall : Bool) : Equiv.Perm (CarrierVacuumSector.Labels c) :=
  if wall then Equiv.sumCongr (Equiv.refl _) (loadingRoot c wall)
  else Equiv.sumCongr (loadingRoot c wall) (Equiv.refl _)

theorem wall_loader_involutive (c : Fin 3) (wall : Bool) :
    Function.Involutive (wallLoader c wall) := by
  have h (v : CarrierEvents.Carrier c) : loadingRoot c wall (loadingRoot c wall v) = v :=
    OrthogonalRootPhase.event_involutive c _ v
  intro x
  rcases x with x | x <;> cases wall <;> simp [wallLoader, h]

private theorem wall_loader_blocks (c : Fin 3) (wall : Bool) :
    (wallLoader c wall).permMatrix ℂ =
      fromBlocks (if wall then 1 else (loadingRoot c wall).permMatrix ℂ) 0 0
        (if wall then (loadingRoot c wall).permMatrix ℂ else 1) := by
  cases wall <;> ext i j <;> cases i <;> cases j <;>
    simp [wallLoader, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Matrix.one_apply]

theorem wall_loader_unitary (c : Fin 3) (wall : Bool) :
    (wallLoader c wall).permMatrix ℂ ∈ unitary _ :=
  CarrierResponse.perm_unitary _

theorem load_rest_mode (c : Fin 3) (wall record : Bool) :
    (wallLoader c wall).permMatrix ℂ *ᵥ restMode c wall record = restMode c wall (!record) := by
  rw [wall_loader_blocks, rest_mode_blocks, rest_mode_blocks]
  cases wall <;> simp [fromBlocks_mulVec, load_rest_coordinate]

/-- The entire reconstructed pulse stays in the native rest kernel.
Both components of the intermediate superposition are rest modes. -/
theorem loading_pulse_stays_at_rest (c : Fin 3) (wall record : Bool)
    (p t : ℝ) (hp : 0 < p) (hp' : p < 1 / 2) :
    NativeSector.nativeHamiltonian c p 0 0 *ᵥ
      (RootTransferPhase.phase (wallLoader c wall) p t *ᵥ restMode c wall record) = 0 := by
  rw [RootTransferPhase.phase_formula _ (wall_loader_involutive c wall)]
  simp [InvolutionSpectral.plus, InvolutionSpectral.minus, Matrix.add_mulVec, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul,
    load_rest_mode, rest_stationary _ _ _ p hp hp']

/-- The normalized odd reference in the first wall's existing record ports. -/
def oddReference : Fin 2 → ℂ := (2 * CarrierParity.scale) • ![1, -1]

private theorem outside_moving_axes : ∀ v : Carrier,
    (∀ j : ActualRootRepair.Ports, ActualRootRepair.label j ≠ v) →
    CarrierEvents.vector v 0 = 0 ∧ CarrierEvents.vector v 1 = 0 := by decide +kernel

theorem first_wall_ports (record : Bool) :
    localMode 0 false record = if record then ActualRootRepair.pack 0 oddReference
      else ActualRootRepair.pack oddReference 0 := by
  funext v
  by_cases hv : v ∈ Set.range ActualRootRepair.label
  · obtain ⟨j, rfl⟩ := hv
    simp only [localMode, coordinateSeed, Matrix.mulVec_single_one, Matrix.col_apply,
      CarrierParity.embedding, Records.label_vector]
    cases record <;> rcases j with i | i <;> fin_cases i <;>
      simp only [axis, Bool.false_eq_true, ite_false, ite_true, ActualRootRepair.pack,
        ActualRootRepair.encoded_coordinate, Sum.elim_inl, Sum.elim_inr] <;>
      norm_num [oddReference] <;> ring
  · have hn (j : ActualRootRepair.Ports) : ActualRootRepair.label j ≠ v :=
      fun h => hv ⟨j,h⟩
    obtain ⟨h0,h1⟩ := outside_moving_axes v hn
    have hz (a b : Fin 2 → ℂ) : ActualRootRepair.pack a b v = 0 := by
      simp [ActualRootRepair.pack, ActualRootRepair.embedding, mulVec, dotProduct,
        fun j => Ne.symm (hn j)]
    cases record <;> simp [localMode, coordinateSeed, axis,
       Matrix.col_apply, CarrierParity.embedding, h0, h1, hz]

theorem odd_reference_population : CommonResponse.nsq oddReference = 1 := by
  have h : CommonResponse.nsq (localMode 0 false true) = 1 := by
    unfold localMode CommonResponse.nsq
    rw [star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec, CarrierParity.isometry,
      Matrix.one_mulVec]
    simp [coordinateSeed, dotProduct, Pi.single_apply]
  rw [first_wall_ports] at h
  change CommonResponse.nsq (ActualRootRepair.pack 0 oddReference) = 1 at h
  rw [ActualRootRepair.population] at h
  simpa [LinkExpansion.nsq_eq] using h

/-- With the first-wall root loader, a train of occupied odd rest seeds
supplies the odd reference at every corresponding open-route visit. -/
theorem odd_seed_train_restores {N : ℕ} (s : OpenHandoff.State (Fin 2 → ℂ))
    (loaded : ∀ j : Fin N, (loadingRoot 0 false).permMatrix ℂ *ᵥ localMode 0 false false =
      ActualRootRepair.pack 0 (s (j.val + 1 : ℤ)).2) :
    (∀ j : Fin N, (OpenHandoff.run s (j.val + 1) 0).1 = oddReference) ∧
      OpenReferenceFlow.incomingPopulation s N = N := by
  have hrest : ∀ j : Fin N, (OpenHandoff.run s (j.val + 1) 0).1 = oddReference := by
    apply (OpenHandoff.acceptance_iff_supply s (· = oddReference) N).mpr
    intro j
    have h := loaded j
    rw [load_rest_coordinate, Bool.not_false, first_wall_ports] at h
    change ActualRootRepair.pack 0 oddReference =
      ActualRootRepair.pack 0 (s (j.val + 1 : ℤ)).2 at h
    exact (ActualRootRepair.pack_injective _ _ _ _ h).2.symm
  refine ⟨hrest, ?_⟩
  rw [OpenHandoff.population_required s oddReference N hrest, odd_reference_population, mul_one]

end PMTransport.OddReferenceSource
