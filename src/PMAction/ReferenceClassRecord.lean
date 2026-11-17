import PMAction.ReferenceClassHop
import PMAction.Machine.CoherentRecordRestoration

/-!
# A retained class record and a class-definite reference

A faithful class record uses orthonormal marker columns for the three carrier classes.
If recording preserves a nonzero pure reference's class density, the reference
occupies exactly one class and is independent of its record. No class is chosen
by the theorem.
This does not prove particle occupation one or select the physical record operation.
The existing live/record mode swap is a direct sum, not this tensor record contract.
-/
noncomputable section
namespace PMAction.ReferenceClassRecord
open Matrix

abbrev Profile := Fin 3 → ℂ

/-- A class-definite amplitude; the nonzero amplitude is not fixed or normalized. -/
def SingleClass (ψ : Profile) : Prop :=
  ∃ r : Fin 3, ∃ a : ℂ, a ≠ 0 ∧ ψ = Pi.single r a

/-- A supplied record encoding keeps the class index and writes its marker. -/
def recorded {R : Type*} (E : Matrix R (Fin 3) ℂ) (ψ : Profile) : Fin 3 × R → ℂ :=
  fun p => ψ p.1 * E p.2 p.1

def product {R : Type*} (ψ : Profile) (ρ : R → ℂ) : Fin 3 × R → ℂ :=
  fun p => ψ p.1 * ρ p.2

/-- Orthogonal normalized records distinguish the classes. -/
theorem marker_injective {R : Type*} [Fintype R]
    (E : Matrix R (Fin 3) ℂ) (hE : Eᴴ * E = 1) :
    Function.Injective (fun c => fun d => E d c) := by
  intro c d h
  have hc : E *ᵥ Pi.single c 1 = E *ᵥ Pi.single d 1 := by
    simpa only [mulVec_single_one, Matrix.col_apply'] using h
  have hr := congrArg (fun v => Eᴴ *ᵥ v) hc
  simp only [mulVec_mulVec, hE, one_mulVec] at hr
  by_contra hne
  have hh := congrFun hr c
  simp [hne] at hh

/-- A non-disturbing independent record forces one class, if its markers distinguish classes.
The actual admission and attachment of such a record remain a substrate premise. -/
theorem single_class_of_record {R : Type*} (E : Matrix R (Fin 3) ℂ)
    (hE : Function.Injective (fun c => fun d => E d c))
    (ψ : Profile) (hψ : ψ ≠ 0) (ρ : R → ℂ)
    (hrec : recorded E ψ = product ψ ρ) : SingleClass ψ := by
  have hex : ∃ r, ψ r ≠ 0 := by
    by_contra h
    push Not at h
    apply hψ
    exact funext h
  obtain ⟨r, hr⟩ := hex
  have col (c : Fin 3) (hc : ψ c ≠ 0) : (fun d => E d c) = ρ := by
    funext d
    have hh := congrFun hrec (c,d)
    change ψ c * E d c = ψ c * ρ d at hh
    exact mul_left_cancel₀ hc hh
  refine ⟨r, ψ r, hr, ?_⟩
  funext c
  by_cases hc : c = r
  · simp [hc]
  · have hz : ψ c = 0 := by
      by_contra hn
      exact hc (hE ((col c hn).trans (col r hr).symm))
    simp [hc, hz]

/-- Conversely, a single-class reference writes only its class's record marker. -/
theorem record_single {R : Type*} (E : Matrix R (Fin 3) ℂ) (r : Fin 3) (a : ℂ) :
    recorded E (Pi.single r a) = product (Pi.single r a) (fun d => E d r) := by
  funext p
  rcases p with ⟨c,d⟩
  by_cases hc : c = r <;> simp [recorded, product, hc]

/-- Exact criterion; orthonormal marker encoding supplies faithfulness. -/
theorem independent_record_iff {R : Type*} [Fintype R]
    (E : Matrix R (Fin 3) ℂ) (hE : Eᴴ * E = 1) (ψ : Profile) (hψ : ψ ≠ 0) :
    (∃ ρ, recorded E ψ = product ψ ρ) ↔ SingleClass ψ := by
  constructor
  · rintro ⟨ρ,hρ⟩
    exact single_class_of_record E (marker_injective E hE) ψ hψ ρ hρ
  · rintro ⟨r,a,ha,rfl⟩
    exact ⟨_,record_single E r a⟩

/-- The class density after the retained record is left unread. -/
def reduced {R : Type*} [Fintype R] (Φ : Fin 3 × R → ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ := fun i j => ∑ d, Φ (i,d) * star (Φ (j,d))

def pureDensity (ψ : Profile) : Matrix (Fin 3) (Fin 3) ℂ :=
  vecMulVec ψ (star ψ)

/-- Faithful orthonormal markers remove off-diagonal class coherence when unread. -/
theorem reduced_record {R : Type*} [Fintype R]
    (E : Matrix R (Fin 3) ℂ) (hE : Eᴴ * E = 1) (ψ : Profile) :
    reduced (recorded E ψ) = fun i j => if i = j then ψ i * star (ψ j) else 0 := by
  ext i j
  have hg : (∑ d, star (E d j) * E d i) = (1 : Matrix (Fin 3) (Fin 3) ℂ) j i := by
    simpa only [mul_apply, conjTranspose_apply] using congrFun (congrFun hE j) i
  unfold reduced recorded
  calc
    (∑ d, ψ i * E d i * star (ψ j * E d j)) =
        (ψ i * star (ψ j)) * (∑ d, star (E d j) * E d i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      simp only [star_mul]
      ring
    _ = _ := by
      rw [hg]
      by_cases h : i = j
      · subst j; simp
      · simp [h, Ne.symm h]

/-- Nondisturbance of a nonzero pure reference suffices: independence of the
record need not be a separate assumption. -/
theorem nondisturbing_record_iff {R : Type*} [Fintype R]
    (E : Matrix R (Fin 3) ℂ) (hE : Eᴴ * E = 1) (ψ : Profile) (hψ : ψ ≠ 0) :
    reduced (recorded E ψ) = pureDensity ψ ↔ SingleClass ψ := by
  rw [reduced_record E hE]
  constructor
  · intro h
    have hex : ∃ r, ψ r ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hψ (funext hn)
    obtain ⟨r,hr⟩ := hex
    refine ⟨r,ψ r,hr,?_⟩
    funext c
    by_cases hc : c = r
    · simp [hc]
    · have hh := congrFun (congrFun h c) r
      have hsr : star (ψ r) ≠ 0 := by simpa using hr
      have hz : ψ c = 0 := by
        have he : ψ c * star (ψ r) = 0 := by
          simpa [pureDensity, vecMulVec, hc] using hh.symm
        exact (mul_eq_zero.mp he).resolve_right hsr
      simp [hc,hz]
  · rintro ⟨r,a,ha,rfl⟩
    ext i j
    by_cases hij : i = j
    · subst j; simp [pureDensity, vecMulVec]
    · by_cases hir : i = r
      · subst i; simp [pureDensity, vecMulVec, Pi.single_apply, hij, Ne.symm hij]
      · simp [pureDensity, vecMulVec, Pi.single_apply, hij, hir]

/-- The selected profile has exactly one nonzero class component. This counts
class support, not particles in a many-carrier configuration. -/
theorem recorded_support_card {R : Type*} [Fintype R]
    (E : Matrix R (Fin 3) ℂ) (hE : Eᴴ * E = 1) (ψ : Profile) (hψ : ψ ≠ 0)
    (hrec : ∃ ρ, recorded E ψ = product ψ ρ) :
    (Finset.univ.filter (fun c => ψ c ≠ 0)).card = 1 := by
  obtain ⟨r,a,ha,rfl⟩ := (independent_record_iff E hE ψ hψ).mp hrec
  have hs : (Finset.univ.filter (fun c : Fin 3 => (Pi.single r a : Profile) c ≠ 0)) = {r} := by
    ext c
    by_cases hc : c = r <;> simp [hc, ha]
  rw [hs, Finset.card_singleton]

/-! ## A reversible finite-label implementation of the record contract -/

/-- Controlled addition writes a class into a clean three-valued record.
Addition here is on the record-index alphabet, not E8 glue-class addition.
This is a supplied record operation; no native gate admission is inferred. -/
def recordPermutation : Equiv.Perm (Fin 3 × Fin 3) where
  toFun p := (p.1, p.2 + p.1)
  invFun p := (p.1, p.2 - p.1)
  left_inv p := by simp
  right_inv p := by simp

def cleanRecord (ψ : Profile) : Fin 3 × Fin 3 → ℂ :=
  fun p => if p.2 = 0 then ψ p.1 else 0

theorem record_unitary :
    (Equiv.Perm.permMatrix ℂ recordPermutation.symm) ∈
      unitary (Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) :=
  CarrierResponse.perm_unitary _

/-- The diagonal class recording is the coherent lift of a reversible label map. -/
theorem reversible_record (ψ : Profile) :
    (Equiv.Perm.permMatrix ℂ recordPermutation.symm) *ᵥ cleanRecord ψ =
      recorded (1 : Matrix (Fin 3) (Fin 3) ℂ) ψ := by
  rw [permMatrix_mulVec]
  funext p
  rcases p with ⟨c,d⟩
  change (if d - c = 0 then ψ c else 0) = ψ c * (1 : Matrix (Fin 3) (Fin 3) ℂ) d c
  simp [sub_eq_zero, Matrix.one_apply]

/-- On a class-definite reference, stationarity kills every outgoing class exchange. -/
theorem stationary_single_iff (X : Matrix (Fin 3) (Fin 3) ℂ) (r : Fin 3)
    (a : ℂ) (ha : a ≠ 0) :
    X *ᵥ Pi.single r a = 0 ↔ ∀ c, X c r = 0 := by
  simp only [mulVec_single, funext_iff, Pi.zero_apply]
  constructor
  · intro h c
    exact (mul_eq_zero.mp (h c)).resolve_right ha
  · intro h c
    simp [h c]

/-- Recording and stationarity together forbid exchange out of the selected class. -/
theorem recorded_stationary {R : Type*} [Fintype R]
    (E : Matrix R (Fin 3) ℂ) (hE : Eᴴ * E = 1)
    (X : Matrix (Fin 3) (Fin 3) ℂ) (ψ : Profile) (hψ : ψ ≠ 0)
    (hrec : ∃ ρ, recorded E ψ = product ψ ρ) (hstat : X *ᵥ ψ = 0) :
    ∃ r : Fin 3, ∃ a : ℂ, a ≠ 0 ∧ ψ = Pi.single r a ∧ ∀ c, X c r = 0 := by
  obtain ⟨r,a,ha,h⟩ := (independent_record_iff E hE ψ hψ).mp hrec
  refine ⟨r,a,ha,h,?_⟩
  rw [h] at hstat
  exact (stationary_single_iff X r a ha).mp hstat

/-- Conservation supplies the corresponding incoming-exchange exclusion. -/
theorem incoming_zero (X : Matrix (Fin 3) (Fin 3) ℂ) (hX : X.IsHermitian)
    (r : Fin 3) (hout : ∀ c, X c r = 0) : ∀ c, X r c = 0 := by
  intro c
  have h := congrFun (congrFun hX r) c
  simpa [conjTranspose_apply, hout c] using h.symm

/-! ## Attachment to the existing reference-wall exchange -/

/-- The same physical reference spin state, with an arbitrary class profile. -/
def wallReference (ψ : Profile) (r : Fin 2 → ℂ) : Fin 3 → ConcreteFermion.Sites → ℂ :=
  fun c => ψ c • ChiralityConvention.physicalBackground r

lemma wall2_reference (ψ : Profile) (r : Fin 2 → ℂ) (c : Fin 3) :
    ReferenceClassHop.wall2 (wallReference ψ r c) =
      ψ c • ReferenceClassHop.wall2 (ChiralityConvention.physicalBackground r) := rfl

/-- The reference-wall theorem holds for whichever class the record selects. -/
theorem act_single (X : Fin 3 → Fin 3 → ConcreteFermion.Spin)
    (hX : ∀ a b, ReferenceClassHop.Conserving (X a b))
    (c : Fin 3) (a : ℂ) (r : Fin 2 → ℂ) (b : Fin 3) :
    ReferenceClassHop.act X (wallReference (Pi.single c a) r) b =
      Sum.elim (fun _ => 0)
        ((a * X c b 2 2) • ReferenceClassHop.wall2 (ChiralityConvention.physicalBackground r)) := by
  have hsum : (∑ j, X j b *ᵥ ReferenceClassHop.wall2
      (wallReference (Pi.single c a) r j)) =
      a • (X c b *ᵥ ReferenceClassHop.wall2 (ChiralityConvention.physicalBackground r)) := by
    simp only [wall2_reference, mulVec_smul]
    simp [Pi.single_apply]
  have hsc := CarrierAdmittance.scalar_on_reference (X c b) (hX c b).1 (hX c b).2
    (ReferenceClassHop.wall2 (ChiralityConvention.physicalBackground r))
    (by simp [ReferenceClassHop.wall2_reference])
    (by simp [ReferenceClassHop.wall2_reference])
  have hk : ConcreteFermion.hamiltonian 0 0 *ᵥ wallReference (Pi.single c a) r b = 0 := by
    rw [wallReference, mulVec_smul, ChiralityConvention.physicalBackground_kernel, smul_zero]
  unfold ReferenceClassHop.act
  rw [hk, zero_add, hsum, hsc, smul_smul]

/-- Faithful, nondisturbing recording and reference stationarity exclude direct
exchange out of the selected class on the actual reference-wall spin sector. -/
theorem recorded_wall_stationary {R : Type*} [Fintype R]
    (E : Matrix R (Fin 3) ℂ) (hE : Eᴴ * E = 1)
    (X : Fin 3 → Fin 3 → ConcreteFermion.Spin)
    (hX : ∀ a b, ReferenceClassHop.Conserving (X a b))
    (ψ : Profile) (hψ : ψ ≠ 0) (r : Fin 2 → ℂ) (hr : r ≠ 0)
    (hrec : ∃ ρ, recorded E ψ = product ψ ρ)
    (hstat : ReferenceClassHop.act X (wallReference ψ r) = 0) :
    ∃ c : Fin 3, SingleClass ψ ∧ ∀ b, X c b 2 2 = 0 := by
  have hs := (independent_record_iff E hE ψ hψ).mp hrec
  obtain ⟨c,a,ha,h⟩ := hs
  refine ⟨c, ⟨c,a,ha,h⟩, ?_⟩
  intro b
  have hb := congrFun hstat b
  rw [h, act_single X hX c a r b] at hb
  have hne := ReferenceClassHop.wall2_ne_zero r hr
  have hm : a * X c b 2 2 = 0 := by
    by_contra hn
    apply hne
    funext i
    have hi := congrFun hb (.inr i)
    change (a * X c b 2 2) * ReferenceClassHop.wall2
      (ChiralityConvention.physicalBackground r) i = 0 at hi
    exact (mul_eq_zero.mp hi).resolve_left hn
  exact (mul_eq_zero.mp hm).resolve_left ha

/-- The native-wall attachment needs only preservation of the pure class density;
independence of its faithful record follows from that condition. -/
theorem nondisturbing_wall_stationary {R : Type*} [Fintype R]
    (E : Matrix R (Fin 3) ℂ) (hE : Eᴴ * E = 1)
    (X : Fin 3 → Fin 3 → ConcreteFermion.Spin)
    (hX : ∀ a b, ReferenceClassHop.Conserving (X a b))
    (ψ : Profile) (hψ : ψ ≠ 0) (r : Fin 2 → ℂ) (hr : r ≠ 0)
    (hkeep : reduced (recorded E ψ) = pureDensity ψ)
    (hstat : ReferenceClassHop.act X (wallReference ψ r) = 0) :
    ∃ c : Fin 3, SingleClass ψ ∧ ∀ b, X c b 2 2 = 0 := by
  apply recorded_wall_stationary E hE X hX ψ hψ r hr _ hstat
  exact (independent_record_iff E hE ψ hψ).mpr
    ((nondisturbing_record_iff E hE ψ hψ).mp hkeep)

/-! ## The existing mode-swap maintenance does not supply the tensor-record premise -/

/-- The coherent mode swap maintains every reference profile, including superpositions. -/
theorem swap_fixed (ψ : Profile) :
    BranchMixerSynthesis.exchange *ᵥ Sum.elim ψ ψ = Sum.elim ψ ψ := by
  exact CoherentRecordRestoration.exchange_action ψ ψ

def twoClass : Profile := ![1,-1,0]
def twoEdges : Matrix (Fin 3) (Fin 3) ℂ := !![0,0,1; 0,0,1; 1,1,0]

theorem two_class_ne_zero : twoClass ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num [twoClass] at this

theorem two_edges_hermitian : twoEdges.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [twoEdges, conjTranspose_apply]

/-- Two kept equal exchanges allow an antisymmetric stationary reference. -/
theorem two_class_stationary : twoEdges *ᵥ twoClass = 0 := by
  ext i
  fin_cases i <;> norm_num [twoEdges, twoClass, mulVec, dotProduct, Fin.sum_univ_three]

theorem two_class_not_single : ¬SingleClass twoClass := by
  rintro ⟨r,a,ha,h⟩
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  fin_cases r
  · norm_num [twoClass, Pi.single_apply] at h1
  · norm_num [twoClass, Pi.single_apply] at h0
  · norm_num [twoClass, Pi.single_apply] at h0

/-- A faithful class record rules out this stationary alternative without a data comparison. -/
theorem two_class_record_impossible {R : Type*} [Fintype R]
    (E : Matrix R (Fin 3) ℂ) (hE : Eᴴ * E = 1) :
    ¬∃ ρ, recorded E twoClass = product twoClass ρ := by
  rw [independent_record_iff E hE twoClass two_class_ne_zero]
  exact two_class_not_single

end PMAction.ReferenceClassRecord
