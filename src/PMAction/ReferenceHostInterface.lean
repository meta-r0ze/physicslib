import PMAction.TensorKernel
import PMAction.ReferenceRootRecord
import PMAction.Machine.RecordSupply
import PMAction.ReferenceNodeBoundary

/-!
# Reference host interface: record transport is distinct from record writing

The supplied native maintenance exports each arriving live value into the
outgoing record stream (`RecordSupply.disturbance_exported`). This module tests
when a node observable is unchanged by record motion. An independent unitary
record factor preserves every live observable, even on entangled inputs.
The actual native routing can act on such a separate bank, but neither that
bank allocation nor the node-current identification is selected here. Moreover,
two of the proposed even class markers are fixed by this routing: independence
alone does not prove successful export or continuing blank supply.
`ReferenceMarkerExport` supplies a separate root-word-conjugated circuit that
routes all three markers; its physical schedule and source remain inputs.

A faithful class write is a joint interaction, not record-only transport. Using
the actual even carrier markers of `ReferenceRootRecord`, its exact compressed
readout deletes cross-class entries. It preserves a supplied observable exactly
when that observable is class-block diagonal. Subsequent independent unitary
export does not undo or add to this change. A node transfer with nonzero
cross-class entries therefore fails the all-input no-feedback test for this writer.

The existing root maintenance exchanges direct-sum live/record modes of one
carrier bank; it does not preserve the live-port projector. Thus two streams
are not automatically independent tensor factors. No fresh record supply,
primitive price, electrical boundary condition or Hamiltonian rate is inferred
from these observable identities. In particular record-only no-feedback is not
by itself the zero-load premise of `ReferenceNodeBoundary`.
-/
noncomputable section
namespace PMAction.ReferenceHostInterface
open Matrix
open scoped Kronecker

section Transport
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

/-- Operator-level no-feedback, hence valid for arbitrary joint preparations. -/
theorem record_transport (J : Matrix L L ℂ) (U : Matrix R R ℂ)
    (hU : U ∈ unitary (Matrix R R ℂ)) :
    ((1 : Matrix L L ℂ) ⊗ₖ U)ᴴ * (J ⊗ₖ (1 : Matrix R R ℂ)) *
      ((1 : Matrix L L ℂ) ⊗ₖ U) = J ⊗ₖ (1 : Matrix R R ℂ) := by
  have hu : Uᴴ * U = 1 := hU.1
  simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one, hu]

/-- The complete live quadratic readout is unchanged, without a product-state hypothesis. -/
theorem record_readout (J : Matrix L L ℂ) (U : Matrix R R ℂ)
    (hU : U ∈ unitary (Matrix R R ℂ)) (ψ : L × R → ℂ) :
    dotProduct (star (((1 : Matrix L L ℂ) ⊗ₖ U) *ᵥ ψ))
        ((J ⊗ₖ (1 : Matrix R R ℂ)) *ᵥ (((1 : Matrix L L ℂ) ⊗ₖ U) *ᵥ ψ)) =
      dotProduct (star ψ) ((J ⊗ₖ (1 : Matrix R R ℂ)) *ᵥ ψ) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec,
    record_transport J U hU]

/-- Export after any admitted write/encoding adds no further live-observable change. -/
theorem export_compression {N : Type*} [Fintype N]
    (W : Matrix (L × R) N ℂ) (J : Matrix L L ℂ) (U : Matrix R R ℂ)
    (hU : U ∈ unitary (Matrix R R ℂ)) :
    (((1 : Matrix L L ℂ) ⊗ₖ U) * W)ᴴ * (J ⊗ₖ (1 : Matrix R R ℂ)) *
        (((1 : Matrix L L ℂ) ⊗ₖ U) * W) =
      Wᴴ * (J ⊗ₖ (1 : Matrix R R ℂ)) * W := by
  calc
    _ = Wᴴ * (((1 : Matrix L L ℂ) ⊗ₖ U)ᴴ * (J ⊗ₖ (1 : Matrix R R ℂ)) *
        ((1 : Matrix L L ℂ) ⊗ₖ U)) * W := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [record_transport J U hU]

/-- Supplied actual carrier routing on a separate record bank passes the test. -/
theorem native_bank_transport {X : Type*} [Fintype X] [DecidableEq X]
    (o : X) (e : Equiv.Perm X) (J : Matrix L L ℂ) :
    ((1 : Matrix L L ℂ) ⊗ₖ (NativeCarrierProtocol.lookup o e).permMatrix ℂ)ᴴ *
      (J ⊗ₖ (1 : Matrix (X × NativeCarrierProtocol.C) (X × NativeCarrierProtocol.C) ℂ)) *
      ((1 : Matrix L L ℂ) ⊗ₖ (NativeCarrierProtocol.lookup o e).permMatrix ℂ) =
      J ⊗ₖ (1 : Matrix (X × NativeCarrierProtocol.C) (X × NativeCarrierProtocol.C) ℂ) :=
  record_transport J _ (CarrierResponse.perm_unitary _)

end Transport

section Writer
variable {L : Type*} [Fintype L] [DecidableEq L]
abbrev C := VectorEvenFrame.C

/-- Isometric class write into the actual even carrier markers, with a supplied clean bank. -/
def writer (cls : L → Fin 3) : Matrix (L × C) L ℂ :=
  fun p l => if p.1 = l then VectorEvenFrame.marker (cls l).succ p.2 else 0

/-- The columns are exactly the native class-controlled blank-to-marker operation. -/
theorem writer_action (cls : L → Fin 3) (ψ : L → ℂ) :
    writer cls *ᵥ ψ = (ReferenceRootRecord.controlled cls).permMatrix ℂ *ᵥ
      ReferenceRootRecord.prepared ψ := by
  rw [ReferenceRootRecord.controlled_action]
  ext p
  simp [writer, mulVec, dotProduct, mul_comm]

/-- Exact effective observable after the class record is retained and unread. -/
def classBlock (cls : L → Fin 3) (J : Matrix L L ℂ) : Matrix L L ℂ :=
  fun i j => if cls i = cls j then J i j else 0

/-- Class-write compression, using the actual carrier marker Gram matrix. -/
theorem writer_observable (cls : L → Fin 3) (J : Matrix L L ℂ) :
    (writer cls)ᴴ * (J ⊗ₖ (1 : Matrix C C ℂ)) * writer cls = classBlock cls J := by
  ext i j
  simp [mul_apply, conjTranspose_apply, Fintype.sum_prod_type, writer,
    apply_ite, Matrix.one_apply]
  calc
    _ = J i j * (∑ x, VectorEvenFrame.marker (cls j).succ x *
        star (VectorEvenFrame.marker (cls i).succ x)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      change star (VectorEvenFrame.marker (cls i).succ x) * J i j *
        VectorEvenFrame.marker (cls j).succ x =
        J i j * (VectorEvenFrame.marker (cls j).succ x *
          star (VectorEvenFrame.marker (cls i).succ x))
      ring
    _ = _ := by
      rw [ReferenceRootRecord.marker_gram]
      by_cases h : cls i = cls j
      · simp [classBlock, h]
      · simp [classBlock, h, Ne.symm h]

/-- Recording retains the complete joint amplitude; the change is in live-only readout. -/
theorem writer_isometry (cls : L → Fin 3) : (writer cls)ᴴ * writer cls = 1 := by
  have h := writer_observable cls (1 : Matrix L L ℂ)
  rw [one_kronecker_one, Matrix.mul_one] at h
  rw [h]
  ext i j
  by_cases hij : i = j
  · subst j; simp [classBlock]
  · simp [classBlock, hij]

/-- Full observable preservation requires no cross-class transfer matrix entries. -/
theorem writer_preserves_iff (cls : L → Fin 3) (J : Matrix L L ℂ) :
    (writer cls)ᴴ * (J ⊗ₖ (1 : Matrix C C ℂ)) * writer cls = J ↔
      ∀ i j, cls i ≠ cls j → J i j = 0 := by
  rw [writer_observable]
  constructor
  · intro h i j hij
    have he := congrFun (congrFun h i) j
    simpa [classBlock, hij] using he.symm
  · intro h
    ext i j
    by_cases hij : cls i = cls j
    · simp [classBlock, hij]
    · simp [classBlock, hij, h i j hij]

/-- Independent transport after the write preserves exactly its compressed readout. -/
theorem exported_writer_observable (cls : L → Fin 3) (J : Matrix L L ℂ)
    (U : Matrix C C ℂ) (hU : U ∈ unitary (Matrix C C ℂ)) :
    (((1 : Matrix L L ℂ) ⊗ₖ U) * writer cls)ᴴ *
        (J ⊗ₖ (1 : Matrix C C ℂ)) * (((1 : Matrix L L ℂ) ⊗ₖ U) * writer cls) =
      classBlock cls J := by
  rw [export_compression _ J U hU, writer_observable]

/-- A nonzero cross-class transfer fails this writer's all-input no-feedback contract. -/
theorem class_transfer_changes (cls : L → Fin 3) (J : Matrix L L ℂ)
    (i j : L) (hc : cls i ≠ cls j) (hJ : J i j ≠ 0) :
    (writer cls)ᴴ * (J ⊗ₖ (1 : Matrix C C ℂ)) * writer cls ≠ J := by
  intro h
  exact hJ ((writer_preserves_iff cls J).mp h i j hc)

/-- Two-port conserving response on a chosen pair of recorded modes.
The conductance can be the derived `ReferenceNodeBoundary.series a b`.
This is an operator witness on that factor, not a native factor identification. -/
def pairLaplacian (g : ℝ) (i j : L) : Matrix L L ℂ := fun n m =>
  (g : ℂ) * ((if n = i then 1 else 0) - (if n = j then 1 else 0)) *
    ((if m = i then 1 else 0) - (if m = j then 1 else 0))

/-- The row gives the same two-terminal current law as the scalar series network. -/
theorem pair_current (g : ℝ) (i j : L) (hij : i ≠ j) (v : L → ℂ) :
    (pairLaplacian g i j *ᵥ v) i = (g : ℂ)*(v i-v j) := by
  simp [pairLaplacian, mulVec, dotProduct, hij, mul_sub, sub_mul,
    Finset.sum_sub_distrib]

/-- A nonzero two-port response across recorded classes is changed by the class write. -/
theorem pair_write_changes (cls : L → Fin 3) (g : ℝ) (hg : g ≠ 0)
    (i j : L) (hc : cls i ≠ cls j) :
    (writer cls)ᴴ * (pairLaplacian g i j ⊗ₖ (1 : Matrix C C ℂ)) * writer cls ≠
      pairLaplacian g i j := by
  have hij : i ≠ j := fun h => hc (congrArg cls h)
  apply class_transfer_changes cls _ i j hc
  simp [pairLaplacian, hij, Ne.symm hij, hg]

/-- In particular the positive, unloaded series response cannot be treated as
unaffected by this writer on the same class factor. -/
theorem series_write_changes (cls : L → Fin 3) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (i j : L) (hc : cls i ≠ cls j) :
    (writer cls)ᴴ * (pairLaplacian (ReferenceNodeBoundary.series a b) i j ⊗ₖ
        (1 : Matrix C C ℂ)) * writer cls ≠
      pairLaplacian (ReferenceNodeBoundary.series a b) i j := by
  apply pair_write_changes cls _ _ i j hc
  unfold ReferenceNodeBoundary.series
  exact ne_of_gt (by positivity)

/-- The criterion attaches to all actual glue-class carriers, without a class-profile encoding. -/
theorem native_writer_preserves_iff (J : Matrix ReferenceRootRecord.Native ReferenceRootRecord.Native ℂ) :
    (writer Sigma.fst)ᴴ * (J ⊗ₖ (1 : Matrix C C ℂ)) * writer Sigma.fst = J ↔
      ∀ n m, n.1 ≠ m.1 → J n m = 0 := writer_preserves_iff Sigma.fst J

end Writer

/-! ## Does the existing stream actually export the proposed class markers? -/

section MarkerRouting
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The standard native stream fixes every amplitude supported on unused carrier labels. -/
theorem unused_bank_fixed (o : X) (e : Equiv.Perm X) (ψ : X × C → ℂ)
    (hψ : ∀ x j, ψ (x, ActualRootRepair.label j) = 0) :
    (NativeCarrierProtocol.lookup o e).permMatrix ℂ *ᵥ ψ = ψ := by
  rw [permMatrix_mulVec]
  ext p
  rcases p with ⟨x,v⟩
  change ψ (NativeCarrierProtocol.lookup o e (x,v)) = ψ (x,v)
  by_cases hv : v ∈ Set.range ActualRootRepair.label
  · obtain ⟨j,rfl⟩ := hv
    rw [NativeCarrierProtocol.lookup_label]
    change ψ ((NativeCarrierProtocol.portStep o e (x,j)).1,
        ActualRootRepair.label (NativeCarrierProtocol.portStep o e (x,j)).2) =
      ψ (x, ActualRootRepair.label j)
    rw [hψ, hψ]
  · rw [NativeCarrierProtocol.lookup_unused o e x v hv]

/-- The second and third spatial markers use none of the stream's moving labels.
The indices come from the existing class-to-marker encoding, not a fitted count. -/
theorem class_marker_inactive : ∀ (i : Fin 3), i ≠ 0 → ∀ j : ActualRootRepair.Ports,
    VectorEvenFrame.indicator (ActualRootRepair.label j) i.succ = 0 := by
  decide +kernel

def placedMarker (x : X) (i : Fin 4) : X × C → ℂ :=
  fun p => if p.1 = x then VectorEvenFrame.marker i p.2 else 0

/-- Two of the three proposed class markers remain at their original site forever
under the existing native stream, regardless of the routing or coupling site. -/
theorem two_markers_stuck (o : X) (e : Equiv.Perm X) (x : X) (i : Fin 3) (hi : i ≠ 0) :
    (NativeCarrierProtocol.lookup o e).permMatrix ℂ *ᵥ placedMarker x i.succ =
      placedMarker x i.succ := by
  apply unused_bank_fixed
  intro y j
  simp [placedMarker, VectorEvenFrame.marker_apply, class_marker_inactive i hi j]

/-- Repeating the supplied native routing does not free the occupied marker cell. -/
theorem two_markers_stuck_iterates (o : X) (e : Equiv.Perm X) (x : X)
    (i : Fin 3) (hi : i ≠ 0) (t : ℕ) :
    ((NativeCarrierProtocol.lookup o e).permMatrix ℂ)^t *ᵥ placedMarker x i.succ =
      placedMarker x i.succ := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', ← mulVec_mulVec, ih, two_markers_stuck o e x i hi]

end MarkerRouting

/-! ## The shared native bank is a different interface -/

def livePort : Matrix ActualRootRepair.Ports ActualRootRepair.Ports ℂ := fromBlocks 1 0 0 0
def recordPort : Matrix ActualRootRepair.Ports ActualRootRepair.Ports ℂ := fromBlocks 0 0 0 1

/-- The native maintenance exchange swaps these port observables; it is not record-only. -/
theorem exchange_live_port :
    BranchMixerSynthesis.exchangeᴴ * livePort * BranchMixerSynthesis.exchange = recordPort := by
  simp [BranchMixerSynthesis.exchange, livePort, recordPort,
    fromBlocks_conjTranspose, fromBlocks_multiply]

/-- Direct attachment to the actual carrier-root encoding. -/
theorem actual_root_live_port :
    (ActualRootRepair.root.permMatrix ℂ * ActualRootRepair.embedding)ᴴ *
        (ActualRootRepair.embedding * livePort * ActualRootRepair.embeddingᴴ) *
        (ActualRootRepair.root.permMatrix ℂ * ActualRootRepair.embedding) = recordPort := by
  rw [ActualRootRepair.intertwining]
  simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ActualRootRepair.embeddingᴴ ActualRootRepair.embedding,
    ActualRootRepair.isometry]
  simp only [Matrix.one_mul]
  rw [← Matrix.mul_assoc ActualRootRepair.embeddingᴴ ActualRootRepair.embedding,
    ActualRootRepair.isometry, Matrix.one_mul]
  rw [← Matrix.mul_assoc, exchange_live_port]

/-- The actual shared-bank coupling fails preservation of the live-port observable. -/
theorem actual_root_changes_live_port :
    (ActualRootRepair.root.permMatrix ℂ * ActualRootRepair.embedding)ᴴ *
        (ActualRootRepair.embedding * livePort * ActualRootRepair.embeddingᴴ) *
        (ActualRootRepair.root.permMatrix ℂ * ActualRootRepair.embedding) ≠ livePort := by
  rw [actual_root_live_port]
  intro h
  have hh := congrFun (congrFun h (.inl 0)) (.inl 0)
  norm_num [recordPort, livePort] at hh

end PMAction.ReferenceHostInterface
