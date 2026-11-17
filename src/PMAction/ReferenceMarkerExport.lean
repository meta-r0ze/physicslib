import PMAction.ReferenceHostInterface

/-!
# A native-word export circuit for the three even class markers

The standard stream has one live axis and one record axis. Conjugating its
transport factor by existing simple-root words brings each spatial marker to
that record axis in turn. Three passes export all three spatial markers; the
blank axis is transported oppositely three times. This is a reversible schedule
on the existing carrier labels, not three copies of the bank or an erasure.

The neighbour routing and separate-bank allocation are supplied. Root words
certify the relabelings; their implementation price, schedule selection and
duration are not derived. The three passes count the three existing marker
channels, not a physical tick or a fitted rate ratio. Blank renewal still needs
a matching incoming blank and no incoming occupied tags at the local port.
-/
noncomputable section
namespace PMAction.ReferenceMarkerExport
open Matrix VectorEvenFrame
open scoped Kronecker

/-- Signed lookup displacement of the existing two-stream transport factor. -/
def lane (v : C) : ℤ :=
  if indicator v 0 ≠ 0 then -1 else if indicator v 1 ≠ 0 then 1 else 0

lemma lane_label : ∀ j : ActualRootRepair.Ports,
    lane (ActualRootRepair.label j) = Sum.elim (fun _ => -1) (fun _ => 1) j := by
  decide +kernel

lemma lane_unused : ∀ v : C, v ∉ Set.range ActualRootRepair.label → lane v = 0 := by
  decide +kernel

/-- Move a chosen spatial marker to the stream's record axis, fixing the blank axis. -/
def rename (i : Fin 3) : Equiv.Perm C := CarrierEvents.permute 0 (Equiv.swap 1 i.succ)

def renameWord (i : Fin 3) : List (Fin 4) :=
  if i = 0 then [] else word 1 ++ word i.succ ++ word 1

/-- Each relabeling is a word of the existing D4 simple-root carrier reflections. -/
theorem rename_root_word : ∀ (i : Fin 3) (v : C),
    ((renameWord i).map (CarrierWeyl.simple 0)).prod v = rename i v := by
  decide +kernel

lemma rename_twice : ∀ (i : Fin 3) (v : C), rename i (rename i v) = v := by
  decide +kernel

/-- The resulting displacement is determined by which of the four carrier axes is occupied. -/
def exportLane (v : C) : ℤ := if indicator v 0 ≠ 0 then -3 else 1

lemma lane_sum : ∀ v : C,
    lane (rename 0 v) + lane (rename 1 v) + lane (rename 2 v) = exportLane v := by
  decide +kernel

lemma spatial_lane : ∀ (i : Fin 3) (v : C),
    indicator v i.succ ≠ 0 → exportLane v = 1 := by
  decide +kernel

lemma blank_lane : ∀ v : C, indicator v 0 ≠ 0 → exportLane v = -3 := by
  decide +kernel

section Routing
variable {X : Type*}

/-- Mathematical description of a carrier-dependent routing; the circuit below realizes it. -/
def routed (e : Equiv.Perm X) (q : C → ℤ) : Equiv.Perm (X × C) where
  toFun p := ((e ^ q p.2) p.1, p.2)
  invFun p := ((e ^ q p.2)⁻¹ p.1, p.2)
  left_inv p := Prod.ext ((e ^ q p.2).symm_apply_apply p.1) rfl
  right_inv p := Prod.ext ((e ^ q p.2).apply_symm_apply p.1) rfl

/-- The existing native transport factor, without executing the on-site maintenance coupling. -/
def nativeStream (e : Equiv.Perm X) : Equiv.Perm (X × C) :=
  (NativeCarrierProtocol.stream e).viaEmbedding NativeCarrierProtocol.labels

theorem native_stream_eq (e : Equiv.Perm X) : nativeStream e = routed e lane := by
  apply Equiv.ext
  rintro ⟨x,v⟩
  by_cases hv : v ∈ Set.range ActualRootRepair.label
  · obtain ⟨j,rfl⟩ := hv
    change nativeStream e (NativeCarrierProtocol.labels (x,j)) = _
    rw [nativeStream, Equiv.Perm.viaEmbedding_apply]
    rcases j with j | j <;>
      simp [NativeCarrierProtocol.stream, NativeCarrierProtocol.labels, routed, lane_label] <;> rfl
  · have hn : (x,v) ∉ Set.range (NativeCarrierProtocol.labels (X := X)) := by
      rintro ⟨⟨y,j⟩,h⟩
      exact hv ⟨j, congrArg Prod.snd h⟩
    rw [nativeStream, Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hn]
    simp [routed, lane_unused v hv]

lemma routed_trans (e : Equiv.Perm X) (q r : C → ℤ) :
    (routed e q).trans (routed e r) = routed e (fun v => q v + r v) := by
  apply Equiv.ext
  rintro ⟨x,v⟩
  change ((e ^ r v) ((e ^ q v) x), v) = ((e ^ (q v + r v)) x, v)
  rw [← Equiv.Perm.mul_apply, ← _root_.zpow_add, add_comm (r v) (q v)]

def relabel (i : Fin 3) : Equiv.Perm (X × C) :=
  Equiv.prodCongr (Equiv.refl X) (rename i)

/-- Root-word conjugation makes the old record channel transport marker i. -/
def pass (e : Equiv.Perm X) (i : Fin 3) : Equiv.Perm (X × C) :=
  (relabel i).trans ((nativeStream e).trans (relabel i))

theorem pass_eq (e : Equiv.Perm X) (i : Fin 3) :
    pass e i = routed e (fun v => lane (rename i v)) := by
  rw [pass, native_stream_eq]
  apply Equiv.ext
  rintro ⟨x,v⟩
  change ((e ^ lane (rename i v)) x, rename i (rename i v)) =
    ((e ^ lane (rename i v)) x, v)
  rw [rename_twice]

/-- One macrocycle visits the three existing spatial marker channels once. -/
def exportCycle (e : Equiv.Perm X) : Equiv.Perm (X × C) :=
  ((pass e 0).trans (pass e 1)).trans (pass e 2)

/-- All label amplitudes, including the blank, are retained by this explicit circuit. -/
theorem export_eq (e : Equiv.Perm X) : exportCycle e = routed e exportLane := by
  rw [exportCycle, pass_eq, pass_eq, pass_eq, routed_trans, routed_trans]
  congr 1
  funext v
  exact lane_sum v

end Routing

section Amplitudes
variable {X : Type*} [Fintype X] [DecidableEq X]

theorem export_unitary (e : Equiv.Perm X) :
    (exportCycle e).permMatrix ℂ ∈ unitary (Matrix (X × C) (X × C) ℂ) :=
  CarrierResponse.perm_unitary _

/-- An entire stream of one marker type; amplitudes need not be normalized or positive. -/
def markerField (i : Fin 4) (f : X → ℂ) : X × C → ℂ :=
  fun p => f p.1 * marker i p.2

/-- Exact amplitude action on any marker stream with a fixed displacement on its support. -/
theorem routed_marker (e : Equiv.Perm X) (q : C → ℤ) (i : Fin 4) (k : ℤ)
    (hk : ∀ v, indicator v i ≠ 0 → q v = k) (f : X → ℂ) :
    (routed e q).permMatrix ℂ *ᵥ markerField i f =
      markerField i (fun x => f ((e ^ k) x)) := by
  rw [permMatrix_mulVec]
  ext ⟨x,v⟩
  by_cases hv : indicator v i = 0
  · simp [markerField, marker_apply, routed, hv]
  · simp [markerField, routed, hk v hv]

/-- All three class-marker streams now move, without changing their encoded class. -/
theorem export_spatial (e : Equiv.Perm X) (i : Fin 3) (f : X → ℂ) :
    (exportCycle e).permMatrix ℂ *ᵥ markerField i.succ f =
      markerField i.succ (fun x => f (e x)) := by
  rw [export_eq]
  simpa using routed_marker e exportLane i.succ 1 (spatial_lane i) f

/-- A localized tag leaves its site along the record direction; the encoded class is unchanged. -/
theorem localized_export (e : Equiv.Perm X) (i : Fin 3) (x : X) :
    (exportCycle e).permMatrix ℂ *ᵥ ReferenceHostInterface.placedMarker x i.succ =
      ReferenceHostInterface.placedMarker (e.symm x) i.succ := by
  have h := export_spatial e i (fun y => if y = x then (1 : ℂ) else 0)
  have hf (y : X) : markerField i.succ (fun z => if z = y then (1 : ℂ) else 0) =
      ReferenceHostInterface.placedMarker y i.succ := by
    funext p
    simp [markerField, ReferenceHostInterface.placedMarker, ite_mul]
  simpa only [← e.eq_symm_apply, hf] using h

/-- The compensating blank stream is retained and moves oppositely over the three passes. -/
theorem export_blank (e : Equiv.Perm X) (f : X → ℂ) :
    (exportCycle e).permMatrix ℂ *ᵥ markerField 0 f =
      markerField 0 (fun x => f ((e ^ (-3 : ℤ)) x)) := by
  rw [export_eq]
  exact routed_marker e exportLane 0 (-3) blank_lane f

/-- One incoming blank stream and the three outgoing class-tag streams share the same bank. -/
def bankField (blank : X → ℂ) (tags : X → Fin 3 → ℂ) : X × C → ℂ :=
  markerField 0 blank + ∑ i : Fin 3, markerField i.succ (fun x => tags x i)

theorem export_bank (e : Equiv.Perm X) (blank : X → ℂ) (tags : X → Fin 3 → ℂ) :
    (exportCycle e).permMatrix ℂ *ᵥ bankField blank tags =
      bankField (fun x => blank ((e ^ (-3 : ℤ)) x)) (fun x i => tags (e x) i) := by
  simp only [bankField, mulVec_add, mulVec_sum, export_blank, export_spatial]

/-- Local blank renewal has explicit incoming boundary data; no free reset is inferred. -/
theorem clean_arrival (e : Equiv.Perm X) (o : X) (blank : X → ℂ)
    (tags : X → Fin 3 → ℂ) (a : ℂ)
    (hb : blank ((e ^ (-3 : ℤ)) o) = a) (ht : ∀ i, tags (e o) i = 0) (v : C) :
    ((exportCycle e).permMatrix ℂ *ᵥ bankField blank tags) (o,v) = a * marker 0 v := by
  rw [export_bank]
  simp only [bankField, Pi.add_apply, Finset.sum_apply, markerField]
  rw [hb]
  simp only [ht, zero_mul, Finset.sum_const_zero, add_zero]

/-- On an allocated independent bank this complete exportCycle preserves every live observable. -/
theorem no_feedback {L : Type*} [Fintype L] [DecidableEq L]
    (e : Equiv.Perm X) (J : Matrix L L ℂ) :
    ((1 : Matrix L L ℂ) ⊗ₖ (exportCycle e).permMatrix ℂ)ᴴ *
        (J ⊗ₖ (1 : Matrix (X × C) (X × C) ℂ)) *
        ((1 : Matrix L L ℂ) ⊗ₖ (exportCycle e).permMatrix ℂ) =
      J ⊗ₖ (1 : Matrix (X × C) (X × C) ℂ) :=
  ReferenceHostInterface.record_transport J _ (export_unitary e)

end Amplitudes
end PMAction.ReferenceMarkerExport
