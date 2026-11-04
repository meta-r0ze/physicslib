import PMConstants.ReferenceMaintenanceLedger
import PMConstants.ReferenceRestoration

/-!
# Capabilities of the actual carrier operations

An operation's affected carriers, affected carrier axes, and its action on a
selected reference are different task scopes. The existing weak permutation
preserves the axis of each carrier, but moves carriers on every axis. Restricted
to the selected L reference type its affected row is exactly row zero. Colour
fixes that reference but has support on all three other axes and twelve carriers.

These facts price explicit support-based tasks. They do not identify carrier
axes with register rows or choose which task the physical refresh performs.
Hypercharge is diagonal: its relative phase support is examined separately.
-/

noncomputable section
namespace PMConstants.SectorCapabilities
open PMConstants Finset CarrierActions

def row (v : Packet) : Fin 4 := axis (carried v)

def affectedRows (scope : Finset Packet) (op : Equiv.Perm Packet) : Finset (Fin 4) :=
  univ.filter fun r => ∃ v ∈ scope, row v = r ∧ op v ≠ v

def referenceScope : Finset Packet := univ.filter fun v => channelType v = .L

/-- Preserving the axis does not mean fixing the carrier on that axis. -/
theorem weak_preserves_row : ∀ v : Packet, row (weak v) = row v := by decide +kernel

theorem weak_all_rows : affectedRows univ weak = univ := by decide +kernel

theorem weak_reference_row : affectedRows referenceScope weak = {0} := by decide +kernel

theorem reference_is_on_row_zero : ∀ v ∈ referenceScope, row v = 0 := by decide +kernel

theorem weak_moves_every_reference : ∀ v ∈ referenceScope, weak v ≠ v := by decide +kernel

theorem weak_also_moves_spatial : ∃ v : Packet, row v = 1 ∧ weak v ≠ v := by decide +kernel

theorem colour_fixes_reference : ∀ (a b : Fin 3) (v : Packet), v ∈ referenceScope →
    colour a b v = v := by
  have href : ∀ v ∈ referenceScope, v ∉ colourSupport := by decide +kernel
  intro a b v hv
  by_contra hn
  exact href v hv (colour_generators_cover a b v hn)

def colourRows : Finset (Fin 4) :=
  univ.filter fun r => ∃ v ∈ colourSupport, row v = r

theorem colour_row_iff (r : Fin 4) : r ∈ colourRows ↔
    ∃ (a b : Fin 3) (v : Packet), row v = r ∧ colour a b v ≠ v := by
  simp only [colourRows, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨v, hv, hr⟩
    obtain ⟨a, b, hab⟩ := (colour_exists_iff v).mpr hv
    exact ⟨a, b, v, hr, hab⟩
  · rintro ⟨a, b, v, hr, hab⟩
    exact ⟨v, colour_generators_cover a b v hab, hr⟩

theorem colour_spatial_rows : colourRows = univ.erase 0 := by decide +kernel

theorem colour_carrier_count : colourSupport.card = 12 := support_counts.2

/-- Exact reversible task price, conditional on paying 43 per affected row. -/
theorem row_task_minimum (scope : Finset Packet) (op : Equiv.Perm Packet) :
    IsLeast {c | ∃ L, ReferenceMaintenance.Restores (affectedRows scope op) L ∧
      MinimalRefresh.cost (fun _ : Fin 4 => (43 : ℝ)) L = c}
      ((affectedRows scope op).card * 43) := by
  simpa using ReferenceMaintenance.minimum_executable_cost
    (fun _ : Fin 4 => (43 : ℝ)) (fun _ => by norm_num) (affectedRows scope op)

theorem weak_scope_prices :
    (affectedRows univ weak).card * (43 : ℝ) = 172 ∧
      (affectedRows referenceScope weak).card * (43 : ℝ) = 43 := by
  rw [weak_all_rows, weak_reference_row]
  norm_num

/-- Reference-local capability excludes the earlier spatial-to-weak assignment.
The locality of this *task scope* is an explicit premise, not a consequence of
axis preservation by the full weak action. -/
theorem reference_capability_forces_rows (f : Fin 4 → RequirementRows.Sector)
    (hclock : f 0 = .weak)
    (hcap : ∀ r, f r = .weak → r ∈ affectedRows referenceScope weak) :
    ∀ r, f r = if r = 0 then .weak else .hyper := by
  apply RequirementRows.rows_assigned f hclock
  intro r hr
  simpa [weak_reference_row] using hcap r hr

/-- The same support data admits a carrier task instead: eight weak jobs at
payload price, rather than one reference-row job. Scope is a physical input. -/
theorem carrier_task_prices :
    (∑ _v ∈ weakSupport, overhead) = 8 * overhead ∧
      (∑ _v ∈ colourSupport, overhead) = 12 * overhead := by
  simp [support_counts.1, support_counts.2]

theorem colour_carrier_task_minimum :
    IsLeast {c | ∃ L, ReferenceMaintenance.Restores colourSupport L ∧
      MinimalRefresh.cost (fun _ : Packet => overhead) L = c} (12 * overhead) := by
  have h := ReferenceMaintenance.minimum_executable_cost (fun _ : Packet => overhead)
    (fun _ => by norm_num [overhead]) colourSupport
  simpa [support_counts.2] using h

/-- Rational charges from the same table used by the actual diagonal matrix. -/
def Y (c : PacketGaugeActions.Channels) : ℚ :=
  RequirementTable.hyper Hypercharge.standard (RequirementTable.ty (PacketGaugeActions.channelIndex c))

def reference : PacketGaugeActions.Channels := ReferenceAnchor.lepton 0

def relativeY (c : PacketGaugeActions.Channels) : ℚ := Y c - Y reference

def absolutePhaseSupport : Finset PacketGaugeActions.Channels := univ.filter fun c => Y c ≠ 0
def relativePhaseSupport : Finset PacketGaugeActions.Channels := univ.filter fun c => relativeY c ≠ 0

theorem reference_charge : Y reference = -1 := by
  norm_num [Y, reference, ReferenceAnchor.lepton, PacketGaugeActions.channelIndex,
    RequirementTable.ty, RequirementTable.hyper, Hypercharge.standard]

/-- Relative phase removes the common reference phase, not all charged phases. -/
theorem relative_phase_counts : absolutePhaseSupport.card = 15 ∧ relativePhaseSupport.card = 14 := by
  constructor <;> decide +kernel

theorem relative_support_iff (c : PacketGaugeActions.Channels) :
    c ∈ relativePhaseSupport ↔
      RequirementTable.ty (PacketGaugeActions.channelIndex c) ≠ .L := by
  revert c
  decide +kernel

theorem relative_phase_task_minimum :
    IsLeast {c | ∃ L, ReferenceMaintenance.Restores relativePhaseSupport L ∧
      MinimalRefresh.cost (fun _ : PacketGaugeActions.Channels => overhead) L = c}
      (14 * overhead) := by
  have h := ReferenceMaintenance.minimum_executable_cost
    (fun _ : PacketGaugeActions.Channels => overhead)
    (fun _ => by norm_num [overhead]) relativePhaseSupport
  simpa [relative_phase_counts.2] using h

theorem sterile_has_relative_phase :
    Y ReferenceLink.nuR = 0 ∧ relativeY ReferenceLink.nuR = 1 := by
  rw [relativeY, reference_charge]
  norm_num [Y, ReferenceLink.nuR,
    PacketGaugeActions.channelIndex, RequirementTable.ty, RequirementTable.hyper, Hypercharge.standard]

theorem lepton_doublet_relative_phase_zero (s : Fin 2) :
    relativeY (ReferenceAnchor.lepton s) = 0 := by
  rw [relativeY, reference_charge]
  fin_cases s <;> norm_num [Y, ReferenceAnchor.lepton,
    PacketGaugeActions.channelIndex, RequirementTable.ty, RequirementTable.hyper, Hypercharge.standard]

/-- The rational phase difference is exactly twice the difference of the actual
Y/2 generator's diagonal entries. No new charge assignment is introduced. -/
theorem relative_generator_entry (c : PacketGaugeActions.Channels) :
    PacketTraceForm.hyperGen c c - PacketTraceForm.hyperGen reference reference =
      (relativeY c : ℂ) / 2 := by
  simp only [PacketTraceForm.hyperGen, Matrix.smul_apply, smul_eq_mul,
    PacketGaugeActions.charge_table]
  change (1 / 2 : ℂ) * (Y c : ℂ) - (1 / 2 : ℂ) * (Y reference : ℂ) = _
  push_cast [relativeY]
  ring

/-- In this basis hypercharge changes phases, not carrier-label coordinates. -/
theorem hyper_no_off_diagonal (c d : PacketGaugeActions.Channels) (h : c ≠ d) :
    PacketTraceForm.hyperGen c d = 0 := ReferenceRestoration.hyper_isDiag h

end PMConstants.SectorCapabilities
