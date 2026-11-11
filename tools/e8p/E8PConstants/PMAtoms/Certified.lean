import PMAtoms.CertifiedEnclosure
import PMAtoms.NuclearRegime
import PMAtoms.HundRule
import E8PConstants.Format
import E8PConstants.PMAtoms.Periodic

/-!
# Nuclear and atomic readouts

Everything printed here is read from `src/`; this module only formats and compares.

* **E8 nuclear mass** — `PMAtoms.certifiedMass` (`NuclearLedger`), the stable-line nuclear ledger.
  It is noncomputable (`π`, `A^(2/3)`, `√`); `PMAtoms.certifiedMass_bounds` proves the computable
  rational enclosure `[cmLo, cmHi]` used here. The enclosure is the exact value of the formula to
  the printed digits, **not** the model's accuracy.
* **Accuracy** — on the stable line the ledger matches measured masses to `4.8 m_e` rms
  (`≈ 0.0026 u`, `≈ 2.5 MeV`); the floor of the bulk terms is `≈ 3.3 m_e` (`PMAtoms/RESIDUALS.md`).
  It is not a mass surface over `(Z, N)`: off the stable line it has no isospin restoring term
  (`PMAtoms.IsospinLedger`).
* **Regime** — `PMAtoms.regimeOf`; `beyond` is past the `Z = 96, N = 152` frontier.
* **Residual** — `E8 − measured` (the sign used in `PMAtoms/RESIDUALS.md`).
* **Measured** — frozen isotope masses (`Periodic`), comparison only.
* **Ground multiplicity** — `PMAtoms.Hund.groundMultiplicity` (Hund's first rule, derived by
  counting, on the Aufbau configuration; the fill order is an input).
-/

namespace E8PConstants
open PMAtoms

/-- Where the enclosure is printed: `A > 4` (the mean-field ledger; `A ≤ 4` uses the line
counts) and inside the deformed frontier (`PMAtoms.deformedFrontierB`). -/
def certifiedDomain (z n : Nat) : Bool := decide (4 < z + n) && PMAtoms.deformedFrontierB z n

/-- Enclosure of `certifiedMass` in `m_e` (`PMAtoms.cmLo`, `cmHi` at 6 digits). -/
def certifiedME (z n : Nat) : Option (Rat × Rat) :=
  if certifiedDomain z n then some (cmLo z n 6, cmHi z n 6) else none

/-- The same enclosure in `u` (`m_e` in `u` is a unit input). -/
def certifiedU (z n : Nat) : Option (Rat × Rat) :=
  (certifiedME z n).map (fun p => (p.1 * electronMassU, p.2 * electronMassU))

def regimeStr (z n : Nat) : String :=
  match PMAtoms.regimeOf z n with
  | .light => "light" | .mid => "mid"
  | .deformedActinide => "deformed" | .beyondFrontier => "beyond"

/-- Frozen measured isotope mass in `u` (comparison only). -/
def isoMass (z a : Nat) : Option Rat :=
  match findIsotopeMass z a with
  | some m => some m
  | none => (extendedIsotopeMassU.find? (fun ((z', a'), _) => z' = z ∧ a' = a)).map (fun (_, m) => m)

/-- `lo..hi` at `p` decimals. -/
def bracket (lo hi : Rat) (p : Nat) : String :=
  s!"{fixedDecimal (lowerScaled lo p) p}..{fixedDecimal (upperScaled hi p) p}"

/-- Signed fixed-point string. -/
def signed (q : Rat) (p : Nat) : String :=
  (if q ≥ 0 then "+" else "") ++ fixedDecimal (lowerScaled q p) p

def isoStr (z a : Nat) : String :=
  match isoMass z a with
  | some m => fixedDecimal (lowerScaled m 6) 6
  | none => "—"

/-- Residual `E8 − measured` in `u`, from the enclosure midpoint. -/
def residualU (z n : Nat) : Option Rat :=
  match certifiedU z n, isoMass z (z + n) with
  | some p, some m => some ((p.1 + p.2) / 2 - m)
  | _, _ => none

/-- Stable-line scatter of the ledger, `4.8 m_e` rms (`PMAtoms/RESIDUALS.md`). -/
def ledgerScatterME : Rat := 48 / 10

/-- Residual in units of the ledger's stable-line scatter (a model z-score, not an experimental
σ: measured masses are known to `~10⁻⁹ u`, so the comparison scale is the model's own scatter). -/
def scatterZ (z n : Nat) : Option Rat :=
  (residualU z n).map (fun r => r / electronMassU / ledgerScatterME)

def absQ (q : Rat) : Rat := if q ≥ 0 then q else -q

/-- `✓` within 1 scatter, `~` within 2, `!` beyond (as in `--audit`). -/
def zGlyph (q : Rat) : String :=
  if absQ q ≤ 1 then "✓" else if absQ q ≤ 2 then "~" else "!"

def zStr (z n : Nat) : String :=
  match scatterZ z n with
  | some q => s!"{signed q 2} {zGlyph q}"
  | none => "—"

def certifiedRow (z a : Nat) : String :=
  let n := a - z
  let meStr := match certifiedME z n with
    | some p => bracket p.1 p.2 4
    | none => "—"
  let uStr := match certifiedU z n with
    | some p => bracket p.1 p.2 6
    | none => "—"
  let (rU, rME) := match residualU z n with
    | some r => (signed r 6, signed (r / electronMassU) 2)
    | none => ("—", "—")
  s!"{z}  {symbol z}  {a}  {n}  {meStr}  {uStr}  {isoStr z a}  {rU}  {rME}  {zStr z n}  {regimeStr z n}"

/-- Standard isotopes (`Z = 1..maxZ`) plus the extended comparison set. -/
def certifiedNuclei (maxZ : Nat) : List (Nat × Nat) :=
  ((List.range maxZ).map (fun i => (i + 1, standardMassNumber.getD i (2 * (i + 1)))))
    ++ extendedIsotopeMassU.map (fun ((z, a), _) => (z, a))

def certifiedTable (maxZ : Nat) : List String :=
  let header :=
    "Z  Sym  A   N   E8 ledger (m_e)          E8 ledger (u)         measured(u)  E8−meas(u)  E8−meas(m_e)  z(scatter)  regime"
  let nuclei := certifiedNuclei maxZ
  let zs := nuclei.filterMap (fun p => scatterZ p.1 (p.2 - p.1))
  let within (t : Rat) := (zs.filter (fun q => absQ q ≤ t)).length
  let summary :=
    s!"{zs.length} nuclei compared:  |z| ≤ 1: {within 1}   |z| ≤ 2: {within 2}   |z| ≤ 3: {within 3}"
  let notes := [
    "E8 ledger = PMAtoms.certifiedMass (stable-line nuclear ledger), printed as its proved rational",
    "  enclosure: the formula's exact value to these digits, not its accuracy.",
    "z(scatter) = (E8 − measured) / 4.8 m_e, the ledger's rms scatter on the stable line",
    "  (≈ 0.0026 u, ≈ 2.5 MeV). A model z-score, not an experimental σ. ✓ |z|≤1, ~ |z|≤2, ! >2.",
    "measured = frozen isotope mass (comparison only). E8−meas uses the enclosure midpoint.",
    "regime = PMAtoms.regimeOf; — = outside the printed domain (A ≤ 4 or past the Z=96, N=152 frontier)." ]
  (header :: nuclei.map (fun p => certifiedRow p.1 p.2)) ++ ("" :: summary :: "" :: notes)

/-- One nucleus, with what each line is. -/
def certifiedNuclide (z n : Nat) : List String :=
  let a := z + n
  match certifiedME z n, certifiedU z n with
  | some p, some q =>
      let head := [
        s!"{symbol z}-{a}  Z={z} N={n}  regime={regimeStr z n}",
        "  E8 ledger mass  (PMAtoms.certifiedMass, stable-line nuclear ledger; exact rational enclosure)",
        s!"    m_e   {bracket p.1 p.2 4}",
        s!"    u     {bracket q.1 q.2 6}" ]
      let cmp := match residualU z n with
        | some r =>
          let rME := r / electronMassU
          [ s!"  measured (frozen isotope mass)   {isoStr z a} u",
            s!"  E8 − measured                    {signed r 6} u  =  {signed rME 2} m_e  =  {signed (rME * electronMassMeV) 3} MeV",
            s!"  ledger scatter (stable line)     ±{fixedDecimal (lowerScaled (ledgerScatterME * electronMassU) 4) 4} u rms  (4.8 m_e)",
            s!"  z (residual / scatter)           {signed (rME / ledgerScatterME) 2} {zGlyph (rME / ledgerScatterME)}" ]
        | none => [ "  measured: no frozen isotope mass for this nucleus" ]
      head ++ cmp ++
        [ "  note: the enclosure is the formula's exact value, not its accuracy; residuals inside the",
          "        scatter are not signals. certifiedMass has no isospin restoring term, so nuclei far",
          "        from the stable line are outside what it describes (PMAtoms.IsospinLedger)." ]
  | _, _ =>
      [ s!"{symbol z}-{a}  Z={z} N={n}  regime={regimeStr z n}",
        "  no enclosure printed: A ≤ 4 (line-count regime) or past the Z=96, N=152 frontier" ]

/-! ## Periodic table -/

/-- `2S+1` from Hund's rule, with the observed term when it differs (`Z ≤ 54`). -/
def multiplicityStr (z : Nat) : String :=
  let g := PMAtoms.Hund.groundMultiplicity z
  match PMAtoms.Hund.observedMultiplicity[z - 1]? with
  | some o => if o == g then toString g else s!"{g}≠{o}"
  | none => toString g

/-- `(matches, compared)` of Hund `2S+1` against the observed terms for `Z = 1..maxZ`. -/
def multiplicityScore (maxZ : Nat) : Nat × Nat :=
  let zs := (List.range maxZ).map (· + 1)
  let cmp := zs.filterMap fun z =>
    (PMAtoms.Hund.observedMultiplicity[z - 1]?).map (· == PMAtoms.Hund.groundMultiplicity z)
  (cmp.count true, cmp.length)

def periodicTable (maxZ : Nat) : List String :=
  let header :=
    "Z   Sym  configuration                  K  L  M  N  2S+1  A   E8 ledger(u)  measured(u)  E8−meas(m_e)  z(scatter)  cloud(eV)  regime"
  let rows := (List.range maxZ).map (fun i =>
    let z := i + 1
    let a := standardMassNumber.getD i (2 * z)
    let n := a - z
    let e8 := match certifiedU z n with
      | some p => fixedDecimal (lowerScaled ((p.1 + p.2) / 2) 6) 6
      | none => "—"
    let res := match residualU z n with
      | some r => signed (r / electronMassU) 2
      | none => "—"
    let shells := String.intercalate "  " ((shellCounts z).map toString)
    s!"{z}  {symbol z}  {configuration z}  |  {shells}  {multiplicityStr z}  {a}  {e8}  {isoStr z a}  {res}  {zStr z n}  {fixedDecimal (lowerScaled (cloudEnergyRat z) 2) 2}  {regimeStr z n}")
  let notes := [
    "configuration = PMAtoms.Aufbau.configuration: capacities 2(2ℓ+1) proved (PMAtoms.Shells); the fill order is a supplied input.",
    s!"2S+1 = PMAtoms.Hund.groundMultiplicity: Hund's first rule derived by counting same-spin pairs (PMAtoms.HundRule); g≠o marks an observed term o that differs; {(multiplicityScore maxZ).1} of {(multiplicityScore maxZ).2} match (misses are Aufbau configuration exceptions).",
    "E8 ledger = midpoint of the PMAtoms.certifiedMass enclosure (— for A ≤ 4); z = residual / 4.8 m_e (the ledger's stable-line scatter).",
    "cloud = hydrogenic electron binding Σ −R∞/n² (PMAtoms.ElectronCloud, certified R∞), no screening.",
    "measured = frozen isotope mass (comparison only)." ]
  (header :: rows) ++ ("" :: notes)

theorem periodicTable_length (maxZ : Nat) : (periodicTable maxZ).length = maxZ + 7 := by
  simp [periodicTable]

end E8PConstants
