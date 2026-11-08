# VEV factor ledger

The VEV is written as four independent factors plus the mass anchor:

```text
v = slotCount · α⁻¹ · (1 + α/D_eff) · (1 − Y/(σ−χ)) · m_e
```

`VevLedger.vevLedger_eq_vev` proves this is exactly the current `vev` formula.

## Factors

| factor | value / expression | status |
|---|---|---|
| `slotCount` | `χΔ² − (ν + DΔ) = 3510` | derived count; premises: channels are frame, wires carry no boundary area |
| handoff | `α⁻¹` | exact under the event calibration `toll·m = 1/(4παN_sys)`; premise: electron maintenance is one repair |
| repair | `1 + α/D_eff` | first-order repair form; `exp` and iterated forms excluded by the Fermi window |
| boundary | `D_eff = D + χ/(4π)` | `χ/(4π)` is unique among `D + a/(bπ)`, `b ≤ 200` |
| margin denominator | `σ − χ = 3` | data allow 3 or 4; 3 selected by the `D−1=3` axes orthogonal to the reference |
| mass anchor | `m_e` | dimensionful input; electron is the unique charged reference carrier |

## What is proved

```lean
slotCount_eq : slotCount = 3510
vevLedger_eq_vev : vevLedger α me = vev α me
noiseDenominator_eq_orthogonal : σ − χ = D − 1
boundaryDenominator : χ/(Dπ) = 2/(4π)
```

## What remains supplied

```text
channels counted as frame, not payload
wires carry no boundary area
electron maintenance is exactly one repair
noise lands on the D−1 axes orthogonal to the reference
the mass unit m_e
```

The Fermi window constrains these choices but does not derive them from bare
persistence.  This is the honest boundary of the VEV derivation.
