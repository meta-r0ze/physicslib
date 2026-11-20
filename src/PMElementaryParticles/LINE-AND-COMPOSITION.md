# The line and composition problems

Status: proposals with numerical checks. Nothing here is proved in Lean yet.
The check script is `tools/clock_ring_check.py` (exploration, no data).

## 1. The line problem: what closes the receiver ring

**Reframing.** Task B5 looked for a lattice line through the vacuum vector
`+2e₀`. That was the wrong question. The vacuum vector is the background
*value* at every site, not the direction of the line. `RingReceiver` says
what the ring is: "A periodic identification closes the encoded root line."
The receiver runs on the encoded root line (`LocalController` on `ℤ`,
`OpenHandoff.address_step` along a primitive root), and the ring is that line
closed periodically. The open question is what supplies the closure.

**Proposal: the clock closes it.** The clock's states are the discriminant
group of the E8 clock plane `ℤcu + ℤcv` (`PMSubstrate.ClockPlane`:
`clock_glue`, `w ↦ w₁ − 2w₂ mod 43`). A lattice point reads the clock by
pairing with the plane: `phase(z) = (⟨z,cu⟩ − 2⟨z,cv⟩) mod 43`.

`tools/clock_ring_check.py` finds:

| Count | Value |
| --- | --- |
| E8 roots | 240 |
| roots that change the clock reading | 218 |
| roots that leave it unchanged | 22 (20 orthogonal to the clock plane, plus `±cu`) |
| roots that advance it by exactly `+1` | 22 |
| roots that advance it by exactly `−1` | 22, the negatives of the `+1` roots |
| split of the `+1` roots by `(⟨r,cu⟩, ⟨r,cv⟩)` | 11 with `(1,0)`, 11 with `(−1,−1)` |

A walk that makes one root event per tick, each changing the reading by `±1`,
lives on `ℤ/43`. Because 43 is prime, the closure has exactly 43 sites. The
ring size is the clock period, `n = Δ`. It is not a free choice, and it is
not 3.

**The two streams.** The live stream steps by `+1` roots and the record stream
by `−1` roots. They move in opposite directions, as in `RingReceiver`. An
exchange swaps a packet between them, which reverses its direction.

**Consequences, if this holds:**

- The 3-ring numbers are replaced by 43-ring numbers. One firing site gives
  exactly one registration per period (`tools/bit_ring_rate_check.py`,
  `n = 43`). This is no longer lap arithmetic: the lap is the clock period.
- The Toll floor (at least one registration per period) is met exactly by one
  firing site per period. Margin still excludes trapping between adjacent
  firing sites.
- A ring site is a clock phase. Requests retained per site are requests per
  phase slot. This matches `ClockedRootTrials`, which fires at phases 0 and 1.

**Checks still needed:**

1. *Step weights.* The 22 one-tick roots split 11/11 by their projection onto
   the clock plane. Closure gives equal weight inside each orbit of the
   clock-plane stabilizer. Find the orbits. The weight between the two classes
   is open, in the same way as `SliceHop`'s four words.
2. *Consistency with `AxisHop` / `SliceHop`.* Those modules describe the
   within-tick directional factor, which does not advance the clock. This
   proposal has one root event per tick advancing the clock reading by `±1`.
   State which update the receiver realizes, or how the two fit together.
3. *Clock-silent roots.* The 22 roots with phase 0 do not move a packet around
   the ring. Say what they do: internal or transverse motion.
4. *Lean.* The phase map on roots, the counts above, and the statement that the
   receiver ring with one-tick root steps is `ℤ/Δ`.

## 2. The composition problem: the nested rules on the machine

The three rules (`PM-3-Nested/paper/2_nested_persistence.tex`), stated on the
automaton:

- **Capacity Partitioning.** Per period, the protocols' registrations plus
  interface overhead fit within the ring's capacity. This is a necessary
  budget, the same shape as the Capacity pillar.
- **Reversible Encoding.** The joint encoding must be injective. The paper's
  relational form: values relative to a reference `x_o`, together with the
  reference value itself, because "dropping the reference value merges
  distinct constant configurations."
- **Impedance Matching.** On the machine this is the certified converter. The
  pass and flip probabilities `cos²(x/2)` and `sin²(x/2)` are the transmission
  `T` and reflection `r²` of the paper's ledger `Pr² + PT = P`. Reflected load
  is registrations. Admissibility `Pr² ≤ B` is the Margin reserve. At `x = π`
  reflection is total, so a reserve is required.

**A composite state.** `k` protocols on one 43-ring, sharing the clock and the
vacuum (`+2e₀`, task B3), each with its own packet. The firing pattern is
joint, and Toll adds over packets (`record_step_identity` per ring).

**The colour question (hypothesis).** A colour label's record is colour-blind
(`record_colour`), but the packet itself still carries its colour
(`channelCode_bijective`). So injectivity holds. The difficulty is Map's
*reference*: a comparison needs a reference **state** at the site. The vacuum
`+2e₀` is colour-blind. The colour reference is the set `{e₁, e₂, e₃}`, which
no single basis vector at a site can hold. That leaves two options:

- **(a) A single-site colour-symmetric reference** `(e₁+e₂+e₃)/√3`. A colour
  axis compared with it has overlap `1/√3`. The mismatch probability is
  `(1 − 1/√3)/2 ≈ 0.211`, at angle `x = arccos(1/√3) ≈ 54.74°`. That is not
  `π`. It would be the first source of a partial comparison phase for colour
  labels, if the substrate admits that state.
- **(b) A colour-complete composite.** One member on each colour axis. The
  members' axes are `{e₁, e₂, e₃}`, which is the colour reference set itself,
  so the composite carries its own reference. Members compare relationally
  (`x_i − x_o`). The configurations merged by dropping a global reference are
  global colour relabelings, which are substrate symmetries
  (`PacketGaugeActions.permuteColour`). If those are not physical
  distinctions, nothing is lost.

**Test.** Apply the pillars and least Toll to (a) a single colour protocol
with the superposed reference and (b) the colour-complete composite. Do not
assume confinement. Lepton protocols compare against `+2e₀` exactly, so they
need neither option.

## 3. What this unblocks

- Re-running the pillar survivors on the 43-ring.
- Shared vs composite backgrounds, and whether colour protocols persist alone.
- Triality and generation costs on a ring of the right size.
- A possible source of cost differences between protocols: comparison angles
  other than `π`, from option (a).
