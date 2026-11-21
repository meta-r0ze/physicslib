# PMElementaryParticles — open work

Current detail is in [HISTORY.md](HISTORY.md). This file is the open list only.

## Line problem — proposed, awaiting compile

See [LINE-AND-COMPOSITION.md](LINE-AND-COMPOSITION.md). The clock closes the
receiver ring. One root event per tick changes the E8 clock reading by `±1`,
so the ring has exactly `Δ = 43` sites (`PMKAutomaton/ClockRing.lean`, not yet
compiled). `SliceHop` agrees once its D4 is placed with its clock axis on the
clock plane, and the six forward tick steps then carry equal weight.
Remaining:

- compile-check `ClockRing.lean`;
- replace `sectorBasis` with an aligned placement, or state the alignment as a
  named hypothesis, and recheck the modules that use its coordinates;
- identify `RingReceiver`'s site index with `clockReading` (`n = Δ`);
- replace the 3-ring registration counts with 43-ring results.

## Composition problem — rules written, awaiting compile

See [LINE-AND-COMPOSITION.md](LINE-AND-COMPOSITION.md). Two of the nested
rules are written on the machine: Impedance Matching (`ImpedanceLedger`; Toll
needs a Margin reserve) and Reversible Encoding (`RecordEncoding`). The colour
reference is one site state, so it does not force composites. The "colour
reference needs a triple" hypothesis is withdrawn. Remaining:

- compile-check `PersistenceMechanics/ImpedanceMatching.lean`,
  `ReversibleEncoding.lean`, `ImpedanceLedger.lean` and `RecordEncoding.lean`;
- compile-check `PersistenceMechanics/CapacityPartitioning.lean` and
  `CapacityLedger.lean` (all three nested rules are now written);
- the vacuum choice (lepton `+e₀` or colour-symmetric) is open again; use the
  P4 shared-vacuum tables;
- generations: the aligned clock breaks triality. The coset signatures are
  vector (7, 7, 2), spinor (4, 4, 0) and conjugate spinor (4, 4, 8), counting
  one-tick `+1`, one-tick `−1` and clock-silent roots
  (`tools/generation_clock_signature.py`). Next: match the cosets to the glue
  address `g`, and state the dynamics rule that turns step counts into cost per
  period.

## Full-ring Lean spectrum

`CoherentRing.ringTick_unitary` certifies the full-firing coherent tick for
every `n`; `Dispersion.planeWave` and `planeWave_exp_period` define the plane
wave and prove `exp(i k n)=1`. The block action, explicit `M(k)`, trace/det
and eigenvalue proof `cos E(k)=cos(x/2) cos k` are still script-level
(`tools/bit_ring_checkerboard.py`). Remaining: the momentum action, `M(k)`,
eigenvalues, and the empty-firing gapless proof. The mass reading is a
hypothesis.

## Everything else still open

- Shared vs sector/composite background: no certified placement of the
  bit-ring background or selection of the colour composite. Blocking item:
  the line/placement map.
- Reference identity: `refRecord` is not proved equal to `SharedReference` or
  `ColourReference`. Blocking item: the E8/layout reference map.
- Multi-protocol composition: same missing object as above.
- Triality and per-generation costs: conditional on the line/attachment map.
  Blocking item: the bit-ring-to-lattice line.
- Radiative stage 2: not started. Blocking item: assembled diagram kernel.
- Legacy single-reference assumptions: conditional per label; the heavy writer
  single reference is not certified. Blocking item: background choice.
