# Monolithic Phase / Vorticity Lab

**PVL-001 · v0.1.0 · 30 October 2026**  
Matthew Chenoweth Wright · Monolithic LLC / eNuminous

A standalone laboratory connecting the Monolithic 102 phase/current and Cartesian vorticity results to **gated, two-dimensional fluid Biot–Savart reconstruction**.

**Open `index.html` directly in a browser.** Everything needed by the lab is embedded in that file. No installation, account, network connection, API key, or build step is required to use it.

## What is included

- Four configurations: one vortex, a counter-rotating dipole, a co-rotating pair, and an alternating quadrupole.
- Phase, winding, core-radius, spatial-orientation and rotating-frame controls.
- Eleven pre-integration checks, with PASS / FAIL / UNRESOLVED results and visible criteria.
- Five defective-model controls and two missing-information controls. Every non-PASS decision blocks the supported integration entry point.
- Actual midpoint quadrature of the 2D fluid Biot–Savart kernel, with analytic-reference error measurements.
- Phase, density, vorticity and speed layers, coordinate inspection, velocity arrows, and passive tracer paths.
- JSON audit/result export and CSV field export.
- Editable source, dependency-free Node tests, benchmark results, pinned upstream Lean sources, a formal reproduction script, GitHub CI, and an optional GitHub Pages workflow.

## What the proposed integration can legitimately claim

The Monolithic analytic overlay supplies useful **theorems under explicit assumptions**. They should be reused with their hypotheses rather than installed as new kernel axioms. A theorem proved from standard axioms is different from an unchecked premise added to Lean.

A phase factor is required by the chosen wave representation, but it cancels in phase-invariant observables such as `|ψ|²`. The validator therefore checks transformation laws and identities for the relevant object. It does not reject every expression in which `exp(iθ)` is absent.

The current lab is a finite numerical validator for registered models, not a general symbolic theorem prover. Passing symmetry checks does not imply numerical accuracy, correct dynamics, a physical interpretation, or general covariance. No EFMW-specific physical discovery is claimed.

## Model in one paragraph

The lab uses integer phase windings and a nonnegative amplitude that vanishes at vortex centers. It evaluates `J = a ρ² ∇θ`, where `a = ℏ/m = 1` in the displayed dimensionless convention. The ideal phase velocity is singular; integration instead uses a declared smooth vortex-blob vorticity with an analytic whole-plane velocity. A finite rotated square samples that vorticity for quadrature. Rotating-frame velocity is added afterward, with `curl(u_rel) = ω − 2Ω`. The model is kinematic: tracers follow a frozen field. It does not solve Schrödinger, Gross–Pitaevskii, Euler time evolution, Maxwell's equations, or a rotating cosmology.

See [MODEL.md](docs/MODEL.md), [AUDIT.md](docs/AUDIT.md), and [FORMAL_BRIDGE.md](docs/FORMAL_BRIDGE.md) for definitions, assumptions, evidence and unresolved obligations.

## Reproduce the numerical checks

Node 20 or newer and Python 3 are sufficient. No `npm install` is needed.

```sh
node --test tests/core.test.cjs
node tools/benchmark.cjs
python3 tools/verify_snapshots.py
python3 tools/build.py
```

The delivered numerical suite has **18 passing tests**. A frozen four-probe benchmark at a 112×112 source grid has relative vector L2 errors of approximately **0.098%, 0.190%, 0.127%, and 0.674%** for the single, dipole, pair and quadrupole cases respectively. These are measured sample errors, not uniform error bounds.

The 32×32 quadrupole case has **44.8% error** despite passing the symmetry gate. This negative result is retained in [numerical-benchmark.json](evidence/numerical-benchmark.json). Grid refinement is not uniformly monotone at fixed probe locations. The benchmark acceptance rule was fixed in its script before the first recorded run: all four 112×112 cases must be below 12% at the four specified probes. The tighter observed values are reported as measurements, not a retrospectively changed threshold.

## Formal evidence

Upstream source is pinned to [`6e85c9e558652f5033c55d70f33077eff7a9fd89`](https://github.com/enuminous/Monolithic-102-Zoo-Lean4/tree/6e85c9e558652f5033c55d70f33077eff7a9fd89). The recorded [analytic job](https://github.com/enuminous/Monolithic-102-Zoo-Lean4/actions/runs/40600670063/job/122527682065) reports a successful 2,820-job build and an axiom audit of 803 safe declarations, including 580 theorem declarations and generated lemmas. Cached/replayed compilation appears in that record. This is inspected upstream evidence, not a new clean build performed for this ZIP.

The local environment used for this package did not have Lean or Lake installed. **A local formal rebuild and the new source-name probe have not been run.** Run the following on a machine with elan, the pinned Lean toolchain and network access to fetch Mathlib dependencies:

```sh
bash tools/verify_formal.sh
```

This rebuilds the unmodified upstream analytic package and runs its strict axiom audit and four rejection controls, then prints the selected theorem signatures and axioms. It does not prove that the JavaScript implements those theorems. The optional `Formal source bridge` Actions workflow performs the same work when manually dispatched.

## GitHub use

The ZIP has **no enclosing directory**: `index.html` is at its root. Extract it into a new repository, preserving subdirectories. Example:

```sh
git init
git add .
git commit -m "Add PVL-001 phase and vorticity laboratory"
```

The `Numerical verification` workflow runs on push and pull request. To publish a static lab, set repository Settings → Pages → Source to **GitHub Actions**, then manually run `Publish laboratory`. The complete package is published in [enuminous/Phase-Vorticity-Lab](https://github.com/enuminous/Phase-Vorticity-Lab). The Pages workflow is included for optional site deployment; repository publication alone does not enable GitHub Pages.

## Layout

| Path | Purpose |
|---|---|
| `index.html` | Self-contained browser application |
| `src/` | Editable physics, gate, UI and styling |
| `tests/` | Positive, negative, covariance and domain tests |
| `tools/` | Build, benchmark, source verification and formal verification |
| `docs/` | Model, audit contract and formal bridge |
| `formal/upstream-analysis/` | Pinned Lean 4.28 analytic package and source probe |
| `evidence/` | Measured results, provenance, source documentation and CI excerpt |
| `.github/workflows/` | Numerical CI, manual formal verification, manual Pages publication |
| `SHA256SUMS` | Hashes of the distributed files |

**Attribution and licence:** original source and contributor attribution are retained in [NOTICE.md](NOTICE.md). No new broad licence grant is made by this research package. AI assistance was used for implementation and source review.
