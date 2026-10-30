# Frozen audit contract

**Target:** PVL-001 v0.1.0, registered polar-vortex family in `src/core.js`.  
**Claim under test:** a prescribed set of representation and symmetry checks can reject known defective members before the supported Biot–Savart integration entry point runs.

The stronger claim that this exactly closes a general symmetry-encoding gap is **supported only for the bounded checks below and unresolved in general**. No universal expression parser or general proof-to-code correspondence is supplied.

## Operations

These are named PVL software checks, not newly invented Zoo animals. **No Zoo animal operations were executed.** The EFMW audit discipline is used to separate evidence and expose assumptions.

| Operation | Input and transformation | Acceptance criterion | Evidence kind |
|---|---|---|---|
| Domain and conventions | Structured parameters | Finite declared values, admissible ranges and positive core/scale | Executed range checks |
| Known representation | Model registry key | Registered `polar-vortex` representation and preset | Executed dispatch check |
| Single-valued wave | Winding list | All windings integral | Executed algebraic condition |
| Reconstruction domain | Boundary descriptor | Explicit whole-plane-decay contract | Declared assumption checked for presence |
| Global U(1) | Four points, phase shift 0.731 | Relative wave transformation error ≤ 1e−10 | Finite numerical test |
| Current invariance | Same phase shift | Relative current error ≤ 1e−10 | Finite numerical test |
| Phase-current identity | Explicit J versus centered differences of ψ, step 1e−5 | Relative error ≤ 2e−6 | Numerical cross-check |
| Spatial SO(2) | Rotate sources, chart and points by 0.29, 1.13, 2.4 radians | Max relative wave/current/velocity error ≤ 1e−10 | Finite numerical test |
| Kernel covariance | Same rotations of kernel displacement | Relative error ≤ 1e−10 | Finite numerical test |
| Curl agreement | Centered differences of blob velocity | Normalized curl error ≤ 2e−6 | Numerical cross-check |
| Frame normalization | Independent nonzero Ω=0.37 probe | Absolute curl residual ≤ 2e−6 | Numerical cross-check |

For vector or complex pairs, relative difference is `||a−b||/max(1,||a||,||b||)`. Probe positions and bounds are fixed in source. PASS requires all checks to pass. FAIL takes priority over UNRESOLVED. Any non-PASS result prevents `integrate()` from allocating its source quadrature. Low-level mathematical helper functions remain available for tests; this is an engineering contract, not a security boundary against someone editing the source.

## Fault controls and evidence

| Fault | Result |
|---|---|
| Real amplitude substituted for the complex wave | Global phase and current identity fail |
| ρ substituted for ρ² in the current | Current identity fails |
| Laboratory x component stretched | Spatial and kernel covariance fail; curl consistency also detects a mismatch |
| Frame contribution doubled | Frame normalization fails |
| Half-integer winding introduced | Single-valuedness condition fails |
| Boundary contract omitted | UNRESOLVED; integration blocked |
| Unregistered expression declared | UNRESOLVED; integration blocked |

The individual gates may pass other aspects of a bad candidate. This is expected: a global phase error need not violate SO(2), and a symmetry-correct model can still be numerically inaccurate. Tests include a density observable with no surviving explicit phase factor, zero winding, core zeros, signed circulation, full-quadrature covariance, and the distinction between current and velocity curl.

## Anti-circularity and limits

- The current comparison computes finite differences of the complex wave rather than substituting the asserted current identity on both sides.
- The curl comparison differentiates the velocity rather than returning the supplied vorticity by definition.
- Both methods nevertheless share the authored ansatz and ordinary floating-point arithmetic. They are implementation cross-checks, not independent empirical evidence.
- The benchmark compares numerical quadrature with the analytic velocity of the chosen blob. It does not fit either field to data.
- Boundary conditions, positive scale, the blob core and dimensional conventions are declared model choices; passing checks do not derive them.
- Finite transformations cannot rule out all possible equivariance violations outside the sampled points. Fail-closed handling is provided for unknown registry entries, not for adversarial arbitrary programs.
- Upstream Lean compilation does not prove JavaScript arithmetic, finite-difference accuracy, quadrature convergence, or correct rendering.
- There is no new physical dataset, no EFMW-versus-standard-physics experiment, and no evidence of universal rotation.

## Evidence-separated conclusions

| Claim | Status |
|---|---|
| Registered faults are rejected before supported integration | **Demonstrated** by delivered tests and browser checks |
| Selected source theorems have a successful upstream analytic CI record | **Supported by inspected CI**, with cache replay; no fresh local Lean build |
| Declared numerical cases meet the frozen fine-grid probe criterion | **Demonstrated** by `numerical-benchmark.json` |
| Polar current, Cartesian curl and rotating-frame equations used here are established mathematical forms | **Known-form overlap / equivalent**, not new EFMW mathematics |
| A universal phase/rotation checker exists for arbitrary expressions | **Unresolved; not implemented** |
| Every phase-free expression is invalid | **Rejected** by the density counterexample |
| A smooth phase gradient itself generates arbitrary distributed vorticity | **Rejected under smooth-chart assumptions**; topology and core singularities matter |
| Finite core regularization is derived by the upstream phase identity | **Modeling postulate**, not established |
| ME-056 supplies a derived rotating metric or a fluid evolution law | **Unresolved; not assumed** |

## Next formal milestone

Prove the proper-planar-rotation covariance of the declared 2D kernel, including its exclusion at zero, in a new Lean module. Then prove covariance of a finite quadrature sum when its nodes, weights and query point transform together. Acceptance requires an actual build and printed axioms at a pinned commit. The JavaScript floating-point and continuous-integral bridges remain separate obligations. Add tests that compare coarse and fine fields over a held-out region rather than only four fixed points; fix an error metric, a core-exclusion rule and an acceptance threshold before running that extension.
