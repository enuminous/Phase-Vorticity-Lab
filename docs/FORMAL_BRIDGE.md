# The formal-source integration

The archive includes the complete ten-module upstream analytic package, its pinned dependencies and its original strict `Audit.lean`. Source files are preserved byte-for-byte and checked against Git blob hashes. The browser consumes a structured numerical model, not Lean axioms.

Upstream: `enuminous/Monolithic-102-Zoo-Lean4` at `6e85c9e558652f5033c55d70f33077eff7a9fd89`; Lean 4.28.0, Mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`. See `evidence/provenance.json` for exact source URLs and hashes.

| Entry | Selected declaration | Scope and use here |
|---|---|---|
| ME-016/017 | `MonolithicAnalysis.Polar.norm_sq` | Real amplitude and complex exponential; motivates the exact density convention |
| ME-018 | `MonolithicAnalysis.Madelung.current_eq_im_conj_wave_deriv` | One-dimensional ordinary derivative under differentiability hypotheses; current comparison reference |
| ME-019 | `MonolithicAnalysis.Madelung.kleinGordon_implies_current_conservation` | Flat 1+1 real-potential Klein–Gordon dynamics; documented, **not invoked to assert lab continuity** |
| ME-020 | `MonolithicAnalysis.Madelung.schrodinger_iff_madelung` | 1+1 pointwise equivalence with regularity and nonzero amplitude/mass/ℏ; no promotion to arbitrary 2D fields |
| ME-021 | `MonolithicAnalysis.Madelung.schrodinger_factorization` | Quantum-potential factorization; documented, no Q field or Schrödinger solver in this lab |
| ME-055 | `MonolithicAnalysis.Vorticity.curl_gradient`, `curl_smul`, `rigid_rotation_curl` | Cartesian derivatives, C² where needed; supplies curl/current distinction and factor-of-two convention |
| ME-055 rotation overlay | `MonolithicAnalysis.RotationKinematics.angular_field_curl` | Constant angular vector; curl = twice angular vector |
| ME-056 partial model | `MonolithicAnalysis.RotatingCosmology.vector_rate_from_curl` | Chosen scalar/vector normalization; not a derived rotating spacetime or lab fluid equation |

`formal/upstream-analysis/SourceBridge.lean` is a newly supplied **probe** containing imports, `#check`, and `#print axioms`. It introduces no new axioms and claims no new theorem. Its declaration names were checked against the packaged source; actual Lean elaboration of this probe remains unperformed here. The optional formal workflow and `tools/verify_formal.sh` run it after building the unchanged upstream package.

The source audit allows only `propext`, `Classical.choice`, and `Quot.sound` for matched safe project declarations and explicitly tests rejection of a public axiom, private axiom, placeholder, and native reduction proof oracle. The upstream job reports 803 safe declarations and 580 theorem declarations including generated lemmas. This count is for the whole analytic package, not only the selected phase/vorticity bridge, and is not a count of distinct physical laws.

The original audit excludes unsafe declarations from that safe-declaration traversal; its result should be interpreted with that scope. No audit result is used as a premise in a new physical derivation. A copy of the selected upstream job log lines is in `evidence/upstream-ci-excerpt.txt`.

The formal source package requires downloading its pinned Mathlib dependency and transitive packages on first build. Browser use and numerical tests remain fully offline. Coverage-check scripts that depend on the original repository's canonical-source layout are not represented as having run inside this relocated subset; the original upstream coverage check is evidenced by its CI record.
