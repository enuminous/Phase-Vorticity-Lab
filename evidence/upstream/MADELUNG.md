# Phase currents and the Madelung equations

[Madelung.lean](Madelung.lean) gives explicit flat, one-space/one-time
specializations of ME-018–021. It uses the existing polar wave

$$\psi(t,x)=\rho(t,x)e^{i\theta(t,x)}.$$

The first and second wave derivatives are proved from Mathlib's ordinary
derivatives and the product and chain rules. They are not formal symbols
assigned the desired values. The canonical equations remain unchanged.

| Entry | Result and principal theorem | Scope |
|---|---|---|
| ME-018 | `relativistic_current_components` identifies the phase current with the imaginary part of the conjugate wave times its derivative. | Cartesian signature (+−), c=1; the raised spatial component has a minus sign. |
| ME-019 | `kleinGordon_implies_current_conservation` derives zero current divergence from the real-potential Klein–Gordon equation. | Flat 1+1 dimensions, with the stated second time and space derivatives. |
| ME-020 | `schrodinger_iff_madelung` proves pointwise equivalence to Hamilton–Jacobi **and** probability continuity; `schrodinger_solution_iff_madelung` gives the everywhere version. | Given differentiable amplitude/phase fields, nonzero amplitude, mass and hbar; one spatial dimension. |
| ME-021 | `schrodinger_factorization` identifies the quantum-potential term in the real part of the Schrödinger equation. | Actual second amplitude derivative; division is used only at a nonzero amplitude in the equivalence. |

## The relativistic current

For real U and the equation

$$\psi_{tt}-\psi_{xx}+U\psi=0,$$

the raised current components are

$$J^t=\rho^2\theta_t,\qquad J^x=-\rho^2\theta_x.$$

The stronger identity `relativistic_divergence_identity` proves

$$\partial_tJ^t+\partial_xJ^x
=\operatorname{Im}\bigl(\overline\psi(\psi_{tt}-\psi_{xx}+U\psi)\bigr).$$

Consequently a Klein–Gordon solution has zero divergence. This identity does
not divide by the amplitude and therefore does not require it to be nonzero.
The converse from current conservation alone to the full complex field equation
is not claimed.

## The Schrödinger relation

Independently, fix a real potential V and the equation

$$i\hbar\psi_t+\frac{\hbar^2}{2m}\psi_{xx}-V\psi=0.$$

Write S = hbar*theta. At nonzero amplitude, the Lean theorem proves equivalence
to the pair

$$S_t+\frac{S_x^2}{2m}+V+Q=0,
\qquad Q=-\frac{\hbar^2}{2m}\frac{\rho_{xx}}{\rho},$$

$$\partial_t(\rho^2)+\partial_x j=0,
\qquad j=\frac{\hbar}{m}\rho^2\theta_x.$$

`probability_density_eq_norm_sq` and `probability_current_eq_wave_current`
connect these definitions to the original complex wave. The proof factors the
Schrödinger residual as

$$\left[-\rho H+i\frac{\hbar}{2\rho}C\right]e^{i\theta},$$

where H and C are the Hamilton–Jacobi and continuity residuals. The exponential
is nonzero; separating its coefficient into real and imaginary parts gives both
directions without assuming either real equation in the forward direction.

The probability density rho squared is **not** the relativistic charge
rho squared times theta_t. The two currents belong to the two separately stated
evolution equations. Neither dynamics follows from the polar identity alone.

## Assumptions and checked examples

`Regular` requires differentiability in time and twice differentiability in
space, for each fixed other coordinate. It does not assume continuous or mixed
derivatives. The Klein–Gordon theorem additionally requires second time
derivatives at the point. The potential is real; no derivative of it is used.
The Schrödinger equivalence requires nonzero real hbar and mass. Its pointwise
form excludes amplitude zeros at that point; its everywhere form assumes
nonzero amplitude everywhere.

- `plane_wave_solution_iff` checks the standard dispersion relation for
  constant nonzero amplitude and phase k*x − omega*t:
  hbar*omega = (hbar*k)^2/(2*m) + V₀. The regularity assumptions are proved for
  these fields.
- `constant_amplitude_quantumPotential` gives Q=0 for constant amplitude.
- `zero_amplitude_counterexample` proves that the zero wave solves Schrödinger
  at hbar=m=1 and V=1 while the divided Hamilton–Jacobi residual is 1 under
  Lean's total division convention.
  This establishes why the amplitude exclusion cannot simply be removed.

These four entries remain **partial specializations** in the coverage ledger.
The module does not prove global phase reconstruction for an arbitrary complex
wave, general manifolds, higher-dimensional covariance, PDE existence, boundary
conditions, finite integrated probability or an empirical interpretation.
The results are standard mathematics, without an EFMW-specific novelty claim.

## Verification

The [analytic workflow](../.github/workflows/lean.yml) builds this module and
includes every declaration in the [strict axiom audit](Audit.lean). The coverage
check locks the canonical text and checks agreement between the module roster,
build targets and audit. The audit's four negative controls must continue to
reject public/private axioms, placeholders and native proof oracles.
