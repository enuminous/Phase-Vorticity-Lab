# A Cartesian model of ME-055

[Vorticity.lean](Vorticity.lean) defines the catalogue's vorticity relation

$$\Omega_U=\nabla\times v_U$$

on real Cartesian three-space, with the standard (x,y,z) orientation and an
explicit input field v. Every partial derivative is the actual Fréchet
derivative applied to the corresponding coordinate basis vector. The gradient,
divergence and curl use their usual Cartesian components. The canonical source
equation is unchanged.

The module contains **30 explicit theorem statements**, including helper
derivative rules and the following results.

| Result | Lean theorem | Assumptions |
|---|---|---|
| Mixed partials commute. | `mixed_partials_commute` | C² real scalar field; uses Mathlib's Schwarz theorem. |
| Curl of a gradient is zero. | `curl_gradient` | C² scalar field. |
| Divergence of a curl is zero. | `divergence_curl` | C² vector field. |
| Curl respects addition and constant scaling. | `curl_add`, `curl_const_smul` | Differentiable fields at the point. |
| Curl obeys the product rule for scalar multiplication. | `curl_smul` | Differentiable scalar and vector fields at the point. |
| Adding a smooth gradient leaves curl unchanged. | `curl_gradient_invariant` | Differentiable vector field and C² scalar potential. |
| The ME-051 and ME-053 force forms have zero curl. | `combined_force_curl_zero`, `scaled_force_curl_zero` | C² potentials and spatially constant coefficients. |
| Rigid rotation has curl (0,0,2*omega) and zero divergence. | `rigid_rotation_curl`, `rigid_rotation_divergence` | Any real omega and point. |
| A varying coefficient times a gradient can have nonzero curl. | `variable_coupling_counterexample` | Explicit coordinate functions; differentiability is proved. |

## Constant and variable coefficients

The product rule for scalar multiplication is

$$\nabla\times(a v)=\nabla a\times v+a(\nabla\times v).$$

Taking v to be the gradient of a C² potential f gives

$$\nabla\times(a\nabla f)=\nabla a\times\nabla f.$$

Consequently a spatial constant a preserves zero curl, while a varying
coefficient need not. The checked example a=x, f=y gives

$$a\nabla f=(0,x,0),\qquad \nabla\times(a\nabla f)=(0,0,1).$$

The full product gradient contains an additional term:

$$\nabla(af)=a\nabla f+f\nabla a.$$

`full_product_gradient_curl` checks that both terms together have zero curl
for the same example. The proof does not assume that a variable-coefficient
multiple of a gradient is itself a gradient.

## Connection to the existing force models

The module reuses the scalar potentials already defined in
[SpecifiedModels.lean](SpecifiedModels.lean):

$$F=-\nabla U+c\nabla R=\nabla(-U+cR),\qquad
F_\phi=-\frac{\beta}{m}\nabla\phi
=\nabla\left(-\frac{\beta}{m}\phi\right).$$

The component-gradient equalities are proved before applying the zero-curl
result. Here c, beta and mass are spatial constants; nonzero mass remains the
application domain of ME-053. Lean's total division does not supply a physical
meaning for zero mass. These force identities do not identify a force with
the velocity field in ME-055 or prove a velocity evolution equation.

For rigid rotation, v=(-omega*y, omega*x, 0), the curl is twice the angular
velocity parameter. `rigid_rotation_squared_curl` also proves that the sum of
squared curl components is 4*omega². The scalar rotation parameter used in the
separate ME-056 cosmological model is not automatically either omega or the
magnitude of this vector curl.

## Coverage and limits

ME-055 now has an **explicit analytic model** in [coverage.json](coverage.json).
This class records a defined mathematical operator and checked properties;
it does not close the retained physical source obligations. The 49-entry
[analytic ledger](COVERAGE.md) records the current counts. The subsequent
[fluid module](FLUIDS.md) reuses these Cartesian derivative operators.

No theorem here identifies an observed universal velocity field, establishes
universal rotation, supplies physical units or dynamics, extends the result to
curved geometry, or proves that every curl-free field on an arbitrary domain
has a global potential. These are standard vector-calculus results under
explicit assumptions, without a novelty or empirical-validation claim.

The [verification workflow](../.github/workflows/lean.yml) builds the module
and applies the [strict declaration audit](Audit.lean) and its four rejection
controls. The coverage checker verifies that all analytic project modules are
listed in both the build and audit, while preserving the canonical source hash.

## Algebraic rotation and the ME-056 bridge

[RotationKinematics.lean](RotationKinematics.lean) adds the standard linear
planar complex structure, norm-preserving rotations, and an actual trajectory
derivative equal to this module's `rigidRotation`. It also proves the curl of
arbitrary constant angular-velocity fields and conditional residual limits.
[RotatingCosmology.lean](RotatingCosmology.lean) checks the exact quarter-factor
normalization when the scalar ME-056 parameter is chosen as angular velocity,
and proves branch, identifiability, and explicit scalar-evolution results.
The choice remains separate from a physical identification. See the
[54-theorem catalogue and limits](ROTATION_COSMOLOGY.md).
