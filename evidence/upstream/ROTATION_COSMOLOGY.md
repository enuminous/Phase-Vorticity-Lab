# ME-055 and ME-056: rotation kinematics and the scalar cosmological constraint

This tranche supplies **54 explicit Lean theorems**: 30 in
[RotationKinematics.lean](RotationKinematics.lean) and 24 in
[RotatingCosmology.lean](RotatingCosmology.lean). It reuses the existing
[Cartesian curl](Vorticity.lean) and `Cosmology.rateSquared` in
[SpecifiedModels.lean](SpecifiedModels.lean). The canonical formulas are unchanged.

The contribution is an explicit mathematical model and its proved consequences.
ME-055 retains `analytic_model` coverage; ME-056 retains
`partial_specialization` because a rotating-spacetime derivation is still open.
The existing 21/28 coverage counts therefore do not change.

## Frozen target and conventions

ME-055 is the retained vector relation $\Omega_U=\nabla\times v_U$.
Coordinates are real, Cartesian, and right-handed. Angles are dimensionless;
when interpreted as kinematics, position has units of length, time has units of
time, and angular velocity and curl of velocity have inverse-time units.
`squaredNorm` is explicitly the sum of squared components. It is not the
default norm on the Lean function type `Fin 3 → ℝ`.

ME-056 retains

$$
H^2=\frac{8\pi G}{3}\rho+\frac{\Lambda}{3}-\frac{k}{a^2}+\frac{\omega^2}{a^2}.
$$

Here `omega` names the catalogue's scalar rotation parameter to distinguish it
from the vector curl in ME-055. `Constraint` additionally requires $a>0$.
Lean's total division does not supply a physical interpretation at $a=0$.
The gravitational coefficients, density, cosmological term, and curvature are
explicit real inputs. Their physical units and cosmological identification
must be fixed by an additional physical model.

**Normalization choice.** In the bridge the scalar parameter is chosen to be
the angular velocity of the rigid flow. For this choice, the rotational term
is one quarter of squared vorticity divided by $a^2$. The canonical catalogue
does not itself prove this choice; using the magnitude of vorticity as the
scalar parameter would give a different normalization.

## ME-055: algebra, finite motion, velocity, and curl

The standard planar linear map is

$$
J(x,y)=(-y,x),\qquad J^2=-I_2.
$$

`planeAction a b` realizes multiplication by $a+ib$ on that plane, including
the complex multiplication law. Taking $a=\cos\theta$ and $b=\sin\theta$
gives a rotation that preserves the explicit Euclidean squared norm.
The three-dimensional `rotate` fixes the third axis. Its generator squares
to minus the transverse projection, **not** minus the identity on all of
three-space. `fixed_axis_not_a_hinge` checks that boundary explicitly.

For any differentiable phase with $\theta'(t)=\omega$ at the specified time,
`phase_hasDerivAt` proves

$$
\frac{d}{dt}\mathcal R(\theta(t))x
=v_\omega(\mathcal R(\theta(t))x),
\qquad v_\omega(x,y,z)=(-\omega y,\omega x,0).
$$

The field on the right is the **existing** `Vorticity.rigidRotation`, not a new
lookalike definition. `flow_deriv_curl` changes from initial to current
coordinates by the inverse rotation and proves that the curl of the resulting
actual derivative field is $(0,0,2\omega)$.

For any spatially constant angular-velocity vector $w$,

$$
v_w(x)=w\times x,\qquad
\nabla\times v_w=2w,\qquad
\nabla\cdot v_w=0,\qquad
\lVert\nabla\times v_w\rVert_2^2=4\lVert w\rVert_2^2.
$$

The cross-product generator satisfies
$w\times(w\times x)=(w\cdot x)w-\lVert w\rVert_2^2x$.
For a unit axis and a transverse vector, this is the hinge relation.
Within the rigid family about a fixed origin, half the curl reconstructs the
angular-velocity vector and therefore the field. This does not make curl
injective on arbitrary fields; the previous `curl_gradient_invariant` theorem
still permits smooth gradient additions.

`residual_curl_tendsto` transfers a **supplied** limit
$\omega(t)\to\omega_\infty$ to the actual curl, and
`residual_limit_nonzero` requires $\omega_\infty\ne0$ as an explicit hypothesis.
No nonzero residual or cosmic rotation is inferred from the algebra.

## ME-056: admissibility, branches, and identifiability

The constraint has a real rate exactly when the scale is positive and its
right-hand side is nonnegative. Every admissible real rate is characterized by

$$
H=+\sqrt{\mathrm{rateSquared}}\quad\text{or}\quad
H=-\sqrt{\mathrm{rateSquared}}.
$$

The equation alone selects neither expansion nor contraction. It also cannot
select the sign of rotation. The code supplies a concrete example admitting
both signs of the Hubble rate.

At a nonzero scale and with the other inputs fixed, two curvature/rotation
pairs yield the same rate exactly when

$$
k_1-\omega_1^2=k_2-\omega_2^2.
$$

Thus the scalar equation identifies the combination
$k_{\mathrm{eff}}=k-\omega^2$, not rotation independently of curvature.
`distinct_parameters_same_rate` supplies the exact witness $(k,\omega)=(0,0)$
and $(1,1)$. `recover_rotation_square` recovers a squared parameter only after
the other inputs, including curvature, are fixed.

The link to the existing ME-055 field is checked directly:

$$
\mathrm{rateSquared}(\omega)
=\mathrm{rateSquared}(0)
+\frac{\sum_i(\nabla\times v_\omega)_i^2}{4a^2}.
$$

An explicitly authored vector extension uses $\lVert w\rVert_2^2/a^2$.
It equals the scalar formula evaluated at
$\omega=\sqrt{\lVert w\rVert_2^2}$ and also equals one quarter of the squared
curl contribution. This proves consistency of the chosen normalization,
not its physical identification.

## Actual scale-factor solutions of the stipulated equation

`EvolutionAt` requires a positive scale, differentiability, and the actual
derivative $H=a'/a$. The checked equivalence is

$$
(a')^2=\left(\frac{8\pi G}{3}\rho+\frac{\Lambda}{3}\right)a^2-k+\omega^2.
$$

This is the scalar constraint rewritten as a first-order squared relation.
It does not replace a spacetime metric, matter conservation, or the remaining
field equations.

Two concrete families are proved with actual derivatives:

| Family | Assumptions and time domain | Result |
|---|---|---|
| $a(t)=a_0+bt$ | $\rho=0$, $\Lambda=0$, $b^2=\omega^2-k$, and $a_0+bt>0$. | `affine_vacuum_solution` |
| $a(t)=a_0+\sqrt{\omega^2-k}\,t$ | $a_0>0$, $t\ge0$, $\omega^2-k\ge0$; same vacuum sector. | `expanding_vacuum_solution` |
| $a(t)=a_0e^{Ht}$ | $a_0>0$, $\rho=0$, $\Lambda=3H^2$, $k=\omega^2$; any real time and signed $H$. | `exponential_vacuum_solution` |

The exponential family illustrates the curvature degeneracy rather than
detecting a rotation. A constant scalar rotation can be absorbed into constant
effective curvature even in the differentiable solution predicate, as
`evolution_effective_curvature` proves. General coupled existence, uniqueness,
variable-axis rotation, and a physical evolution law for the rotation parameter
remain open.

## Exact declaration catalogue

### RotationKinematics: 30 theorems

| Area | Declarations |
|---|---|
| Planar algebra and norm | `quarter_turn_square`, `plane_action_mul`, `plane_rotate_zero`, `plane_rotate_add`, `plane_rotate_quarter`, `plane_action_squared_norm`, `plane_rotate_squared_norm` |
| Fixed-axis geometry | `rotate_plane_part`, `axis_generator_square`, `fixed_axis_not_a_hinge`, `rotate_axis`, `rotate_zero`, `rotate_add`, `rotate_inverse`, `rotate_two_pi`, `rotate_squared_norm` |
| Actual derivatives and flow | `phase_hasDerivAt`, `flow_hasDerivAt`, `flow_add`, `flow_deriv_curl` |
| Arbitrary angular-velocity vector | `angular_field_z`, `angular_field_curl`, `angular_field_divergence`, `angular_field_square`, `unit_axis_hinge_on_plane`, `angular_field_squared_curl`, `reconstruct_rigid_from_curl`, `angular_field_curl_nonzero` |
| Residual hypothesis | `residual_curl_tendsto`, `residual_limit_nonzero` |

### RotatingCosmology: 24 theorems

| Area | Declarations |
|---|---|
| Domain, real rates, signs | `zero_scale_excluded`, `constraint_rate_nonnegative`, `constraint_branches`, `admissible_rate_exists_iff`, `rate_rotation_sign`, `constraint_rotation_sign`, `constraint_rate_sign`, `both_rate_signs` |
| Rotation and curvature | `rotation_excess`, `rotation_excess_positive_iff`, `effective_curvature`, `rate_eq_iff_effective_curvature`, `distinct_parameters_same_rate`, `recover_rotation_square` |
| ME-055/056 normalization | `rate_from_rigid_curl`, `vector_rate_scalar_norm`, `vector_rate_from_curl` |
| Actual scalar evolution | `velocity_constraint_iff`, `evolution_iff`, `evolution_rotation_sign`, `evolution_effective_curvature`, `affine_vacuum_solution`, `expanding_vacuum_solution`, `exponential_vacuum_solution` |

## Provenance and verification

These are standard rotation and scalar-equation results, developed in response
to the request to formalize ME-055/056 following
[Two Paths to Rotation](https://github.com/enuminous/papers/blob/80807f2987fa992d23f3936daaaab1ad4f85a7bb/Two-Paths-to-Rotation.md).
The planar construction realizes the algebra discussed there using local Lean
definitions. It does not import or certify Ramtastic, nor claim a completed
interoperability theorem between both repositories' actual `Hinge` types.

Both new modules are build targets and are included in the strict declaration
audit and source-coverage check. Reproduce from the repository root:

```sh
cd analysis
lake exe cache get
lake build
python3 scripts/check_coverage.py
lake env lean -DwarningAsError=true Audit.lean
python3 scripts/test_axiom_audit.py
```

Only `propext`, `Classical.choice`, and `Quot.sound` are permitted by the audit.
Its four controls must reject a public axiom, private axiom, placeholder proof,
and native proof oracle. The workflow also verifies the separate root package.
Build evidence applies to the specific commit that passes these gates.

### Evidence boundary

The new formalization supplies genuine kinematics and exact consequences of a
specified scalar cosmological constraint. It does not establish that the
observed universe rotates, that CMB anisotropy has a rotational cause, or that
the retained ME-056 term follows from Einstein's equations. A specified
rotating metric, observer/matter model, unit conventions, and independent
observations remain the physical obligations.
