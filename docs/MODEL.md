# PVL-001 mathematical model

## Scope and conventions

This is a two-dimensional, nonrelativistic, incompressible-fluid reconstruction on the plane. It uses the standard positive orientation `(x,y)` and scalar vorticity `ω = ∂x u_y − ∂y u_x`. A proper planar rotation acts on coordinates and vectors with the same matrix `R(β)`. Reflection covariance and arbitrary curved-space covariance are outside this version.

Choose length unit L₀ and time unit T₀. Velocity has units L₀/T₀, vorticity and frame angular speed have units 1/T₀, circulation and `a = ℏ/m` have units L₀²/T₀. The UI fixes the dimensionless value `a = 1`. The amplitude is normalized relative to a reference density; the interface is not a physical unit-inference system.

## Phase and current

For integer windings nᵢ and centers xᵢ, let rᵢ = x − xᵢ and

\[
\theta(x)=\alpha+\sum_i n_i\arg(r_i),\qquad
\rho(x)=\prod_i\left(\frac{|r_i|}{\sqrt{|r_i|^2+\epsilon^2}}\right)^{|n_i|},
\quad \psi=\rho e^{i\theta}.
\]

The phase chart rotates with the configuration, so an active spatial rotation gives `ψ_R(Rx) = ψ(x)`. Phase values themselves can jump by integer multiples of 2π at chart cuts; the wave is single-valued for integer winding. At a nonzero-winding center the amplitude vanishes. The code reports no phase gradient there rather than dividing by zero.

Away from the centers,

\[
\nabla\theta=\sum_i n_i\frac{(-r_{i,y},r_{i,x})}{|r_i|^2},\qquad
J=a\rho^2\nabla\theta=a\operatorname{Im}(\bar\psi\nabla\psi).
\]

The rightmost identity is checked numerically using centered differences of the complex wave, independently of the explicit phase-gradient formula. Global `α → α + δ` multiplies ψ by `exp(iδ)` but leaves density and J invariant. This does not imply invariance under a position-dependent phase; no compensating gauge field is supplied.

The finite-difference identity is an implementation check in two spatial dimensions. It is not claimed to be an instance of a complete 2D Madelung-equivalence theorem imported from the upstream 1+1-dimensional module. Density is generally not integrable over the whole plane in this model. It is not a normalized single-particle probability distribution, and the stationary ansatz is not asserted to solve an evolution equation.

## Why a separate vortex regularization is needed

The ideal phase velocity is `v_phase = a ∇θ`. It has zero ordinary curl on any smooth chart excluding the vortex points. An enclosing loop has circulation `2π a Σ nᵢ`; the singular vorticity is concentrated at the excluded cores in the distributional description. A globally smooth scalar gradient cannot represent arbitrary smooth distributed vorticity.

For numerical reconstruction we **choose**, rather than derive from the phase identity, the regularized blob

\[
u_i(x)=a n_i\frac{(-r_{i,y},r_{i,x})}{|r_i|^2+\epsilon^2},\qquad
\omega_i(x)=\frac{2a n_i\epsilon^2}{(|r_i|^2+\epsilon^2)^2}.
\]

Direct differentiation gives `curl uᵢ = ωᵢ` and `div uᵢ = 0`; integration over the whole plane gives `∫ωᵢ dA = 2πa nᵢ`. The code checks the curl identity with independent finite differences. For a circle of radius R around one isolated vortex,

\[
\oint u_i\cdot d\ell = 2\pi a n_i\frac{R^2}{R^2+\epsilon^2}.
\]

Thus finite-core circulation is not exactly quantized at finite R. The ratio of regularized to ideal phase speed is `R²/(R²+ε²)`, with relative discrepancy `ε²/(R²+ε²)` away from the center. For one unit-winding vortex, the chosen amplitude happens to make J equal the regularized u in the displayed normalization. That coincidence must not be generalized to higher winding or overlapping vortex products. The test suite contains a multiple-vortex counterexample.

In particular, even on a smooth phase chart,

\[
\nabla\times J=a\,\nabla(\rho^2)\times\nabla\theta,
\]

which can be nonzero while `curl(v_phase)=0`. Current curl, velocity curl and angular speed are distinct objects.

## Biot–Savart reconstruction

The whole-plane fluid kernel is

\[
K(r)=\frac{(-r_y,r_x)}{2\pi |r|^2},\qquad
u(x)=\int_{\mathbb R^2}K(x-y)\omega(y)\,d^2y.
\]

This is the standard 2D fluid kernel, not the three-dimensional electromagnetic current-density formula. See the author-hosted [2-D Vortex Methods manuscript](https://math.berkeley.edu/~strain/Publications/svm.pdf), §2, for the kernel convention. The blob family above supplies an analytic full-plane comparison, obtained by integrating its radial vorticity.

The lab approximates the integral with N×N midpoint samples in `R(β)[−L,L]²`, with default L=4. The same domain, sources and query points must rotate together in a covariance comparison. The source kernel is locally integrable; at an exactly coincident sample the code assigns zero to the symmetric self-cell contribution. This is a finite-cell approximation, not an exact integral over every nonuniform cell. No extra kernel softening is silently applied.

There are two distinct errors: truncation of the blob tails outside the square and quadrature error within it. Increasing N does not remove the tail error. Near-cell sampling can make fixed-probe refinement nonmonotone. No periodic, wall, image-vortex or no-through-flow boundary condition is implied by the square display. A velocity specified only by its curl can also require harmonic/boundary data; the selected decaying whole-plane reconstruction fixes the intended class for this model.

## Rotating frame

For a constant angular speed Ω about the normal axis, the displayed relative velocity is

\[
u_{\rm rel}(x)=u(x)-\Omega\,\hat z\times x
             =u(x)+(\Omega y,-\Omega x),\qquad
\omega_{\rm rel}=\omega-2\Omega.
\]

The rigid frame term is added after the decaying-vortex reconstruction. Feeding its constant vorticity into a finite-square whole-plane integral would be a different problem with different boundary behavior. The lab changes the velocity representation at the current configuration; it does not evolve moving coordinates or integrate Coriolis/centrifugal force equations.

ME-055 provides relevant Cartesian curl and factor-of-two results. ME-056's scalar rotating-cosmology normalization is documented in the source bridge, but it is not used as a constitutive law for this fluid model.

## Visualization

The wave-phase color uses `arg(ψ)`; it therefore becomes uniform under the phase-removal fault. Density and vorticity layers use the defined fields. Before integration, arrows show the analytic regularized candidate. After integration, arrows and tracer paths use bilinear interpolation of the reconstructed 31×31 velocity display grid. The integrator's source grid is independently selectable. Tracers use a midpoint step and reset at the display edge; they are an illustration of a frozen flow, not a probability-conserving particle simulation or evolving vortex dynamics.
