import Vorticity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# ME-055: algebraic rotation, actual trajectory derivatives, and vorticity

The planar generator is the standard Euclidean complex structure. Three-space
uses a fixed axis, so the square-minus-identity relation holds on the transverse
plane, not on all of three-space. All curl results reuse Vorticity.curl.
No cosmological velocity field, nonzero residual, or Clifford representation of
physical space is assumed to follow from these mathematical identities.
-/

noncomputable section
open scoped BigOperators
open Filter
open MonolithicAnalysis.Vorticity

namespace MonolithicAnalysis.RotationKinematics

abbrev Plane := Fin 2 → ℝ

/-- The standard planar quarter-turn, as an actual real linear map. -/
def quarterTurn : Plane →ₗ[ℝ] Plane where
  toFun x := ![-x 1, x 0]
  map_add' x y := by
    ext i
    fin_cases i <;> simp
    ring
  map_smul' a x := by ext i; fin_cases i <;> simp

theorem quarter_turn_square :
    quarterTurn.comp quarterTurn = -LinearMap.id := by
  ext x i
  fin_cases i <;> simp [quarterTurn]

/-- The real representation of the complex scalar a + i*b. -/
def planeAction (a b : ℝ) (x : Plane) : Plane := a • x + b • quarterTurn x

theorem plane_action_mul (a b c d : ℝ) (x : Plane) :
    planeAction a b (planeAction c d x) =
      planeAction (a*c-b*d) (a*d+b*c) x := by
  ext i
  fin_cases i <;> simp [planeAction, quarterTurn, Matrix.vecHead, Matrix.vecTail] <;> ring

def planeRotate (θ : ℝ) (x : Plane) : Plane :=
  planeAction (Real.cos θ) (Real.sin θ) x

theorem plane_rotate_zero (x : Plane) : planeRotate 0 x = x := by
  simp [planeRotate, planeAction]

theorem plane_rotate_add (α β : ℝ) (x : Plane) :
    planeRotate (α+β) x = planeRotate α (planeRotate β x) := by
  ext i
  fin_cases i <;>
    simp [planeRotate, planeAction, quarterTurn, Matrix.vecHead, Matrix.vecTail, Real.cos_add, Real.sin_add] <;> ring

theorem plane_rotate_quarter (x : Plane) :
    planeRotate (Real.pi/2) x = quarterTurn x := by
  simp [planeRotate, planeAction]

def planeSquaredNorm (x : Plane) : ℝ := x 0 ^ 2 + x 1 ^ 2

theorem plane_action_squared_norm (a b : ℝ) (x : Plane) :
    planeSquaredNorm (planeAction a b x) =
      (a^2+b^2)*planeSquaredNorm x := by
  simp [planeSquaredNorm, planeAction, quarterTurn]
  ring

theorem plane_rotate_squared_norm (θ : ℝ) (x : Plane) :
    planeSquaredNorm (planeRotate θ x) = planeSquaredNorm x := by
  rw [planeRotate, plane_action_squared_norm]
  have h : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [h, one_mul]

def planePart (x : Space) : Plane := ![x 0, x 1]
def transverse (x : Space) : Space := ![x 0, x 1, 0]
def axisGenerator (x : Space) : Space := ![-x 1, x 0, 0]

/-- Extend the planar action by fixing the third coordinate. -/
def rotate (θ : ℝ) (x : Space) : Space :=
  ![Real.cos θ*x 0-Real.sin θ*x 1,
    Real.sin θ*x 0+Real.cos θ*x 1, x 2]

theorem rotate_plane_part (θ : ℝ) (x : Space) :
    planePart (rotate θ x) = planeRotate θ (planePart x) := by
  ext i
  fin_cases i <;> simp [planePart, rotate, planeRotate, planeAction, quarterTurn] <;> ring

theorem axis_generator_square (x : Space) :
    axisGenerator (axisGenerator x) = -transverse x := by
  ext i
  fin_cases i <;> simp [axisGenerator, transverse]

theorem fixed_axis_not_a_hinge :
    axisGenerator (axisGenerator ![0,0,1]) ≠ -(![0,0,1] : Space) := by
  intro h
  have hc := congrFun h 2
  change (0 : ℝ) = -1 at hc
  norm_num at hc

theorem rotate_axis (θ : ℝ) (z : ℝ) : rotate θ ![0,0,z] = ![0,0,z] := by
  ext i
  fin_cases i <;> simp [rotate]

theorem rotate_zero (x : Space) : rotate 0 x = x := by
  ext i
  fin_cases i <;> simp [rotate]

theorem rotate_add (α β : ℝ) (x : Space) :
    rotate (α+β) x = rotate α (rotate β x) := by
  ext i
  fin_cases i <;> simp [rotate, Real.cos_add, Real.sin_add] <;> ring

theorem rotate_inverse (θ : ℝ) (x : Space) : rotate (-θ) (rotate θ x) = x := by
  rw [← rotate_add, neg_add_cancel, rotate_zero]

theorem rotate_two_pi (x : Space) : rotate (2*Real.pi) x = x := by
  ext i
  fin_cases i <;> simp [rotate]

/-- Explicit Euclidean squared norm; no identification with the Pi sup norm. -/
def squaredNorm (x : Space) : ℝ := ∑ i : Fin 3, x i ^ 2

theorem rotate_squared_norm (θ : ℝ) (x : Space) :
    squaredNorm (rotate θ x) = squaredNorm x := by
  have h : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  calc
    _ = (Real.cos θ ^ 2 + Real.sin θ ^ 2)*(x 0 ^ 2+x 1 ^ 2)+x 2 ^ 2 := by
      simp only [squaredNorm, Fin.sum_univ_three]
      change (Real.cos θ*x 0-Real.sin θ*x 1)^2+
        (Real.sin θ*x 0+Real.cos θ*x 1)^2+x 2^2 = _
      ring
    _ = _ := by simp [h, squaredNorm, Fin.sum_univ_three]

/-- The derivative of the actual rotation curve is the existing ME-055 field. -/
theorem phase_hasDerivAt {θ : ℝ → ℝ} {ω t : ℝ}
    (hθ : HasDerivAt θ ω t) (x : Space) :
    HasDerivAt (fun s => rotate (θ s) x) (rigidRotation ω (rotate (θ t) x)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert (hθ.cos.mul_const (x 0)).sub (hθ.sin.mul_const (x 1)) using 1
    simp [rotate, rigidRotation]
    ring
  · convert (hθ.sin.mul_const (x 0)).add (hθ.cos.mul_const (x 1)) using 1
    simp [rotate, rigidRotation]
    ring
  · simpa [rotate, rigidRotation] using hasDerivAt_const t (x 2)

def flow (ω t : ℝ) (x : Space) : Space := rotate (ω*t) x

theorem flow_hasDerivAt (ω t : ℝ) (x : Space) :
    HasDerivAt (fun s => flow ω s x) (rigidRotation ω (flow ω t x)) t := by
  apply phase_hasDerivAt
  simpa using (hasDerivAt_id t).const_mul ω

theorem flow_add (ω t s : ℝ) (x : Space) :
    flow ω (t+s) x = flow ω t (flow ω s x) := by
  simp only [flow, mul_add, rotate_add]

theorem flow_deriv_curl (ω t : ℝ) (x : Space) :
    curl (fun y => deriv (fun s => flow ω s (rotate (-(ω*t)) y)) t) x =
      ![0,0,2*ω] := by
  have hv : (fun y => deriv (fun s => flow ω s (rotate (-(ω*t)) y)) t) =
      rigidRotation ω := by
    funext y
    rw [(flow_hasDerivAt ω t _).deriv]
    simp [flow, ← rotate_add, rotate_zero]
  rw [hv, rigid_rotation_curl]

/-- Arbitrary constant angular-velocity vector, not required to be a unit axis. -/
def angularField (w : Space) : Field := fun x => cross w x

theorem angular_field_z (ω : ℝ) : angularField ![0,0,ω] = rigidRotation ω := by
  ext x i
  fin_cases i <;> simp [angularField, cross, rigidRotation]

theorem angular_field_curl (w x : Space) : curl (angularField w) x = (2 : ℝ) • w := by
  have hd (i j : Fin 3) : DifferentiableAt ℝ (fun y : Space => w i*y j) x :=
    (differentiableAt_apply j x).const_mul (w i)
  ext i
  fin_cases i <;>
    simp [curl, angularField, cross, partial_sub, partial_const_mul, hd,
      differentiableAt_apply, partial_coordinate] <;> ring

theorem angular_field_divergence (w x : Space) : divergence (angularField w) x = 0 := by
  have hd (i j : Fin 3) : DifferentiableAt ℝ (fun y : Space => w i*y j) x :=
    (differentiableAt_apply j x).const_mul (w i)
  simp [divergence, angularField, cross, Fin.sum_univ_three, partial_sub,
    partial_const_mul, hd, differentiableAt_apply, partial_coordinate]

def dot (w x : Space) : ℝ := ∑ i : Fin 3, w i*x i

theorem angular_field_square (w x : Space) :
    angularField w (angularField w x) = dot w x • w-squaredNorm w • x := by
  ext i
  fin_cases i <;>
    simp [angularField, cross, dot, squaredNorm, Fin.sum_univ_three] <;> ring

theorem unit_axis_hinge_on_plane (n x : Space)
    (hn : squaredNorm n = 1) (hx : dot n x = 0) :
    angularField n (angularField n x) = -x := by
  rw [angular_field_square, hn, hx]
  simp

theorem angular_field_squared_curl (w x : Space) :
    squaredNorm (curl (angularField w) x) = 4*squaredNorm w := by
  rw [angular_field_curl]
  simp [squaredNorm, Fin.sum_univ_three]
  ring

/-- Recover a field only inside the declared rigid family, with origin fixed. -/
theorem reconstruct_rigid_from_curl (w x : Space) :
    angularField ((1/2 : ℝ) • curl (angularField w) x) x = angularField w x := by
  rw [angular_field_curl, smul_smul]
  norm_num

theorem angular_field_curl_nonzero (w x : Space) :
    curl (angularField w) x ≠ 0 ↔ w ≠ 0 := by
  rw [angular_field_curl]
  simp

/-- A supplied limit for angular velocity transfers to the actual curl. -/
theorem residual_curl_tendsto {ω : ℝ → ℝ} {ωinf : ℝ}
    (hω : Tendsto ω atTop (nhds ωinf)) (x : Space) :
    Tendsto (fun t => curl (rigidRotation (ω t)) x) atTop (nhds ![0,0,2*ωinf]) := by
  apply tendsto_pi_nhds.mpr
  intro i
  fin_cases i
  · simp [rigid_rotation_curl]
  · simp [rigid_rotation_curl]
  · simpa [rigid_rotation_curl] using
      (tendsto_const_nhds.mul hω :
        Tendsto (fun t => (2 : ℝ)*ω t) atTop (nhds (2*ωinf)))

theorem residual_limit_nonzero {ωinf : ℝ} (hω : ωinf ≠ 0) :
    (![0,0,2*ωinf] : Space) ≠ 0 := by
  intro h
  have hc := congrFun h 2
  simp at hc
  exact hω hc

end MonolithicAnalysis.RotationKinematics
