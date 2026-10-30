import Vorticity

/-! Cartesian fluid identities for ME-077 and ME-080. The shear convention is
authored explicitly. Every spatial/time derivative is an actual fderiv/deriv;
no relativistic geometry, constitutive identification or PDE existence is assumed. -/

noncomputable section
open scoped BigOperators
namespace MonolithicAnalysis.Fluids
open Vorticity

abbrev Tensor := Fin 3 → Fin 3 → ℝ
abbrev Density := ℝ → Scalar
abbrev Velocity := ℝ → Field

def dot (a b : Space) : ℝ := ∑ i, a i * b i

def laplacian (u : Field) (x : Space) : Space :=
  fun i => ∑ j, partialD j (partialD j (fun y => u y i)) x

def symmetricGradient (u : Field) (x : Space) : Tensor :=
  fun i j => partialD j (fun y => u y i) x + partialD i (fun y => u y j) x

/-- Unhalved, trace-free Cartesian strain in three dimensions; no bulk viscosity. -/
def shear (u : Field) (x : Space) : Tensor :=
  fun i j => symmetricGradient u x i j - if i = j then (2 / 3 : ℝ) * divergence u x else 0

def tensorDivergence (T : Space → Tensor) (x : Space) : Space :=
  fun i => ∑ j, partialD j (fun y => T y i j) x

def viscousForce (η : Scalar) (u : Field) : Field :=
  tensorDivergence (fun x i j => η x * shear u x i j)

def viscosityCorrection (η : Scalar) (u : Field) (x : Space) : Space :=
  fun i => ∑ j, partialD j η x * shear u x i j

theorem partial_sum (i : Fin 3) {f : Fin 3 → Scalar} {x : Space}
    (hf : ∀ j, DifferentiableAt ℝ (f j) x) :
    partialD i (fun y => ∑ j, f j y) x = ∑ j, partialD i (f j) x := by
  simp [partialD, fderiv_fun_sum (fun j _ => hf j)]

theorem divergence_differentiable {u : Field} (hu : ContDiff ℝ 2 u) :
    Differentiable ℝ (divergence u) := by
  exact Differentiable.fun_sum fun i _ => partial_differentiable (contDiff_pi.mp hu i) i

theorem partial_divergence {u : Field} (hu : ContDiff ℝ 2 u)
    (i : Fin 3) (x : Space) :
    partialD i (divergence u) x = ∑ j, partialD i (partialD j (fun y => u y j)) x := by
  exact partial_sum i (fun j => partial_differentiable (contDiff_pi.mp hu j) j x)

theorem shear_symmetric (u : Field) (x : Space) (i j : Fin 3) :
    shear u x i j = shear u x j i := by
  simp [shear, symmetricGradient, eq_comm, add_comm]

theorem shear_trace_zero (u : Field) (x : Space) :
    (∑ i, shear u x i i) = 0 := by
  simp [shear, symmetricGradient, divergence, Fin.sum_univ_three]
  ring

theorem shear_differentiable {u : Field} (hu : ContDiff ℝ 2 u) (i j : Fin 3) :
    Differentiable ℝ (fun x => shear u x i j) := by
  have hd := (partial_differentiable (contDiff_pi.mp hu i) j).add
    (partial_differentiable (contDiff_pi.mp hu j) i)
  by_cases hij : i = j
  · simpa [shear, symmetricGradient, hij] using
      hd.sub ((divergence_differentiable hu).const_mul (2 / 3 : ℝ))
  · simpa [shear, symmetricGradient, hij] using hd

theorem symmetric_gradient_divergence {u : Field} (hu : ContDiff ℝ 2 u) (x : Space) :
    tensorDivergence (symmetricGradient u) x = laplacian u x + Vorticity.gradient (divergence u) x := by
  funext i
  have hc := contDiff_pi.mp hu
  have hd (j k : Fin 3) := partial_differentiable (hc k) j x
  simp only [tensorDivergence, symmetricGradient, laplacian, Vorticity.gradient, Pi.add_apply,
    partial_add _ (hd _ _) (hd _ _), partial_divergence hu, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => mixed_partials_commute (hc j) j i x)

theorem shear_divergence {u : Field} (hu : ContDiff ℝ 2 u) (x : Space) :
    tensorDivergence (shear u) x = laplacian u x + (1 / 3 : ℝ) • Vorticity.gradient (divergence u) x := by
  have hc := contDiff_pi.mp hu
  have hd (j k : Fin 3) := partial_differentiable (hc k) j x
  have hs (i j : Fin 3) : DifferentiableAt ℝ (fun y => symmetricGradient u y i j) x :=
    (hd j i).add (hd i j)
  have hdiag (i : Fin 3) :
      (∑ j, partialD j (fun y => if i = j then (2 / 3 : ℝ) * divergence u y else 0) x) =
        (2 / 3 : ℝ) * partialD i (divergence u) x := by
    fin_cases i <;>
      simp [Fin.sum_univ_three, partial_const_mul, divergence_differentiable hu x, partial_const]
  funext i
  have hi := congrFun (symmetric_gradient_divergence hu x) i
  change (∑ j, partialD j (fun y => symmetricGradient u y i j -
      if i = j then (2 / 3 : ℝ) * divergence u y else 0) x) = _
  have hsub (j : Fin 3) := partial_sub j (hs i j)
    (by
      by_cases hij : i = j
      · simpa [hij] using (divergence_differentiable hu x).const_mul (2 / 3 : ℝ)
      · simp only [hij, if_false]
        exact differentiableAt_const 0 : DifferentiableAt ℝ
      (fun y => if i = j then (2 / 3 : ℝ) * divergence u y else 0) x)
  simp only [hsub, Finset.sum_sub_distrib]
  rw [hdiag]
  change tensorDivergence (symmetricGradient u) x i - _ = _
  rw [hi]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Vorticity.gradient]
  ring

theorem viscous_force_product {η : Scalar} {u : Field} {x : Space}
    (hη : DifferentiableAt ℝ η x) (hu : ContDiff ℝ 2 u) :
    viscousForce η u x = viscosityCorrection η u x +
      η x • (laplacian u x + (1 / 3 : ℝ) • Vorticity.gradient (divergence u) x) := by
  rw [← shear_divergence hu x]
  funext i
  simp only [viscousForce, tensorDivergence, viscosityCorrection, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, partial_mul _ hη (shear_differentiable hu _ _ x),
    Finset.sum_add_distrib, Finset.mul_sum]
  simp only [mul_comm, add_comm]

/-- eta may depend on time; this statement fixes a time and requires spatial constancy only. -/
theorem viscous_force_constant (η : ℝ) {u : Field} (hu : ContDiff ℝ 2 u) (x : Space) :
    viscousForce (fun _ => η) u x =
      η • (laplacian u x + (1 / 3 : ℝ) • Vorticity.gradient (divergence u) x) := by
  rw [viscous_force_product (differentiableAt_const η) hu]
  have hc : viscosityCorrection (fun _ => η) u x = 0 := by
    funext i
    simp [viscosityCorrection, partial_const]
  rw [hc, zero_add]

theorem incompressible_viscous_force (η : ℝ) {u : Field}
    (hu : ContDiff ℝ 2 u) (hdiv : ∀ x, divergence u x = 0) (x : Space) :
    viscousForce (fun _ => η) u x = η • laplacian u x := by
  rw [viscous_force_constant η hu]
  have heq : divergence u = fun _ => 0 := funext hdiv
  have hz : Vorticity.gradient (fun _ => 0) x = 0 := by
    funext i
    exact partial_const i 0 x
  rw [heq, hz]
  simp

/-- Pointwise viscous work equals half the squared shear; this is not an integral energy law. -/
theorem shear_work (u : Field) (x : Space) :
    (∑ i, ∑ j, shear u x i j * partialD j (fun y => u y i) x) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, (shear u x i j) ^ 2 := by
  simp [shear, symmetricGradient, divergence, Fin.sum_univ_three]
  ring

theorem viscous_work_nonnegative (η : ℝ) (hη : 0 ≤ η) (u : Field) (x : Space) :
    0 ≤ ∑ i, ∑ j, (η * shear u x i j) * partialD j (fun y => u y i) x := by
  have heq : (∑ i, ∑ j, (η * shear u x i j) * partialD j (fun y => u y i) x) =
      η * (∑ i, ∑ j, shear u x i j * partialD j (fun y => u y i) x) := by
    simp only [Finset.mul_sum, mul_assoc]
  rw [heq, shear_work]
  positivity

theorem divergence_smul {ρ : Scalar} {u : Field} {x : Space}
    (hρ : DifferentiableAt ℝ ρ x) (hu : DifferentiableAt ℝ u x) :
    divergence (fun y => ρ y • u y) x = dot (u x) (Vorticity.gradient ρ x) + ρ x * divergence u x := by
  have hc := differentiableAt_pi.mp hu
  simp only [divergence, dot, Vorticity.gradient, Pi.smul_apply, smul_eq_mul,
    partial_mul _ hρ (hc _), Finset.sum_add_distrib, Finset.mul_sum]
  ring

def timeD (ρ : Density) (t : ℝ) (x : Space) : ℝ := deriv (fun s => ρ s x) t

def materialD (ρ : Density) (u : Velocity) (t : ℝ) (x : Space) : ℝ :=
  timeD ρ t x + dot (u t x) (Vorticity.gradient (ρ t) x)

/-- ME-080 with its historical sign unchanged. -/
def continuity (ρ : Density) (u : Velocity) (t : ℝ) (x : Space) : ℝ :=
  timeD ρ t x + divergence (fun y => ρ t y • u t y) x

/-- Differentiability is part of the solution predicate, so totalized derivatives
do not classify a nondifferentiable field as a classical solution. -/
def SolvesContinuity (ρ : Density) (u : Velocity) : Prop :=
  (∀ t x, DifferentiableAt ℝ (fun s => ρ s x) t) ∧
  (∀ t, Differentiable ℝ (ρ t)) ∧
  (∀ t, Differentiable ℝ (u t)) ∧
  ∀ t x, continuity ρ u t x = 0

theorem continuity_material {ρ : Density} {u : Velocity} {t : ℝ} {x : Space}
    (hρ : DifferentiableAt ℝ (ρ t) x) (hu : DifferentiableAt ℝ (u t) x) :
    continuity ρ u t x = materialD ρ u t x + ρ t x * divergence (u t) x := by
  rw [continuity, divergence_smul hρ hu]
  simp only [materialD]
  ring

theorem continuity_iff_material {ρ : Density} {u : Velocity} {t : ℝ} {x : Space}
    (hρ : DifferentiableAt ℝ (ρ t) x) (hu : DifferentiableAt ℝ (u t) x) :
    continuity ρ u t x = 0 ↔ materialD ρ u t x = -ρ t x * divergence (u t) x := by
  rw [continuity_material hρ hu]
  constructor <;> intro h <;> linarith

theorem incompressible_continuity_iff {ρ : Density} {u : Velocity} {t : ℝ} {x : Space}
    (hρ : DifferentiableAt ℝ (ρ t) x) (hu : DifferentiableAt ℝ (u t) x)
    (hdiv : divergence (u t) x = 0) :
    continuity ρ u t x = 0 ↔ materialD ρ u t x = 0 := by
  rw [continuity_material hρ hu, hdiv]
  simp

theorem constant_density_continuity (r : ℝ) (u : Velocity) (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (u t) x) :
    continuity (fun _ _ => r) u t x = r * divergence (u t) x := by
  rw [continuity_material (differentiableAt_const r) hu]
  simp [materialD, timeD, Vorticity.gradient, dot, partial_const]

theorem nonzero_constant_density_iff (r : ℝ) (hr : r ≠ 0)
    (u : Velocity) (t : ℝ) (x : Space) (hu : DifferentiableAt ℝ (u t) x) :
    continuity (fun _ _ => r) u t x = 0 ↔ divergence (u t) x = 0 := by
  rw [constant_density_continuity r u t x hu]
  exact mul_eq_zero.trans (or_iff_right hr)

/-- Conservative momentum includes a continuity residual until mass conservation is imposed. -/
def conservativeMomentum (ρ : Density) (u : Velocity) (t : ℝ) (x : Space) : Space :=
  fun i => deriv (fun s => ρ s x * u s x i) t +
    divergence (fun y => (ρ t y * u t y i) • u t y) x

def acceleration (u : Velocity) (t : ℝ) (x : Space) : Space :=
  fun i => materialD (fun s y => u s y i) u t x

theorem momentum_transport {ρ : Density} {u : Velocity} {t : ℝ} {x : Space}
    (hρt : DifferentiableAt ℝ (fun s => ρ s x) t)
    (hut : DifferentiableAt ℝ (fun s => u s x) t)
    (hρx : DifferentiableAt ℝ (ρ t) x) (hux : DifferentiableAt ℝ (u t) x) :
    conservativeMomentum ρ u t x =
      ρ t x • acceleration u t x + continuity ρ u t x • u t x := by
  have ht := differentiableAt_pi.mp hut
  have hx := differentiableAt_pi.mp hux
  rw [continuity_material hρx hux]
  funext i
  simp only [conservativeMomentum, deriv_fun_mul hρt (ht i)]
  rw [divergence_smul (ρ := fun y => ρ t y * u t y i) (u := u t) (hρx.mul (hx i)) hux,
    Vorticity.gradient_mul hρx (hx i)]
  simp only [acceleration, materialD, timeD, dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_three]
  ring

theorem momentum_of_continuity {ρ : Density} {u : Velocity} {t : ℝ} {x : Space}
    (hρt : DifferentiableAt ℝ (fun s => ρ s x) t)
    (hut : DifferentiableAt ℝ (fun s => u s x) t)
    (hρx : DifferentiableAt ℝ (ρ t) x) (hux : DifferentiableAt ℝ (u t) x)
    (hmass : continuity ρ u t x = 0) :
    conservativeMomentum ρ u t x = ρ t x • acceleration u t x := by
  rw [momentum_transport hρt hut hρx hux, hmass]
  simp

def momentumResidual (ρ : Density) (u : Velocity) (P η : Density)
    (external : Velocity) (t : ℝ) (x : Space) : Space :=
  ρ t x • acceleration u t x + Vorticity.gradient (P t) x - viscousForce (η t) (u t) x - external t x

/-- The source's eta(t) is spatially constant; no time derivative of eta appears here. -/
theorem momentum_residual_constant_viscosity (ρ : Density) (u : Velocity)
    (P : Density) (η : ℝ → ℝ) (external : Velocity) (t : ℝ) (x : Space)
    (hu : ContDiff ℝ 2 (u t)) :
    momentumResidual ρ u P (fun s _ => η s) external t x =
      ρ t x • acceleration u t x + Vorticity.gradient (P t) x -
        η t • (laplacian (u t) x + (1 / 3 : ℝ) • Vorticity.gradient (divergence (u t)) x) -
        external t x := by
  rw [momentumResidual, viscous_force_constant (η t) hu]

def dilation (a : ℝ) : Field := fun x => a • x

theorem dilation_smooth (a : ℝ) : ContDiff ℝ 2 (dilation a) := by
  change ContDiff ℝ 2 (fun x : Space => a • x)
  fun_prop

theorem dilation_divergence (a : ℝ) (x : Space) : divergence (dilation a) x = 3 * a := by
  simp [divergence, dilation, Pi.smul_apply, smul_eq_mul,
    partial_const_mul, differentiableAt_apply, partial_coordinate]

theorem dilation_shear (a : ℝ) (x : Space) : shear (dilation a) x = 0 := by
  funext i j
  simp [shear, symmetricGradient, dilation_divergence, dilation, Pi.smul_apply,
    smul_eq_mul, partial_const_mul, differentiableAt_apply, partial_coordinate]
  by_cases hij : i = j <;> simp [hij, Ne.symm, eq_comm]
  ring

def expandingDensity (r a : ℝ) : Density := fun t _ => r * Real.exp (-(3 * a) * t)

theorem expanding_density_timeD (r a t : ℝ) (x : Space) :
    timeD (expandingDensity r a) t x = -(3 * a) * expandingDensity r a t x := by
  have h := (((hasDerivAt_id t).const_mul (-(3 * a))).exp).const_mul r
  change deriv (fun s => r * Real.exp (-(3 * a) * s)) t = _
  convert h.deriv using 1
  simp only [id_eq, expandingDensity]
  ring

theorem expanding_density_positive {r : ℝ} (hr : 0 < r) (a t : ℝ) (x : Space) :
    0 < expandingDensity r a t x :=
  mul_pos hr (Real.exp_pos _)

theorem expanding_density_initial (r a : ℝ) (x : Space) :
    expandingDensity r a 0 x = r := by
  simp [expandingDensity]

/-- A compressible three-dimensional solution of continuity, not a solution of all fluid equations. -/
theorem expanding_continuity (r a t : ℝ) (x : Space) :
    continuity (expandingDensity r a) (fun _ => dilation a) t x = 0 := by
  have hu := (dilation_smooth a).differentiable (by norm_num) x
  rw [continuity_material (ρ := expandingDensity r a) (u := fun _ => dilation a)
    (t := t) (differentiableAt_const _) hu]
  simp only [materialD, expanding_density_timeD, dilation_divergence]
  have hg : Vorticity.gradient (expandingDensity r a t) x = 0 := by
    funext i
    exact partial_const i _ x
  rw [hg]
  simp only [dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  ring

theorem expanding_solution (r a : ℝ) :
    SolvesContinuity (expandingDensity r a) (fun _ => dilation a) := by
  refine ⟨?_, ?_, ?_, expanding_continuity r a⟩
  · intro t x
    exact ((((hasDerivAt_id t).const_mul (-(3 * a))).exp).const_mul r).differentiableAt
  · intro t
    exact differentiable_const _
  · intro t
    exact (dilation_smooth a).differentiable (by norm_num)

/-- Constant positive density alone does not imply the continuity equation. -/
theorem constant_density_expansion_counterexample (t : ℝ) (x : Space) :
    continuity (fun _ _ => 1) (fun _ => dilation 1) t x = 3 := by
  rw [constant_density_continuity 1 _ t x
    ((dilation_smooth 1).differentiable (by norm_num) x), dilation_divergence]
  norm_num

def linearShear : Field := fun x => ![x 1, 0, 0]

theorem linear_shear_smooth : ContDiff ℝ 2 linearShear := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [linearShear] <;> fun_prop

theorem linear_shear_divergence (x : Space) : divergence linearShear x = 0 := by
  simp [divergence, linearShear, Fin.sum_univ_three, partial_coordinate, partial_const]

theorem linear_shear_tensor (x : Space) :
    shear linearShear x = ![![0, 1, 0], ![1, 0, 0], ![0, 0, 0]] := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [shear, symmetricGradient, linear_shear_divergence, linearShear,
      partial_coordinate, partial_const]

theorem linear_shear_laplacian (x : Space) : laplacian linearShear x = 0 := by
  have hc (i j : Fin 3) : partialD i (fun y : Space => y j) =
      fun _ => if j = i then 1 else 0 := funext (partial_coordinate i j)
  have hz (i : Fin 3) : partialD i (fun _ => (0 : ℝ)) = fun _ => 0 :=
    funext (partial_const i 0)
  funext i
  fin_cases i <;>
    simp [laplacian, linearShear, hc, hz, partial_const]

theorem linear_shear_viscous_force (η : Scalar) (x : Space) :
    viscousForce η linearShear x = ![partialD 1 η x, partialD 0 η x, 0] := by
  funext i
  fin_cases i <;>
    simp [viscousForce, tensorDivergence, linear_shear_tensor, Fin.sum_univ_three, partial_const]

/-- Strictly positive viscosity everywhere; at y=1 the omitted correction is (2,0,0). -/
def varyingViscosity : Scalar := fun x => x 1 * x 1 + 1

theorem varying_viscosity_positive (x : Space) : 0 < varyingViscosity x := by
  unfold varyingViscosity
  nlinarith [sq_nonneg (x 1)]

theorem varying_viscosity_counterexample :
    viscousForce varyingViscosity linearShear ![0, 1, 0] = ![2, 0, 0] ∧
      laplacian linearShear ![0, 1, 0] = 0 := by
  constructor
  · change viscousForce (fun x => x 1 * x 1 + 1) linearShear ![0, 1, 0] = _
    rw [linear_shear_viscous_force]
    funext i
    fin_cases i <;>
      simp [partial_add, partial_mul, differentiableAt_apply,
        differentiableAt_const, partial_coordinate, partial_const]
    norm_num
  · exact linear_shear_laplacian _

end MonolithicAnalysis.Fluids
