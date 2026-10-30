import SpecifiedModels
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! ME-055 in oriented Cartesian real three-space. All partials are actual
Frechet derivatives. Regularity, constant coefficients and orientation are
explicit; no physical velocity field or curved-space interpretation is supplied. -/

noncomputable section
open scoped BigOperators
namespace MonolithicAnalysis.Vorticity

abbrev Space := Fin 3 → ℝ
abbrev Scalar := Space → ℝ
abbrev Field := Space → Space

def basis (i : Fin 3) : Space := Pi.single i 1

def partialD (i : Fin 3) (f : Scalar) (x : Space) : ℝ :=
  fderiv ℝ f x (basis i)

def gradient (f : Scalar) (x : Space) : Space := fun i => partialD i f x

def divergence (v : Field) (x : Space) : ℝ :=
  ∑ i : Fin 3, partialD i (fun y => v y i) x

def cross (u v : Space) : Space :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

/-- ME-055 with the standard (x,y,z) orientation. -/
def curl (v : Field) (x : Space) : Space :=
  ![partialD 1 (fun y => v y 2) x - partialD 2 (fun y => v y 1) x,
    partialD 2 (fun y => v y 0) x - partialD 0 (fun y => v y 2) x,
    partialD 0 (fun y => v y 1) x - partialD 1 (fun y => v y 0) x]

theorem partial_const (i : Fin 3) (a : ℝ) (x : Space) :
    partialD i (fun _ => a) x = 0 := by
  simp [partialD]

theorem partial_coordinate (i j : Fin 3) (x : Space) :
    partialD i (fun y => y j) x = if j = i then 1 else 0 := by
  rw [partialD, (hasFDerivAt_apply j x).fderiv]
  simp [basis, Pi.single_apply, eq_comm]

theorem partial_add (i : Fin 3) {f g : Scalar} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    partialD i (fun y => f y + g y) x = partialD i f x + partialD i g x := by
  simp [partialD, fderiv_fun_add hf hg]

theorem partial_sub (i : Fin 3) {f g : Scalar} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    partialD i (fun y => f y - g y) x = partialD i f x - partialD i g x := by
  simp [partialD, fderiv_fun_sub hf hg]

theorem partial_neg (i : Fin 3) (f : Scalar) (x : Space) :
    partialD i (fun y => -f y) x = -partialD i f x := by
  simp [partialD]

theorem partial_const_mul (i : Fin 3) {f : Scalar} {x : Space}
    (hf : DifferentiableAt ℝ f x) (a : ℝ) :
    partialD i (fun y => a * f y) x = a * partialD i f x := by
  simp [partialD, fderiv_const_mul hf a]

theorem partial_mul (i : Fin 3) {f g : Scalar} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    partialD i (fun y => f y * g y) x =
      f x * partialD i g x + g x * partialD i f x := by
  simp [partialD, fderiv_fun_mul hf hg]

theorem partial_differentiable {f : Scalar} (hf : ContDiff ℝ 2 f) (i : Fin 3) :
    Differentiable ℝ (partialD i f) := by
  have h : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  exact (h.differentiable (by norm_num)).clm_apply (differentiable_const (basis i))

theorem second_partial_eq {f : Scalar} (hf : ContDiff ℝ 2 f)
    (i j : Fin 3) (x : Space) :
    partialD i (partialD j f) x = fderiv ℝ (fderiv ℝ f) x (basis i) (basis j) := by
  have h : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hd := h.differentiable (by norm_num) x
  unfold partialD
  rw [fderiv_clm_apply hd (differentiableAt_const (basis j))]
  simp

/-- Mixed partials commute by the C² Schwarz theorem, not by an assumed symmetry. -/
theorem mixed_partials_commute {f : Scalar} (hf : ContDiff ℝ 2 f)
    (i j : Fin 3) (x : Space) :
    partialD i (partialD j f) x = partialD j (partialD i f) x := by
  rw [second_partial_eq hf, second_partial_eq hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq (basis i) (basis j)

theorem curl_gradient {f : Scalar} (hf : ContDiff ℝ 2 f) (x : Space) :
    curl (gradient f) x = 0 := by
  funext i
  fin_cases i <;> simp [curl, gradient, mixed_partials_commute hf]

theorem curl_const (a : Space) (x : Space) : curl (fun _ => a) x = 0 := by
  funext i
  fin_cases i <;> simp [curl, partial_const]

theorem curl_add {u v : Field} {x : Space}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    curl (fun y => u y + v y) x = curl u x + curl v x := by
  have hu' := differentiableAt_pi.mp hu
  have hv' := differentiableAt_pi.mp hv
  funext i
  fin_cases i <;> simp [curl, partial_add, hu', hv'] <;> ring

theorem curl_neg (v : Field) (x : Space) :
    curl (fun y => -v y) x = -curl v x := by
  funext i
  fin_cases i <;> simp [curl, partial_neg] <;> ring

theorem curl_const_smul {v : Field} {x : Space}
    (hv : DifferentiableAt ℝ v x) (a : ℝ) :
    curl (fun y => a • v y) x = a • curl v x := by
  have hv' := differentiableAt_pi.mp hv
  funext i
  fin_cases i <;> simp [curl, partial_const_mul, hv', Pi.smul_apply, smul_eq_mul] <;> ring

theorem curl_smul {a : Scalar} {v : Field} {x : Space}
    (ha : DifferentiableAt ℝ a x) (hv : DifferentiableAt ℝ v x) :
    curl (fun y => a y • v y) x = cross (gradient a x) (v x) + a x • curl v x := by
  have hv' := differentiableAt_pi.mp hv
  funext i
  fin_cases i <;>
    simp [curl, cross, gradient, partial_mul, ha, hv', Pi.smul_apply, smul_eq_mul] <;> ring

theorem gradient_differentiable {f : Scalar} (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (gradient f) := by
  exact differentiable_pi.mpr (fun i => partial_differentiable hf i)

theorem curl_mul_gradient {a f : Scalar} {x : Space}
    (ha : DifferentiableAt ℝ a x) (hf : ContDiff ℝ 2 f) :
    curl (fun y => a y • gradient f y) x = cross (gradient a x) (gradient f x) := by
  rw [curl_smul ha (gradient_differentiable hf x), curl_gradient hf]
  simp

theorem divergence_curl {v : Field} (hv : ContDiff ℝ 2 v) (x : Space) :
    divergence (curl v) x = 0 := by
  have hc := contDiff_pi.mp hv
  have hd (i j : Fin 3) := partial_differentiable (hc j) i x
  simp only [divergence, Fin.sum_univ_three]
  change partialD 0 (fun y => partialD 1 (fun z => v z 2) y -
      partialD 2 (fun z => v z 1) y) x +
    partialD 1 (fun y => partialD 2 (fun z => v z 0) y -
      partialD 0 (fun z => v z 2) y) x +
    partialD 2 (fun y => partialD 0 (fun z => v z 1) y -
      partialD 1 (fun z => v z 0) y) x = 0
  rw [partial_sub 0 (hd 1 2) (hd 2 1),
    partial_sub 1 (hd 2 0) (hd 0 2), partial_sub 2 (hd 0 1) (hd 1 0)]
  rw [mixed_partials_commute (hc 2) 0 1, mixed_partials_commute (hc 1) 0 2,
    mixed_partials_commute (hc 0) 1 2]
  ring

/-- Adding a smooth gradient changes the field but leaves its vorticity unchanged. -/
theorem curl_gradient_invariant {v : Field} {f : Scalar} {x : Space}
    (hv : DifferentiableAt ℝ v x) (hf : ContDiff ℝ 2 f) :
    curl (fun y => v y + gradient f y) x = curl v x := by
  rw [curl_add hv (gradient_differentiable hf x), curl_gradient hf, add_zero]

theorem gradient_mul {f g : Scalar} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => f y * g y) x = f x • gradient g x + g x • gradient f x := by
  funext i
  exact partial_mul i hf hg

/-- ME-051's force form, using the previously specified scalar potential. -/
def combinedForce (U R : Scalar) (c : ℝ) (x : Space) : Space :=
  -gradient U x + c • gradient R x

theorem combined_force_eq_gradient {U R : Scalar}
    (hU : Differentiable ℝ U) (hR : Differentiable ℝ R) (c : ℝ) :
    combinedForce U R c = gradient (Force.combinedPotential U R c) := by
  funext x i
  change -partialD i U x + c * partialD i R x =
    partialD i (fun y => -U y + c * R y) x
  rw [partial_add (f := fun y => -U y) i (hU x).neg ((hR x).const_mul c), partial_neg,
    partial_const_mul i (hR x) c]

theorem combined_force_curl_zero {U R : Scalar}
    (hU : ContDiff ℝ 2 U) (hR : ContDiff ℝ 2 R) (c : ℝ) (x : Space) :
    curl (combinedForce U R c) x = 0 := by
  rw [combined_force_eq_gradient (hU.differentiable (by norm_num))
    (hR.differentiable (by norm_num)) c]
  exact curl_gradient (hU.neg.add (contDiff_const.mul hR)) x

/-- ME-053's coefficients are spatial constants. Nonzero mass is the application domain. -/
def scaledForce (phi : Scalar) (beta mass : ℝ) (x : Space) : Space :=
  (-(beta / mass)) • gradient phi x

theorem scaled_force_eq_gradient {phi : Scalar} (hphi : Differentiable ℝ phi)
    (beta mass : ℝ) :
    scaledForce phi beta mass = gradient (Force.scaledPotential phi beta mass) := by
  funext x i
  exact (partial_const_mul i (hphi x) (-(beta / mass))).symm

theorem scaled_force_curl_zero {phi : Scalar} (hphi : ContDiff ℝ 2 phi)
    (beta mass : ℝ) (x : Space) : curl (scaledForce phi beta mass) x = 0 := by
  rw [scaled_force_eq_gradient (hphi.differentiable (by norm_num)) beta mass]
  exact curl_gradient (contDiff_const.mul hphi) x

def rigidRotation (ω : ℝ) (x : Space) : Space := ![-ω * x 1, ω * x 0, 0]

theorem rigid_rotation_curl (ω : ℝ) (x : Space) :
    curl (rigidRotation ω) x = ![0, 0, 2 * ω] := by
  funext i
  fin_cases i <;>
    simp [curl, rigidRotation, partial_const_mul, differentiableAt_apply,
      partial_coordinate, partial_const, partial_neg]
  ring

theorem rigid_rotation_divergence (ω : ℝ) (x : Space) :
    divergence (rigidRotation ω) x = 0 := by
  simp [divergence, rigidRotation, Fin.sum_univ_three,
    partial_const_mul, differentiableAt_apply, partial_coordinate, partial_const, partial_neg]

theorem rigid_rotation_squared_curl (ω : ℝ) (x : Space) :
    (∑ i : Fin 3, (curl (rigidRotation ω) x i) ^ 2) = 4 * ω ^ 2 := by
  rw [rigid_rotation_curl]
  simp [Fin.sum_univ_three]
  ring

/-- Varying coupling can break zero curl: x * grad(y) has nonzero curl. -/
theorem variable_coupling_counterexample (x : Space) :
    curl (fun y => y 0 • gradient (fun z => z 1) y) x = ![0, 0, 1] := by
  rw [curl_mul_gradient (differentiableAt_apply 0 x) (contDiff_apply ℝ ℝ 1)]
  funext i
  fin_cases i <;> simp [cross, gradient, partial_coordinate]

/-- The extra product-rule term restores a true gradient and hence zero curl. -/
theorem full_product_gradient_curl (x : Space) :
    curl (fun y => y 0 • gradient (fun z => z 1) y +
      y 1 • gradient (fun z => z 0) y) x = 0 := by
  have h : (fun y : Space => y 0 • gradient (fun z => z 1) y +
      y 1 • gradient (fun z => z 0) y) = gradient (fun y => y 0 * y 1) := by
    funext y
    exact (gradient_mul (differentiableAt_apply 0 y) (differentiableAt_apply 1 y)).symm
  rw [h]
  exact curl_gradient ((contDiff_apply ℝ ℝ 0).mul (contDiff_apply ℝ ℝ 1)) x

end MonolithicAnalysis.Vorticity
