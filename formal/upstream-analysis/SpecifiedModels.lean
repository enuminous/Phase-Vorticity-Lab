import CatalogueAnalysis
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

/-! Explicit mathematical completions of underdetermined working constructs.
The conventions in SPECIFICATIONS.md are part of the target. A coordinate model
or counterexample does not establish a physical interpretation. -/
noncomputable section
open scoped BigOperators
namespace MonolithicAnalysis

namespace NullPairs
/-- ME-087: the real coordinate algebra, with coordinatewise multiplication.
This is a commutative algebra with zero divisors, not a division algebra. -/
abbrev Algebra (n : ℕ) := Fin n → ℝ
def basis (n : ℕ) (i : Fin n) : Algebra n := Pi.single i 1

theorem basis_ne_zero (n : ℕ) (i : Fin n) : basis n i ≠ 0 := by
  intro h
  have := congrFun h i
  simp [basis] at this

theorem basis_mul (n : ℕ) (i j : Fin n) :
    basis n i * basis n j = if i = j then basis n i else 0 := by
  ext k
  by_cases h : i = j
  · subst j
    by_cases hk : k = i <;> simp_all [basis, Pi.single_apply]
  · by_cases hk : k = i <;> by_cases hl : k = j <;> simp_all [basis, Pi.single_apply]

theorem null_pair_iff (n : ℕ) (i j : Fin n) :
    basis n i * basis n j = 0 ↔ i ≠ j := by
  rw [basis_mul]
  by_cases h : i = j <;> simp [h, basis_ne_zero]

theorem basis_partition_of_unity (n : ℕ) : ∑ i : Fin n, basis n i = 1 := by
  ext k
  simp [basis, Finset.sum_apply, Pi.single_apply]
end NullPairs

namespace Dyad
/-- ME-066: canonical coordinate realization of H ⊕ A ⊕ (H ⊗ A).
The tensor block is the Kronecker product in the chosen finite bases. -/
abbrev Index (m n : ℕ) := Sum (Fin m) (Sum (Fin n) (Fin m × Fin n))
def raw {m n : ℕ} (h : Fin m → ℂ) (a : Fin n → ℂ) (coupling : ℂ) :
    Index m n → ℂ
  | .inl i => h i
  | .inr (.inl j) => a j
  | .inr (.inr (i,j)) => coupling * h i * a j

def squaredNorm {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ :=
  ∑ i, Complex.normSq (v i)

theorem raw_squaredNorm {m n : ℕ} (h : Fin m → ℂ) (a : Fin n → ℂ) (c : ℂ) :
    squaredNorm (raw h a c) = squaredNorm h + squaredNorm a +
      Complex.normSq c * squaredNorm h * squaredNorm a := by
  simp only [squaredNorm, Fintype.sum_sum_type, raw, Fintype.sum_prod_type,
    map_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem raw_nonzero_left {m n : ℕ} (h : Fin m → ℂ) (a : Fin n → ℂ) (c : ℂ)
    (hh : ∃ i, h i ≠ 0) : ∃ k, raw h a c k ≠ 0 := by
  obtain ⟨i, hi⟩ := hh
  exact ⟨.inl i, hi⟩

/-- N is positive real L² normalization, applied to all three blocks together. -/
def normalized {m n : ℕ} (h : Fin m → ℂ) (a : Fin n → ℂ) (c : ℂ) :
    Index m n → ℂ := fun k =>
  ((Real.sqrt (squaredNorm (raw h a c)))⁻¹ : ℂ) * raw h a c k

theorem normalized_squaredNorm {m n : ℕ} (h : Fin m → ℂ) (a : Fin n → ℂ) (c : ℂ)
    (hv : ∃ k, raw h a c k ≠ 0) : squaredNorm (normalized h a c) = 1 := by
  have hp : 0 < squaredNorm (raw h a c) := by
    obtain ⟨k,hk⟩ := hv
    apply Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _)
    exact ⟨k, Finset.mem_univ _, (Complex.normSq_pos).mpr hk⟩
  simp only [normalized, squaredNorm, map_mul, ← Finset.mul_sum]
  have hs := Real.sq_sqrt hp.le
  simp only [Complex.normSq_inv, Complex.normSq_ofReal, ← pow_two]
  change (Real.sqrt (squaredNorm (raw h a c)) ^ 2)⁻¹ * squaredNorm (raw h a c) = 1
  rw [hs]
  exact inv_mul_cancel₀ (ne_of_gt hp)
end Dyad

namespace TensorModels
abbrev Index := Fin 4
abbrev Tensor := Index → Index → ℝ
/-- A fixed coordinate metric and inverse; inverse and geometric compatibility
are separate conditions, not smuggled into algebraic identities. -/
def contraction (inverse : Tensor) (p : Index → ℝ) : ℝ :=
  ∑ i, ∑ j, inverse i j * p i * p j
/-- ME-015 and ME-040 share this scalar stress construction. -/
def scalarStress (g inverse : Tensor) (p : Index → ℝ) (potential : ℝ) : Tensor :=
  fun i j => p i * p j - g i j * (contraction inverse p / 2 + potential)
/-- ME-010. -/
def scalarLagrangian (inverse : Tensor) (p : Index → ℝ) (potential : ℝ) : ℝ :=
  -contraction inverse p / 2 - potential
/-- ME-006; R is an additional tensor, not identified with Ricci curvature. -/
def information (g inverse : Tensor) (p : Index → ℝ) (potential : ℝ) (R : Tensor) : Tensor :=
  fun i j => p i * p j - g i j * contraction inverse p / 2 - g i j * potential + R i j

theorem information_eq_stress_add (g inverse : Tensor) (p : Index → ℝ)
    (V : ℝ) (R : Tensor) : information g inverse p V R = scalarStress g inverse p V + R := by
  ext i j
  simp only [information, scalarStress, Pi.add_apply]
  ring

theorem stress_symmetric (g inverse : Tensor) (p : Index → ℝ) (V : ℝ)
    (hg : ∀ i j, g i j = g j i) : ∀ i j,
    scalarStress g inverse p V i j = scalarStress g inverse p V j i := by
  intro i j
  simp only [scalarStress, hg i j, mul_comm (p i) (p j)]

theorem stress_eq_gradient_plus_metric_lagrangian
    (g inverse : Tensor) (p : Index → ℝ) (V : ℝ) (i j : Index) :
    scalarStress g inverse p V i j =
      p i * p j + g i j * scalarLagrangian inverse p V := by
  unfold scalarStress scalarLagrangian
  ring

/-- ME-007 and ME-008 as coordinate residuals, with all couplings explicit. -/
def compactResidual (G g T I : Tensor) (cosmological grav coupling : ℝ) : Tensor :=
  fun i j => G i j + cosmological * g i j -
    8 * Real.pi * grav * (T i j + coupling * I i j)
def expandedResidual (G g inverse T R : Tensor) (p : Index → ℝ)
    (V cosmological grav coupling : ℝ) : Tensor :=
  fun i j => G i j + cosmological * g i j -
    (8 * Real.pi * grav * T i j + 8 * Real.pi * grav * coupling *
      (p i * p j - g i j * contraction inverse p / 2 - g i j * V + R i j))

theorem einstein_residual_expansion (G g inverse T R : Tensor) (p : Index → ℝ)
    (V cosmological grav coupling : ℝ) :
    compactResidual G g T (information g inverse p V R) cosmological grav coupling =
    expandedResidual G g inverse T R p V cosmological grav coupling := by
  ext i j
  unfold compactResidual expandedResidual information
  ring

theorem decoupling (G g T I : Tensor) (cosmological grav : ℝ) :
    compactResidual G g T I cosmological grav 0 =
      fun i j => G i j + cosmological * g i j - 8 * Real.pi * grav * T i j := by
  ext i j
  simp [compactResidual]

/-- ME-067: the dyad contribution is explicitly symmetrized. -/
def cognition (g inverse : Tensor) (p M O : Index → ℝ) (coupling : ℝ) : Tensor :=
  fun i j => p i * p j - g i j * contraction inverse p / 2 +
    coupling * (M i * O j + M j * O i)

theorem cognition_symmetric (g inverse : Tensor) (p M O : Index → ℝ) (c : ℝ)
    (hg : ∀ i j, g i j = g j i) : ∀ i j,
    cognition g inverse p M O c i j = cognition g inverse p M O c j i := by
  intro i j
  unfold cognition
  rw [hg i j]
  ring

/-- ME-068, also the tensor sum used on the right of ME-039. -/
def coupledStress (C I : Tensor) (chi : ℝ) : Tensor := fun i j => C i j + chi * I i j

theorem coupled_symmetric (C I : Tensor) (chi : ℝ)
    (hC : ∀ i j, C i j = C j i) (hI : ∀ i j, I i j = I j i) :
    ∀ i j, coupledStress C I chi i j = coupledStress C I chi j i := by
  intro i j
  simp [coupledStress, hC i j, hI i j]

/-- ME-081: stress of an explicitly given fluid state. Constitutive dynamics
and whether the state solves them are not contained in this definition. -/
def fluidStress (g shear : Tensor) (u : Index → ℝ) (density pressure viscosity : ℝ) : Tensor :=
  fun i j => (density + pressure) * u i * u j + pressure * g i j + viscosity * shear i j

theorem fluid_symmetric (g shear : Tensor) (u : Index → ℝ) (density pressure viscosity : ℝ)
    (hg : ∀ i j, g i j = g j i) (hs : ∀ i j, shear i j = shear j i) :
    ∀ i j, fluidStress g shear u density pressure viscosity i j =
      fluidStress g shear u density pressure viscosity j i := by
  intro i j
  unfold fluidStress
  rw [hg i j, hs i j]
  ring
end TensorModels

namespace Force
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
/-- ME-052: positions and velocities are independent coordinates. The force
below differentiates position while holding velocity and memory fixed. -/
def discrepancy (x memory velocity memoryVelocity : E) (k eta gamma : ℝ)
    (recursion : E → ℝ) : ℝ :=
  k * ‖x - memory‖ ^ 2 + eta * ‖velocity - memoryVelocity‖ ^ 2 - gamma * recursion x

theorem discrepancy_hasGradient (memory velocity memoryVelocity : E) (k eta gamma : ℝ)
    (recursion : E → ℝ) (grad x : E) (hr : HasGradientAt recursion grad x) :
    HasGradientAt (fun y => discrepancy y memory velocity memoryVelocity k eta gamma recursion)
      ((2*k) • (x-memory) - gamma • grad) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hn := ((hasFDerivAt_id x).sub_const memory).norm_sq
  have hd := ((hn.const_mul k).add_const (eta * ‖velocity-memoryVelocity‖^2)).sub
    (hr.hasFDerivAt.const_mul gamma)
  convert hd using 1
  ext d
  simp [InnerProductSpace.toDual_apply_apply, mul_assoc]
  ring

def combinedPotential (U R : E → ℝ) (c : ℝ) (x : E) : ℝ := -U x + c*R x

def scaledPotential (phi : E → ℝ) (beta mass : ℝ) (x : E) : ℝ := -(beta/mass)*phi x

/-- ME-051: this follows from differentiating the specified combined potential. -/
theorem combined_potential_hasGradient (U R : E → ℝ) (u r x : E) (c : ℝ)
    (hU : HasGradientAt U u x) (hR : HasGradientAt R r x) :
    HasGradientAt (combinedPotential U R c) (-u + c • r) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hU.hasFDerivAt.neg.add (hR.hasFDerivAt.const_mul c) using 1
  ext d
  simp

/-- ME-053 is the negative gradient of the rescaled scalar potential. -/
theorem scaled_potential_hasGradient (phi : E → ℝ) (p x : E) (beta mass : ℝ)
    (hp : HasGradientAt phi p x) :
    HasGradientAt (scaledPotential phi beta mass) (-(beta/mass) • p) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hp.hasFDerivAt.const_mul (-(beta/mass)) using 1
  ext d
  simp
end Force

namespace Cosmology
/-- ME-056, with nonzero scale factor a required by the model domain. -/
def rateSquared (grav density cosmological curvature scale rotation : ℝ) : ℝ :=
  (8*Real.pi*grav/3)*density + cosmological/3 - curvature/scale^2 + rotation^2/scale^2

theorem rotation_nonnegative (G rho L k a w : ℝ) :
    rateSquared G rho L k a 0 ≤ rateSquared G rho L k a w := by
  have : 0 ≤ w^2/a^2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  simp only [rateSquared, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero]
  linarith

theorem real_rate_exists_iff (G rho L k a w : ℝ) :
    (∃ H : ℝ, H^2 = rateSquared G rho L k a w) ↔
      0 ≤ rateSquared G rho L k a w := by
  constructor
  · rintro ⟨H,hH⟩; rw [← hH]; exact sq_nonneg H
  · intro h; exact ⟨Real.sqrt _, Real.sq_sqrt h⟩
end Cosmology

namespace Toroidal
/-- A real unit-circle point. The torus domain is the product of two circles. -/
@[ext] structure CirclePoint where
  re : ℝ
  im : ℝ
  onCircle : re^2 + im^2 = 1

def embed (R r : ℝ) (p : CirclePoint × CirclePoint) : ℝ × ℝ × ℝ :=
  ((R+r*p.1.re)*p.2.re, (R+r*p.1.re)*p.2.im, r*p.1.im)

theorem radial_positive (R r : ℝ) (hr : 0 < r) (hR : r < R) (u : CirclePoint) :
    0 < R+r*u.re := by
  have hu : -1 ≤ u.re := by nlinarith [u.onCircle, sq_nonneg u.im, sq_nonneg (u.re+1)]
  nlinarith [mul_le_mul_of_nonneg_left hu hr.le]

theorem horizontal_radius (R r : ℝ) (p : CirclePoint × CirclePoint) :
    (embed R r p).1^2 + (embed R r p).2.1^2 = (R+r*p.1.re)^2 := by
  change ((R+r*p.1.re)*p.2.re)^2 + ((R+r*p.1.re)*p.2.im)^2 = _
  calc
    _ = (R+r*p.1.re)^2 * (p.2.re^2+p.2.im^2) := by ring
    _ = _ := by rw [p.2.onCircle]; ring

theorem embed_injective (R r : ℝ) (hr : 0 < r) (hR : r < R) :
    Function.Injective (embed R r) := by
  rintro ⟨u,v⟩ ⟨u',v'⟩ he
  have hx := congrArg Prod.fst he
  have hy := congrArg (fun p : ℝ × ℝ × ℝ => p.2.1) he
  have hz := congrArg (fun p : ℝ × ℝ × ℝ => p.2.2) he
  have hh := horizontal_radius R r (u,v)
  have hh' := horizontal_radius R r (u',v')
  rw [he] at hh
  have hp := radial_positive R r hr hR u
  have hp' := radial_positive R r hr hR u'
  have hs : R+r*u.re = R+r*u'.re := by nlinarith
  have huRe : u.re = u'.re := by nlinarith
  have huIm : u.im = u'.im := by dsimp [embed] at hz; nlinarith
  have hvRe : v.re = v'.re := by dsimp [embed] at hx; rw [← hs] at hx; nlinarith
  have hvIm : v.im = v'.im := by dsimp [embed] at hy; rw [← hs] at hy; nlinarith
  have hu : u = u' := CirclePoint.ext huRe huIm
  have hv : v = v' := CirclePoint.ext hvRe hvIm
  exact Prod.ext hu hv

/-- ME-084: center at B888=(8,8,8), minor radius 8 and major radius 8φ.
φ>1 is the nondegenerate domain. Translation is explicit. -/
def base888 (phi : ℝ) (p : CirclePoint × CirclePoint) : ℝ × ℝ × ℝ :=
  let q := embed (8*phi) 8 p
  (8+q.1, 8+q.2.1, 8+q.2.2)

theorem base888_injective (phi : ℝ) (hphi : 1 < phi) :
    Function.Injective (base888 phi) := by
  intro p q he
  apply embed_injective (8*phi) 8 (by norm_num) (by linarith)
  apply Prod.ext
  · have := congrArg Prod.fst he
    dsimp [base888] at this
    linarith
  · apply Prod.ext
    · have := congrArg (fun p : ℝ × ℝ × ℝ => p.2.1) he
      dsimp [base888] at this
      linarith
    · have := congrArg (fun p : ℝ × ℝ × ℝ => p.2.2) he
      dsimp [base888] at this
      linarith
end Toroidal

namespace SignChecks
/-- ME-054 in the same (+---), c=1 convention as ME-004. -/
def projectedForce (beta : ℝ) (u p : Fin 4 → ℝ) (mu : Fin 4) : ℝ :=
  beta * ∑ nu : Fin 4, (FlatScalar.minkowskiInverseMetric 1 mu nu + u mu*u nu)*p nu

def restTime : Fin 4 → ℝ := Pi.single 0 1

/-- For a unit timelike rest vector and a time-directed scalar gradient,
the displayed plus-sign projector produces a nonzero temporal force.
It is therefore not the (+---) orthogonal projection. -/
theorem plus_projector_not_orthogonal :
    projectedForce 1 restTime restTime 0 = 2 := by
  norm_num [projectedForce, restTime, FlatScalar.minkowskiInverseMetric,
    Fin.sum_univ_succ, Pi.single_apply]
end SignChecks

namespace Reaction
/-- ME-024 with constant gap magnitudes and forcing (deterministic sector). -/
def drift (a b k eta gapSquared rateGapSquared forcing : ℝ) (phi : ℝ) : ℝ :=
  b*phi-a*phi^3-k*phi*gapSquared-eta*phi*rateGapSquared+forcing

def potential (a b k eta gapSquared rateGapSquared forcing : ℝ) (phi : ℝ) : ℝ :=
  a/4*phi^4-(b-k*gapSquared-eta*rateGapSquared)/2*phi^2-forcing*phi

theorem potential_hasDerivAt (a b k eta q v f x : ℝ) :
    HasDerivAt (potential a b k eta q v f) (-drift a b k eta q v f x) x := by
  convert ((((hasDerivAt_id x).pow 4).const_mul (a/4)).sub
    (((hasDerivAt_id x).pow 2).const_mul ((b-k*q-eta*v)/2))).sub
    ((hasDerivAt_id x).const_mul f) using 1 <;> simp only [potential, drift, id_eq] <;> ring

theorem energy_dissipates (a b k eta q v f tau : ℝ) (htau : 0 < tau)
    (phi : ℝ → ℝ) (t : ℝ)
    (hphi : HasDerivAt phi (drift a b k eta q v f (phi t) / tau) t) :
    HasDerivAt (fun s => potential a b k eta q v f (phi s))
      (-(drift a b k eta q v f (phi t))^2 / tau) t ∧
    -(drift a b k eta q v f (phi t))^2 / tau ≤ 0 := by
  constructor
  · convert (potential_hasDerivAt a b k eta q v f (phi t)).comp t hphi using 1 <;> ring
  · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) htau.le

/-- Homogeneous uncoupled ME-036/037 preserves the catalogue's cubic sign. -/
def homogeneous (x : ℝ) := -(x-x^3)
theorem reaction_grows_above_one (x : ℝ) (hx : 1 < x) : 0 < homogeneous x := by
  have h := mul_pos (show 0 < x by linarith) (show 0 < x^2-1 by nlinarith)
  unfold homogeneous
  nlinarith

theorem homogeneous_fixed_points (x : ℝ) :
    homogeneous x = 0 ↔ x = 0 ∨ x = 1 ∨ x = -1 := by
  have he : homogeneous x = x*(x-1)*(x+1) := by unfold homogeneous; ring
  rw [he, mul_eq_zero, mul_eq_zero]
  constructor <;> intro h
  · rcases h with (h|h)|h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (by linarith))
  · rcases h with h|h|h <;> simp [h]
end Reaction

namespace Electromagnetism
/-- ME-012, Cartesian c=1 coordinates with signature (+---).
The six independent components determine an antisymmetric field tensor. -/
def fieldTensor (electric magnetic : Fin 3 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![0, electric 0, electric 1, electric 2],
    ![-electric 0, 0, magnetic 2, -magnetic 1],
    ![-electric 1, -magnetic 2, 0, magnetic 0],
    ![-electric 2, magnetic 1, -magnetic 0, 0]]

def sign (i : Fin 4) : ℝ := if i = 0 then 1 else -1

def lagrangian (electric magnetic : Fin 3 → ℝ) : ℝ :=
  -(1/4 : ℝ) * ∑ i : Fin 4, ∑ j : Fin 4,
    fieldTensor electric magnetic i j *
      (sign i * sign j * fieldTensor electric magnetic i j)

theorem tensor_antisymmetric (E B : Fin 3 → ℝ) (i j : Fin 4) :
    fieldTensor E B i j = -fieldTensor E B j i := by
  fin_cases i <;> fin_cases j <;> simp [fieldTensor]

theorem lagrangian_eq_electric_sub_magnetic (E B : Fin 3 → ℝ) :
    lagrangian E B = ((∑ i : Fin 3, (E i)^2) - ∑ i : Fin 3, (B i)^2)/2 := by
  simp [lagrangian, sign, fieldTensor, Fin.sum_univ_succ]
  ring
end Electromagnetism
end MonolithicAnalysis
