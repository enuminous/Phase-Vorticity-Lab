import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Module

/-! Real/complex realizations of the frozen catalogue. Domains and exclusions
are explicit in COVERAGE.md. These are standard mathematical results, not
empirical evidence for the catalogue's physical interpretations. -/

noncomputable section
open scoped BigOperators
namespace MonolithicAnalysis

namespace FlatScalar
abbrev Spacetime := Fin 4 → ℝ
def partialD (i : Fin 4) (f : Spacetime → ℝ) (x : Spacetime) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)
def second (i : Fin 4) (f : Spacetime → ℝ) := partialD i (partialD i f)
def laplacian (f : Spacetime → ℝ) (x : Spacetime) : ℝ :=
  ∑ i : Fin 3, second i.succ f x
/-- ME-004: flat (+---) convention, with a nonzero speed in the solution domain. -/
def box (c : ℝ) (f : Spacetime → ℝ) (x : Spacetime) : ℝ :=
  second 0 f x / c ^ 2 - laplacian f x
/-- In physical-time Cartesian coordinates, x⁰ = t and x¹,x²,x³ are
spatial coordinates. This is the inverse metric for the frozen (+---)
convention; the covariant metric is diag(c², -1, -1, -1). -/
def minkowskiInverseMetric (c : ℝ) (μ ν : Fin 4) : ℝ :=
  if μ = ν then if μ = 0 then 1 / c ^ 2 else -1 else 0
/-- The Cartesian Christoffel symbols vanish in this flat specialization. -/
def minkowskiChristoffel (_k _μ _ν : Fin 4) : ℝ := 0
/-- The scalar Hessian component
∇_μ∇_ν f = ∂_μ(∂_ν f) - Γ^λ_μν ∂_λ f. -/
def scalarCovariantHessian (f : Spacetime → ℝ) (μ ν : Fin 4)
    (x : Spacetime) : ℝ :=
  partialD μ (partialD ν f) x -
    ∑ k : Fin 4, minkowskiChristoffel k μ ν * partialD k f x
/-- ME-003's explicit scalar metric contraction on flat Minkowski spacetime. -/
def minkowskiCovariantBox (c : ℝ) (f : Spacetime → ℝ)
    (x : Spacetime) : ℝ :=
  ∑ μ : Fin 4, ∑ ν : Fin 4,
    minkowskiInverseMetric c μ ν * scalarCovariantHessian f μ ν x
/-- Under C² regularity and nonzero speed, the flat ME-003 contraction is
exactly the existing ME-004 operator. This states no curved-spacetime result. -/
theorem minkowski_specialization_eq_box (c : ℝ) (f : Spacetime → ℝ)
    (x : Spacetime) (hc : c ≠ 0) (hf : ContDiff ℝ 2 f) :
    minkowskiCovariantBox c f x = box c f x := by
  simp [minkowskiCovariantBox, minkowskiInverseMetric, scalarCovariantHessian,
    minkowskiChristoffel, box, laplacian, second, Fin.sum_univ_succ]
  ring
/-- ME-002 specialized to the explicitly stated flat ME-004 operator. -/
def original (c α : ℝ) (f energy pressure : Spacetime → ℝ) (x : Spacetime) : ℝ :=
  box c f x - α ^ 2 / c ^ 2 * second 0 f x -
    (4 * Real.pi / c ^ 2) * (energy x + pressure x * c)
/-- ME-005, preserving the catalogue's signs. -/
def expanded (c α : ℝ) (f energy pressure : Spacetime → ℝ) (x : Spacetime) : ℝ :=
  ((1 - α ^ 2) / c ^ 2) * second 0 f x - laplacian f x -
    (4 * Real.pi / c ^ 2) * (energy x + pressure x * c)
theorem residual_eq (c α : ℝ) (f energy pressure : Spacetime → ℝ) (x : Spacetime) :
    original c α f energy pressure x = expanded c α f energy pressure x := by
  unfold original expanded box
  ring
def OriginalSolution (c α : ℝ) (f energy pressure : Spacetime → ℝ) : Prop :=
  c ≠ 0 ∧ ContDiff ℝ 2 f ∧ ∀ x, original c α f energy pressure x = 0
def ExpandedSolution (c α : ℝ) (f energy pressure : Spacetime → ℝ) : Prop :=
  c ≠ 0 ∧ ContDiff ℝ 2 f ∧ ∀ x, expanded c α f energy pressure x = 0
theorem solution_iff (c α : ℝ) (f energy pressure : Spacetime → ℝ) :
    OriginalSolution c α f energy pressure ↔ ExpandedSolution c α f energy pressure := by
  simp only [OriginalSolution, ExpandedSolution, residual_eq]
end FlatScalar

namespace Polar
/-- ME-016: a complex amplitude with real modulus parameter and phase. -/
def wave (ρ θ : ℝ) : ℂ := (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
/-- ME-017 holds even when the real amplitude parameter is negative. -/
theorem norm_sq (ρ θ : ℝ) : ‖wave ρ θ‖ ^ 2 = ρ ^ 2 := by
  simp [wave, Complex.norm_exp, Complex.mul_re, Real.norm_eq_abs, sq_abs]
end Polar

namespace Closure
/-- ME-026: inner-product closure with a strictly positive regularizer. -/
def value {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (ε : ℝ) : ℝ := inner ℝ u v / (‖u‖ * ‖v‖ + ε)
theorem abs_lt_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (ε : ℝ) (hε : 0 < ε) : |value u v ε| < 1 := by
  have hd : 0 < ‖u‖ * ‖v‖ + ε := by positivity
  rw [value, abs_div, abs_of_pos hd, div_lt_one hd]
  exact (abs_real_inner_le_norm u v).trans_lt (by linarith)
end Closure

namespace Information
/-- ME-034: finite Shannon entropy in nats; zero-mass terms are zero. -/
def entropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  - ∑ i, p i * Real.log (p i)
theorem entropy_nonneg {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (h0 : ∀ i, 0 ≤ p i) (h1 : ∀ i, p i ≤ 1) : 0 ≤ entropy p := by
  apply neg_nonneg.mpr
  exact Finset.sum_nonpos fun i _ =>
    mul_nonpos_of_nonneg_of_nonpos (h0 i) (Real.log_nonpos (h0 i) (h1 i))
theorem entropy_point_mass {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι) :
    entropy (fun i => if i = j then 1 else 0 : ι → ℝ) = 0 := by
  simp [entropy]
/-- ME-092 on finite distributions with strictly positive reference mass. -/
def kl {ι : Type*} [Fintype ι] (p q : ι → ℝ) : ℝ :=
  ∑ i, p i * Real.log (p i / q i)
theorem kl_self {ι : Type*} [Fintype ι] (p : ι → ℝ) : kl p p = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  by_cases h : p i = 0
  · simp [h]
  · simp [h]
theorem kl_nonneg {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) : 0 ≤ kl p q := by
  have hterm (i : ι) : p i - q i ≤ p i * Real.log (p i / q i) := by
    rcases (hp i).eq_or_lt with h | h
    · simp only [← h, zero_sub, zero_div, zero_mul]
      exact neg_nonpos.mpr (hq i).le
    · have hlog := Real.log_le_sub_one_of_pos (div_pos (hq i) h)
      have hm := mul_le_mul_of_nonneg_left hlog h.le
      rw [Real.log_div (ne_of_gt (hq i)) (ne_of_gt h)] at hm
      rw [Real.log_div (ne_of_gt h) (ne_of_gt (hq i))]
      have hc : p i * (q i / p i) = q i := mul_div_cancel₀ _ (ne_of_gt h)
      nlinarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  simpa [kl, Finset.sum_sub_distrib, hps, hqs] using hs
/-- ME-093 for a finite joint table. Probability normalization is a separate
domain condition; this definition itself does not assert independence. -/
def mutualInformation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι × κ → ℝ) : ℝ :=
  entropy (fun i => ∑ j, p (i, j)) + entropy (fun j => ∑ i, p (i, j)) - entropy p
theorem mutualInformation_swap {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι × κ → ℝ) :
    mutualInformation (fun z : κ × ι => p (z.2, z.1)) = mutualInformation p := by
  unfold mutualInformation entropy
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm (f := fun j i => p (i, j) * Real.log (p (i, j)))]
  ring
end Information

namespace Tiling
/-- ME-046 over a real vector space, for any chosen operator and real scale. -/
def apply {E : Type*} [AddCommGroup E] [Module ℝ E] (A : E → E) (φ : ℝ) (x : E) : E :=
  A (φ • x) + (φ - 1) • (x - A (φ • x))
theorem expansion {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : E → E) (φ : ℝ) (x : E) :
    apply A φ x = (2 - φ) • A (φ • x) + (φ - 1) • x := by
  unfold apply
  module
end Tiling

namespace Density
/-- ME-057 is a sum of four real density contributions. -/
def effective (matter field recursion rotation : ℝ) := matter + field + recursion + rotation
theorem nonneg (m f r o : ℝ) (hm : 0 ≤ m) (hf : 0 ≤ f) (hr : 0 ≤ r) (ho : 0 ≤ o) :
    0 ≤ effective m f r o := by unfold effective; positivity
end Density

namespace Born
/-- ME-060's normalization after an operator has been applied.
The zero-vector exclusion is essential. -/
def normalize {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (v : E) : E :=
  (‖v‖ : ℝ)⁻¹ • v
theorem normalized_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (hv : v ≠ 0) : ‖normalize v‖ = 1 := by
  simp [normalize, norm_smul, norm_ne_zero_iff.mpr hv]
theorem zero_normalization {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    normalize (0 : E) = 0 := by simp [normalize]
/-- ME-060's displayed adjoint denominator on a complex Hilbert space. -/
def normalizeOperator {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A : E →L[ℂ] E) (ψ : E) : E :=
  (Real.sqrt (RCLike.re (inner ℂ ψ ((A.adjoint ∘L A) ψ))))⁻¹ • A ψ
theorem operator_eq_normalize {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A : E →L[ℂ] E) (ψ : E) :
    normalizeOperator A ψ = normalize (A ψ) := by
  rw [normalizeOperator, ← A.apply_norm_eq_sqrt_inner_adjoint_right ψ]
  rfl
theorem operator_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A : E →L[ℂ] E) (ψ : E) (h : A ψ ≠ 0) :
    ‖normalizeOperator A ψ‖ = 1 := by
  rw [operator_eq_normalize]
  exact normalized_norm (A ψ) h
/-- ME-061: probabilities of a finite family of complex amplitudes. -/
def probability {ι : Type*} [Fintype ι] (a : ι → ℂ) (i : ι) : ℝ :=
  Complex.normSq (a i) / ∑ j, Complex.normSq (a j)
theorem probability_nonneg {ι : Type*} [Fintype ι] (a : ι → ℂ) (i : ι) :
    0 ≤ probability a i := by
  exact div_nonneg (Complex.normSq_nonneg _) (Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)
theorem probability_sum {ι : Type*} [Fintype ι] (a : ι → ℂ)
    (ha : ∃ i, a i ≠ 0) : ∑ i, probability a i = 1 := by
  have hsum : 0 < ∑ i, Complex.normSq (a i) := by
    obtain ⟨i, hi⟩ := ha
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, by
      exact lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm (by simpa using hi))⟩
  simp only [probability, ← Finset.sum_div]
  exact div_self (ne_of_gt hsum)
end Born

namespace Information

/-- The nonnegative scalar remainder in Gibbs' inequality. -/
def gibbsTerm (p q : ℝ) : ℝ := p * Real.log (p / q) - p + q

theorem gibbsTerm_nonneg (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hsupport : p ≠ 0 → q ≠ 0) : 0 ≤ gibbsTerm p q := by
  by_cases hp0 : p = 0
  · simpa [gibbsTerm, hp0] using hq
  · have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
    have hq' : 0 < q := lt_of_le_of_ne hq (Ne.symm (hsupport hp0))
    have hlog := Real.log_le_sub_one_of_pos (div_pos hq' hp')
    have hm := mul_le_mul_of_nonneg_left hlog hp
    rw [Real.log_div (ne_of_gt hq') hp0] at hm
    rw [gibbsTerm, Real.log_div hp0 (ne_of_gt hq')]
    have hc : p * (q / p) = q := mul_div_cancel₀ _ hp0
    nlinarith

theorem gibbsTerm_eq_zero_iff (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hsupport : p ≠ 0 → q ≠ 0) : gibbsTerm p q = 0 ↔ p = q := by
  constructor
  · intro hz
    by_cases hp0 : p = 0
    · simp [gibbsTerm, hp0] at hz
      exact hp0.trans hz.symm
    · have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
      have hq' : 0 < q := lt_of_le_of_ne hq (Ne.symm (hsupport hp0))
      by_contra hne
      have hratio : q / p ≠ 1 := by
        intro h
        have he : q = p := (div_eq_one_iff_eq hp0).mp h
        exact hne he.symm
      have hlog := Real.log_lt_sub_one_of_pos (div_pos hq' hp') hratio
      have hm := mul_lt_mul_of_pos_left hlog hp'
      rw [Real.log_div (ne_of_gt hq') hp0] at hm
      rw [gibbsTerm, Real.log_div hp0 (ne_of_gt hq')] at hz
      have hc : p * (q / p) = q := mul_div_cancel₀ _ hp0
      nlinarith
  · rintro rfl
    by_cases hp0 : p = 0 <;> simp [gibbsTerm, hp0]

theorem sum_gibbsTerm {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) :
    ∑ i, gibbsTerm (p i) (q i) = kl p q := by
  simp [gibbsTerm, kl, Finset.sum_add_distrib, Finset.sum_sub_distrib, hps, hqs]

/-- Zero reference mass is allowed exactly where the source mass is zero.
Positive source mass over zero reference mass is excluded, not assigned
the spurious finite value obtained from totalized real logarithms. -/
theorem kl_nonneg_of_support {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hsupport : ∀ i, p i ≠ 0 → q i ≠ 0)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) : 0 ≤ kl p q := by
  rw [← sum_gibbsTerm p q hps hqs]
  exact Finset.sum_nonneg fun i _ => gibbsTerm_nonneg _ _ (hp i) (hq i) (hsupport i)

theorem kl_eq_zero_iff {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hsupport : ∀ i, p i ≠ 0 → q i ≠ 0)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) :
    kl p q = 0 ↔ p = q := by
  constructor
  · intro hz
    have hs : (∑ i, gibbsTerm (p i) (q i)) = 0 := by
      rw [sum_gibbsTerm p q hps hqs, hz]
    have he := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => gibbsTerm_nonneg _ _ (hp i) (hq i) (hsupport i))).mp hs
    funext i
    exact (gibbsTerm_eq_zero_iff _ _ (hp i) (hq i) (hsupport i)).mp
      (he i (Finset.mem_univ _))
  · rintro rfl
    exact kl_self p

def marginalLeft {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι × κ → ℝ) (i : ι) : ℝ := ∑ j, p (i, j)
def marginalRight {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι × κ → ℝ) (j : κ) : ℝ := ∑ i, p (i, j)
def marginalProduct {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι × κ → ℝ) (z : ι × κ) : ℝ := marginalLeft p z.1 * marginalRight p z.2

theorem marginalProduct_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι × κ → ℝ) (hp : ∀ z, 0 ≤ p z) (z : ι × κ) :
    0 ≤ marginalProduct p z :=
  mul_nonneg (Finset.sum_nonneg fun j _ => hp (z.1, j))
    (Finset.sum_nonneg fun i _ => hp (i, z.2))

theorem marginalProduct_support {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι × κ → ℝ) (hp : ∀ z, 0 ≤ p z) (z : ι × κ) (hz : p z ≠ 0) :
    marginalProduct p z ≠ 0 := by
  have hz' : 0 < p z := lt_of_le_of_ne (hp z) (Ne.symm hz)
  have hl : p z ≤ marginalLeft p z.1 :=
    Finset.single_le_sum (fun j _ => hp (z.1, j)) (Finset.mem_univ z.2)
  have hr : p z ≤ marginalRight p z.2 :=
    Finset.single_le_sum (fun i _ => hp (i, z.2)) (Finset.mem_univ z.1)
  exact ne_of_gt (mul_pos (hz'.trans_le hl) (hz'.trans_le hr))

theorem marginalProduct_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι × κ → ℝ) (hps : ∑ z, p z = 1) :
    ∑ z, marginalProduct p z = 1 := by
  have hl : ∑ i, marginalLeft p i = 1 := by
    simpa [marginalLeft, Fintype.sum_prod_type] using hps
  have hr : ∑ j, marginalRight p j = 1 := by
    simp only [marginalRight]
    rw [Finset.sum_comm]
    simpa [Fintype.sum_prod_type] using hps
  simp only [marginalProduct, Fintype.sum_prod_type, ← Finset.mul_sum, hr, mul_one]
  exact hl

/-- Shannon's identity with zero-mass cells and zero marginals included. -/
theorem mutualInformation_eq_kl {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι × κ → ℝ) (hp : ∀ z, 0 ≤ p z) :
    mutualInformation p = kl p (marginalProduct p) := by
  have hterm (z : ι × κ) :
      p z * Real.log (p z / marginalProduct p z) =
        p z * Real.log (p z) - p z * Real.log (marginalLeft p z.1) -
          p z * Real.log (marginalRight p z.2) := by
    by_cases hz : p z = 0
    · simp [hz]
    · have hprod := marginalProduct_support p hp z hz
      have hl : marginalLeft p z.1 ≠ 0 := (mul_ne_zero_iff.mp hprod).1
      have hr : marginalRight p z.2 ≠ 0 := (mul_ne_zero_iff.mp hprod).2
      rw [Real.log_div hz hprod, marginalProduct, Real.log_mul hl hr]
      ring
  have hl :
      ∑ z : ι × κ, p z * Real.log (marginalLeft p z.1) =
        ∑ i, marginalLeft p i * Real.log (marginalLeft p i) := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.sum_mul, marginalLeft]
  have hr :
      ∑ z : ι × κ, p z * Real.log (marginalRight p z.2) =
        ∑ j, marginalRight p j * Real.log (marginalRight p j) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [← Finset.sum_mul, marginalRight]
  unfold kl
  simp_rw [hterm, Finset.sum_sub_distrib]
  rw [hl, hr]
  unfold mutualInformation entropy marginalLeft marginalRight
  ring

theorem mutualInformation_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι × κ → ℝ) (hp : ∀ z, 0 ≤ p z) (hps : ∑ z, p z = 1) :
    0 ≤ mutualInformation p := by
  rw [mutualInformation_eq_kl p hp]
  exact kl_nonneg_of_support p (marginalProduct p) hp (marginalProduct_nonneg p hp)
    (marginalProduct_support p hp) hps (marginalProduct_sum p hps)

/-- A finite joint distribution has zero mutual information exactly when
it factors into its two marginals (independence). -/
theorem mutualInformation_zero_iff_independent {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι × κ → ℝ) (hp : ∀ z, 0 ≤ p z) (hps : ∑ z, p z = 1) :
    mutualInformation p = 0 ↔ p = marginalProduct p := by
  rw [mutualInformation_eq_kl p hp]
  exact kl_eq_zero_iff p (marginalProduct p) hp (marginalProduct_nonneg p hp)
    (marginalProduct_support p hp) hps (marginalProduct_sum p hps)
end Information

namespace FiniteSelection
/-- ME-059 on a nonempty finite state space, with an explicitly positive
probability distribution. The chosen divergence and reward are input data. -/
structure Model (S : Type*) [Fintype S] where
  probability : S → ℝ
  positive : ∀ s, 0 < probability s
  normalized : ∑ s, probability s = 1
  divergence : S → ℝ
  reward : S → ℝ
  lambda : ℝ
  gamma : ℝ

def cost {S : Type*} [Fintype S] (m : Model S) (s : S) : ℝ :=
  -Real.log (m.probability s) + m.lambda * m.divergence s - m.gamma * m.reward s

def minimizers {S : Type*} [Fintype S] (m : Model S) : Set S :=
  {s | ∀ t, cost m s ≤ cost m t}

theorem minimizer_exists {S : Type*} [Fintype S] [Nonempty S] (m : Model S) :
    (minimizers m).Nonempty := by
  obtain ⟨s, _, hs⟩ := Finset.exists_min_image Finset.univ (cost m) Finset.univ_nonempty
  exact ⟨s, fun t => hs t (Finset.mem_univ _)⟩

/-- A strict gap greater than twice the uniform cost error preserves the
unique optimizer. This is a stability claim with a quantitative hypothesis. -/
theorem strict_margin_stability {S : Type*} (f g : S → ℝ) (s : S) (ε : ℝ)
    (herr : ∀ t, |g t - f t| ≤ ε)
    (hgap : ∀ t, t ≠ s → 2 * ε < f t - f s) :
    ∀ t, t ≠ s → g s < g t := by
  intro t ht
  have hs := abs_le.mp (herr s)
  have ht' := abs_le.mp (herr t)
  have hg := hgap t ht
  linarith

theorem unique_minimizer_of_margin {S : Type*} [Fintype S] (m : Model S) (s : S)
    (hmargin : ∀ t, t ≠ s → cost m s < cost m t) :
    ∀ t, t ∈ minimizers m ↔ t = s := by
  intro t
  constructor
  · intro ht
    by_contra h
    exact (not_lt_of_ge (ht s)) (hmargin t h)
  · intro ht
    subst t
    intro t
    by_cases h : t = s
    · simp [h]
    · exact (hmargin t h).le

/-- Existence alone cannot justify a unique collapse outcome. -/
theorem constant_cost_not_unique :
    ¬ ∃! s : Bool, ∀ t : Bool, (fun _ : Bool => (0 : ℝ)) s ≤ (fun _ : Bool => (0 : ℝ)) t := by
  rintro ⟨s, _, hs⟩
  have ht := hs true (fun _ => le_rfl)
  have hf := hs false (fun _ => le_rfl)
  have h : true = false := ht.trans hf.symm
  cases h

/-- A valid two-state probability model with nonnegative zero divergence and
reward already has a tie; the ambiguity is inside ME-059's modeled domain. -/
def symmetricModel : Model Bool where
  probability := fun _ => 1 / 2
  positive := by intro s; norm_num
  normalized := by norm_num [Fintype.sum_bool]
  divergence := fun _ => 0
  reward := fun _ => 0
  lambda := 0
  gamma := 0

theorem symmetricModel_all_minimizers (s : Bool) : s ∈ minimizers symmetricModel := by
  intro t
  simp [cost, symmetricModel]

theorem symmetricModel_not_unique : ¬ ∃! s : Bool, s ∈ minimizers symmetricModel := by
  rintro ⟨s, _, hs⟩
  have ht := hs true (symmetricModel_all_minimizers true)
  have hf := hs false (symmetricModel_all_minimizers false)
  have h : true = false := ht.trans hf.symm
  cases h

end FiniteSelection


namespace Lyapunov
/-- ME-033's logarithmic growth expression for one perturbation.
This definition does not assert a maximum over directions. -/
def finiteTimeRate {E : Type*} [NormedAddCommGroup E] (v : ℝ → E) (t : ℝ) : ℝ :=
  Real.log (‖v t‖ / ‖v 0‖) / t

def HasDirectionalRate {E : Type*} [NormedAddCommGroup E] (v : ℝ → E) (rate : ℝ) : Prop :=
  v 0 ≠ 0 ∧ Filter.Tendsto (finiteTimeRate v) Filter.atTop (nhds rate)

def exponentialOrbit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (rate : ℝ) (v : E) (t : ℝ) : E := Real.exp (rate * t) • v

theorem exponential_rate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (rate t : ℝ) (v : E) (hv : v ≠ 0) (ht : t ≠ 0) :
    finiteTimeRate (exponentialOrbit rate v) t = rate := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  simp [finiteTimeRate, exponentialOrbit, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), hn, ht, Real.log_exp]

theorem exponential_hasDirectionalRate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (rate : ℝ) (v : E) (hv : v ≠ 0) : HasDirectionalRate (exponentialOrbit rate v) rate := by
  refine ⟨by simpa [exponentialOrbit] using hv, ?_⟩
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  exact (exponential_rate rate t v hv (ne_of_gt ht)).symm

def diagonalFlow (a b t : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (Real.exp (a * t) * v.1, Real.exp (b * t) * v.2)

theorem diagonal_first_orbit (a b : ℝ) :
    (fun t => diagonalFlow a b t (1, 0)) = exponentialOrbit a (1, 0) := by
  funext t
  simp [diagonalFlow, exponentialOrbit, Prod.smul_mk, smul_eq_mul]

theorem diagonal_second_orbit (a b : ℝ) :
    (fun t => diagonalFlow a b t (0, 1)) = exponentialOrbit b (0, 1) := by
  funext t
  simp [diagonalFlow, exponentialOrbit, Prod.smul_mk, smul_eq_mul]

/-- One diagonal flow has unequal rates along its two coordinate directions.
The rate along an arbitrary direction cannot be called the maximum. -/
theorem directional_rate_need_not_be_maximal (a b t : ℝ) (hab : a < b) (ht : t ≠ 0) :
    finiteTimeRate (fun τ => diagonalFlow a b τ (1, 0)) t <
      finiteTimeRate (fun τ => diagonalFlow a b τ (0, 1)) t := by
  rw [diagonal_first_orbit, diagonal_second_orbit,
    exponential_rate a t (1, 0) (by simp) ht,
    exponential_rate b t (0, 1) (by simp) ht]
  exact hab
end Lyapunov

end MonolithicAnalysis
