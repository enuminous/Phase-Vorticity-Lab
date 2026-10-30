import SpecifiedModels
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Fixed-background scalar sector of ME-009/013, with the original negative
kinetic sign and a quadratic potential. See SCALAR_ACTION.md for the frozen
scope. All spacetime and variation derivatives are actual Mathlib derivatives. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace MonolithicAnalysis.ScalarAction

abbrev Space := FlatScalar.Spacetime
abbrev Field := Space → ℝ
abbrev D := FlatScalar.partialD

def sign (i : Fin 4) : ℝ := if i = 0 then 1 else -1
def pairing (φ h : Field) (x : Space) : ℝ :=
  ∑ i : Fin 4, sign i * D i φ x * D i h x
def density (m2 : ℝ) (J φ : Field) (x : Space) : ℝ :=
  -(1 / 2 : ℝ) * pairing φ φ x - (m2 / 2) * φ x ^ 2 + J x * φ x
def variationDensity (m2 : ℝ) (J φ h : Field) (x : Space) : ℝ :=
  -pairing φ h x - m2 * φ x * h x + J x * h x
def perturb (φ h : Field) (ε : ℝ) : Field := fun x => φ x + ε * h x

/-- A genuine integral of the density difference, well defined even if the
unperturbed action on all spacetime is infinite. -/
def actionChange (m2 : ℝ) (J φ h : Field) (ε : ℝ) : ℝ :=
  ∫ x, density m2 J (perturb φ h ε) x - density m2 J φ x
def firstVariation (m2 : ℝ) (J φ h : Field) : ℝ :=
  ∫ x, variationDensity m2 J φ h x
def action (m2 : ℝ) (J φ : Field) : ℝ := ∫ x, density m2 J φ x
def residual (m2 : ℝ) (J φ : Field) (x : Space) : ℝ :=
  FlatScalar.box 1 φ x - m2 * φ x + J x

theorem partial_perturb (φ h : Field) (ε : ℝ) (i : Fin 4) (x : Space)
    (hφ : DifferentiableAt ℝ φ x) (hh : DifferentiableAt ℝ h x) :
    D i (perturb φ h ε) x = D i φ x + ε * D i h x := by
  unfold D FlatScalar.partialD perturb
  rw [fderiv_fun_add hφ (hh.const_mul ε), fderiv_const_mul hh ε]
  simp

theorem pairing_expansion (φ h : Field) (ε : ℝ) (x : Space)
    (hφ : DifferentiableAt ℝ φ x) (hh : DifferentiableAt ℝ h x) :
    pairing (perturb φ h ε) (perturb φ h ε) x =
      pairing φ φ x + 2 * ε * pairing φ h x + ε ^ 2 * pairing h h x := by
  simp only [pairing, partial_perturb φ h ε _ x hφ hh,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem density_expansion (m2 : ℝ) (J φ h : Field) (ε : ℝ) (x : Space)
    (hφ : DifferentiableAt ℝ φ x) (hh : DifferentiableAt ℝ h x) :
    density m2 J (perturb φ h ε) x - density m2 J φ x =
      ε * variationDensity m2 J φ h x + ε ^ 2 * density m2 (fun _ => 0) h x := by
  simp only [density, pairing_expansion φ h ε x hφ hh, perturb, variationDensity]
  ring

theorem partial_contDiff {φ : Field} {n : ℕ} (hφ : ContDiff ℝ (n + 1) φ)
    (i : Fin 4) : ContDiff ℝ n (D i φ) := by
  have hd : ContDiff ℝ n (fderiv ℝ φ) := hφ.fderiv_right (by norm_cast)
  exact hd.clm_apply contDiff_const

theorem partial_compact {h : Field} (hh : HasCompactSupport h) (i : Fin 4) :
    HasCompactSupport (D i h) := hh.fderiv_apply ℝ (Pi.single i 1)

theorem integrable_product {f h : Field} (hf : Continuous f) (hh : Continuous h)
    (hs : HasCompactSupport h) : Integrable (fun x => f x * h x) :=
  (hf.mul hh).integrable_of_hasCompactSupport hs.mul_left

theorem pairing_integrable {φ h : Field} (hφ : ContDiff ℝ 1 φ)
    (hh : ContDiff ℝ 1 h) (hs : HasCompactSupport h) : Integrable (pairing φ h) := by
  apply integrable_finset_sum
  intro i _
  exact integrable_product
    (continuous_const.mul (partial_contDiff hφ i).continuous)
    (partial_contDiff hh i).continuous (partial_compact hs i)

theorem variation_integrable (m2 : ℝ) {J φ h : Field} (hJ : Continuous J)
    (hφ : ContDiff ℝ 1 φ) (hh : ContDiff ℝ 1 h) (hs : HasCompactSupport h) :
    Integrable (variationDensity m2 J φ h) := by
  exact ((pairing_integrable hφ hh hs).neg.sub
    (integrable_product (continuous_const.mul hφ.continuous) hh.continuous hs)).add
    (integrable_product hJ hh.continuous hs)

theorem density_integrable (m2 : ℝ) {J φ : Field} (hJ : Continuous J)
    (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ) :
    Integrable (density m2 J φ) := by
  have hp : Integrable (fun x => φ x ^ 2) := by
    simpa only [pow_two] using integrable_product hφ.continuous hφ.continuous hs
  exact (((pairing_integrable hφ hφ hs).const_mul (-(1 / 2 : ℝ))).sub
    (hp.const_mul (m2 / 2))).add (integrable_product hJ hφ.continuous hs)

theorem change_integrable (m2 : ℝ) {J φ h : Field} (ε : ℝ) (hJ : Continuous J)
    (hφ : ContDiff ℝ 1 φ) (hh : ContDiff ℝ 1 h) (hs : HasCompactSupport h) :
    Integrable (fun x => density m2 J (perturb φ h ε) x - density m2 J φ x) := by
  have he := fun x => density_expansion m2 J φ h ε x
    (hφ.differentiable (by norm_num) x) (hh.differentiable (by norm_num) x)
  simp_rw [he]
  exact ((variation_integrable m2 hJ hφ hh hs).const_mul ε).add
    ((density_integrable m2 continuous_const hh hs).const_mul (ε ^ 2))

theorem action_change_expansion (m2 : ℝ) {J φ h : Field} (ε : ℝ) (hJ : Continuous J)
    (hφ : ContDiff ℝ 1 φ) (hh : ContDiff ℝ 1 h) (hs : HasCompactSupport h) :
    actionChange m2 J φ h ε = ε * firstVariation m2 J φ h +
      ε ^ 2 * action m2 (fun _ => 0) h := by
  unfold actionChange
  simp_rw [density_expansion m2 J φ h ε _
    (hφ.differentiable (by norm_num) _) (hh.differentiable (by norm_num) _)]
  rw [integral_add ((variation_integrable m2 hJ hφ hh hs).const_mul ε)
    ((density_integrable m2 continuous_const hh hs).const_mul (ε ^ 2)),
    integral_const_mul, integral_const_mul]
  rfl

/-- Differentiate the proved integral polynomial; no interchange of a limit
and an integral is assumed. -/
theorem action_change_hasDerivAt (m2 : ℝ) {J φ h : Field} (hJ : Continuous J)
    (hφ : ContDiff ℝ 1 φ) (hh : ContDiff ℝ 1 h) (hs : HasCompactSupport h) :
    HasDerivAt (actionChange m2 J φ h) (firstVariation m2 J φ h) 0 := by
  have he : actionChange m2 J φ h = fun ε => ε * firstVariation m2 J φ h +
      ε ^ 2 * action m2 (fun _ => 0) h := by
    funext ε
    exact action_change_expansion m2 ε hJ hφ hh hs
  rw [he]
  convert ((hasDerivAt_id (0 : ℝ)).mul_const (firstVariation m2 J φ h)).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (action m2 (fun _ => 0) h)) using 1
  norm_num

theorem box_eq_sum (φ : Field) (x : Space) :
    FlatScalar.box 1 φ x = ∑ i : Fin 4, sign i * D i (D i φ) x := by
  simp [FlatScalar.box, FlatScalar.laplacian, FlatScalar.second, sign,
    Fin.sum_univ_succ, D]
  ring

theorem residual_continuous (m2 : ℝ) {J φ : Field} (hJ : Continuous J)
    (hφ : ContDiff ℝ 2 φ) : Continuous (residual m2 J φ) := by
  have hb : Continuous (FlatScalar.box 1 φ) := by
    change Continuous (fun x => FlatScalar.box 1 φ x)
    simp_rw [box_eq_sum]
    apply continuous_finset_sum
    intro i _
    exact continuous_const.mul (partial_contDiff (partial_contDiff hφ i) i).continuous
  exact (hb.sub (continuous_const.mul hφ.continuous)).add hJ

/-- Compact support discharges all integrability/boundary obligations of the
proved Haar-measure integration-by-parts theorem. -/
theorem partial_integration_by_parts {φ h : Field} (hφ : ContDiff ℝ 2 φ)
    (hh : ContDiff ℝ 1 h) (hs : HasCompactSupport h) (i : Fin 4) :
    (∫ x, D i φ x * D i h x) = -(∫ x, D i (D i φ) x * h x) := by
  have hpi := partial_contDiff hφ i
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_product (partial_contDiff hpi i).continuous hh.continuous hs)
    (integrable_product hpi.continuous (partial_contDiff hh i).continuous (partial_compact hs i))
    (integrable_product hpi.continuous hh.continuous hs)
    (hpi.differentiable (by norm_num)) (hh.differentiable (by norm_num))

theorem pairing_integration_by_parts {φ h : Field} (hφ : ContDiff ℝ 2 φ)
    (hh : ContDiff ℝ 1 h) (hs : HasCompactSupport h) :
    (∫ x, pairing φ h x) = -(∫ x, FlatScalar.box 1 φ x * h x) := by
  have hp (i : Fin 4) : Integrable (fun x => D i φ x * D i h x) :=
    integrable_product (partial_contDiff hφ i).continuous
      (partial_contDiff hh i).continuous (partial_compact hs i)
  have hpp (i : Fin 4) : Integrable (fun x => D i (D i φ) x * h x) :=
    integrable_product (partial_contDiff (partial_contDiff hφ i) i).continuous hh.continuous hs
  calc
    (∫ x, pairing φ h x) = ∑ i : Fin 4, sign i * ∫ x, D i φ x * D i h x := by
      simp only [pairing, mul_assoc]
      rw [integral_finset_sum _ (fun i _ => (hp i).const_mul (sign i))]
      simp_rw [integral_const_mul]
    _ = -(∑ i : Fin 4, sign i * ∫ x, D i (D i φ) x * h x) := by
      simp_rw [partial_integration_by_parts hφ hh hs, mul_neg, Finset.sum_neg_distrib]
    _ = -(∫ x, FlatScalar.box 1 φ x * h x) := by
      simp_rw [box_eq_sum, Finset.sum_mul, mul_assoc]
      rw [integral_finset_sum _ (fun i _ => (hpp i).const_mul (sign i))]
      simp_rw [integral_const_mul]

theorem first_variation_eq_residual (m2 : ℝ) {J φ h : Field} (hJ : Continuous J)
    (hφ : ContDiff ℝ 2 φ) (hh : ContDiff ℝ 1 h) (hs : HasCompactSupport h) :
    firstVariation m2 J φ h = ∫ x, residual m2 J φ x * h x := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hp := pairing_integrable hφ1 hh hs
  have hm : Integrable (fun x => m2 * φ x * h x) :=
    integrable_product (continuous_const.mul hφ.continuous) hh.continuous hs
  have hj := integrable_product hJ hh.continuous hs
  have hb : Integrable (fun x => FlatScalar.box 1 φ x * h x) := by
    have hbcont : Continuous (FlatScalar.box 1 φ) := by
      have hc := residual_continuous 0 (J := fun _ => 0) continuous_const hφ
      change Continuous (fun x => residual 0 (fun _ => 0) φ x) at hc
      simpa [residual] using hc
    exact integrable_product hbcont hh.continuous hs
  simp only [firstVariation, variationDensity, residual, sub_mul, add_mul]
  have haddL := integral_add (hp.neg.sub hm) hj
  have hsubL := integral_sub hp.neg hm
  have haddR := integral_add (hb.sub hm) hj
  simp only [Pi.sub_apply, Pi.neg_apply] at haddL hsubL haddR
  rw [haddL, hsubL, integral_neg, pairing_integration_by_parts hφ hh hs,
    neg_neg, haddR, integral_sub hb hm]

/-- Stationarity concerns the actual derivative of the integrated action change.
C2 regularity of the background is imposed in the equivalence theorem below. -/
def Stationary (m2 : ℝ) (J φ : Field) : Prop :=
  ∀ h : Field, ContDiff ℝ ∞ h → HasCompactSupport h →
    HasDerivAt (actionChange m2 J φ h) 0 0

theorem stationary_iff_firstVariation_zero (m2 : ℝ) {J φ : Field}
    (hJ : Continuous J) (hφ : ContDiff ℝ 1 φ) :
    Stationary m2 J φ ↔
      ∀ h : Field, ContDiff ℝ ∞ h → HasCompactSupport h → firstVariation m2 J φ h = 0 := by
  constructor
  · intro hstat h hh hs
    exact (action_change_hasDerivAt m2 hJ hφ (hh.of_le (by simp)) hs).unique (hstat h hh hs)
  · intro hz h hh hs
    have hd := action_change_hasDerivAt m2 hJ hφ (hh.of_le (by simp)) hs
    rwa [hz h hh hs] at hd

/-- The fundamental lemma gives almost-everywhere vanishing; continuity and
positive measure of open sets upgrade it to a pointwise classical equation. -/
theorem stationary_iff_residual_zero (m2 : ℝ) {J φ : Field}
    (hJ : Continuous J) (hφ : ContDiff ℝ 2 φ) :
    Stationary m2 J φ ↔ ∀ x, residual m2 J φ x = 0 := by
  rw [stationary_iff_firstVariation_zero m2 hJ (hφ.of_le (by norm_num))]
  constructor
  · intro hz
    have hc := residual_continuous m2 hJ hφ
    have hae : ∀ᵐ x, residual m2 J φ x = 0 := by
      apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hc.locallyIntegrable
      intro h hh hs
      have he := first_variation_eq_residual m2 hJ hφ (hh.of_le (by simp)) hs
      rw [hz h hh hs] at he
      simpa only [smul_eq_mul, mul_comm] using he.symm
    have heq : residual m2 J φ = fun _ => 0 := MeasureTheory.Measure.eq_of_ae_eq hae hc continuous_const
    exact fun x => congrFun heq x
  · intro hz h hh hs
    rw [first_variation_eq_residual m2 hJ hφ (hh.of_le (by simp)) hs]
    simp [hz]

theorem absolute_action_difference (m2 : ℝ) {J φ h : Field} (ε : ℝ) (hJ : Continuous J)
    (hφ : ContDiff ℝ 1 φ) (hφs : HasCompactSupport φ)
    (hh : ContDiff ℝ 1 h) (hs : HasCompactSupport h) :
    actionChange m2 J φ h ε = action m2 J (perturb φ h ε) - action m2 J φ := by
  have hc : ContDiff ℝ 1 (perturb φ h ε) := hφ.add (contDiff_const.mul hh)
  have hcs : HasCompactSupport (perturb φ h ε) := hφs.add hs.mul_left
  exact integral_sub (density_integrable m2 hJ hc hcs) (density_integrable m2 hJ hφ hφs)

theorem absolute_action_hasDerivAt (m2 : ℝ) {J φ h : Field} (hJ : Continuous J)
    (hφ : ContDiff ℝ 1 φ) (hφs : HasCompactSupport φ)
    (hh : ContDiff ℝ 1 h) (hs : HasCompactSupport h) :
    HasDerivAt (fun ε => action m2 J (perturb φ h ε)) (firstVariation m2 J φ h) 0 := by
  have he : (fun ε => action m2 J (perturb φ h ε)) =
      fun ε => actionChange m2 J φ h ε + action m2 J φ := by
    funext ε
    rw [absolute_action_difference m2 ε hJ hφ hφs hh hs]
    ring
  rw [he]
  exact (action_change_hasDerivAt m2 hJ hφ hh hs).add_const _

/-- An arbitrary fixed background density cancels before integration, so no
finite integral of the background over all spacetime is presumed. -/
theorem fixed_background_cancels (B : Field) (m2 : ℝ) (J φ h : Field) (ε : ℝ) :
    (∫ x, (B x + density m2 J (perturb φ h ε) x) - (B x + density m2 J φ x)) =
      actionChange m2 J φ h ε := by
  unfold actionChange
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by ring

theorem contraction_eq_pairing (φ : Field) (x : Space) :
    TensorModels.contraction (FlatScalar.minkowskiInverseMetric 1) (fun i => D i φ x) =
      pairing φ φ x := by
  simp [TensorModels.contraction, FlatScalar.minkowskiInverseMetric,
    pairing, sign, Fin.sum_univ_succ]

theorem density_eq_catalogue_scalar (m2 : ℝ) (J φ : Field) (x : Space) :
    density m2 J φ x =
      TensorModels.scalarLagrangian (FlatScalar.minkowskiInverseMetric 1)
        (fun i => D i φ x) ((m2 / 2) * φ x ^ 2) + J x * φ x := by
  rw [TensorModels.scalarLagrangian, contraction_eq_pairing]
  unfold density
  ring

/-- ME-013 with a prescribed information field: scalar variation gives
box(phi)-m2*phi+lambda*I=0 in the frozen (+---) convention. -/
theorem prescribed_source_stationary_iff (m2 lam : ℝ) {I φ : Field}
    (hI : Continuous I) (hφ : ContDiff ℝ 2 φ) :
    Stationary m2 (fun x => lam * I x) φ ↔
      ∀ x, FlatScalar.box 1 φ x - m2 * φ x + lam * I x = 0 :=
  stationary_iff_residual_zero m2 (continuous_const.mul hI) hφ

/-- A field-dependent source requires the full product derivative. This is
not covered by the prescribed-source specialization above. -/
theorem dependent_source_derivative (lam : ℝ) (I : ℝ → ℝ) (u dI : ℝ)
    (hI : HasDerivAt I dI u) :
    HasDerivAt (fun q => lam * q * I q) (lam * (I u + u * dI)) u := by
  convert (((hasDerivAt_id u).mul hI).const_mul lam) using 1
  · funext q
    simp only [Pi.mul_apply, id_eq]
    ring
  · simp only [id_eq]
    ring

theorem dependent_source_counterexample :
    deriv (fun q : ℝ => q * q) 1 = 2 ∧ (fun q : ℝ => q) 1 ≠ 2 := by
  constructor
  · convert ((hasDerivAt_id (1 : ℝ)).mul (hasDerivAt_id (1 : ℝ))).deriv using 1
    norm_num
  · norm_num

/-- Match ME-002 only in its alpha=0, massless, c=1 sector and with the
required negative source in the Lagrangian. The historical sign is retained. -/
theorem massless_source_match (φ energy pressure : Field) (x : Space) :
    residual 0 (fun y => -(4 * Real.pi) * (energy y + pressure y)) φ x =
      FlatScalar.original 1 0 φ energy pressure x := by
  simp [residual, FlatScalar.original]
  ring

def timeQuadratic (a : ℝ) : Field := fun x => a * (x 0) ^ 2

theorem time_quadratic_smooth (a : ℝ) : ContDiff ℝ ∞ (timeQuadratic a) :=
  contDiff_const.mul ((contDiff_apply ℝ ℝ (0 : Fin 4)).pow 2)

theorem time_quadratic_partial (a : ℝ) (i : Fin 4) (x : Space) :
    D i (timeQuadratic a) x = if i = 0 then 2 * a * x 0 else 0 := by
  unfold D FlatScalar.partialD timeQuadratic
  rw [(((hasFDerivAt_apply 0 x).pow 2).const_mul a).fderiv]
  by_cases hi : i = 0
  · simp [hi]
    ring
  · simp [hi, eq_comm]

theorem time_quadratic_second (a : ℝ) (i : Fin 4) (x : Space) :
    D i (D i (timeQuadratic a)) x = if i = 0 then 2 * a else 0 := by
  have he : D i (timeQuadratic a) = fun y => if i = 0 then 2 * a * y 0 else 0 :=
    funext (time_quadratic_partial a i)
  rw [he]
  by_cases hi : i = 0
  · subst i
    simp only [↓reduceIte]
    unfold D FlatScalar.partialD
    rw [((hasFDerivAt_apply 0 x).const_mul (2 * a)).fderiv]
    simp
  · simp [hi, D, FlatScalar.partialD]

theorem time_quadratic_box (a : ℝ) (x : Space) :
    FlatScalar.box 1 (timeQuadratic a) x = 2 * a := by
  rw [box_eq_sum]
  simp [time_quadratic_second, sign]

/-- A real C-infinity background solves the positive-source action residual
but fails ME-002 with the same positive source. It is not claimed to have a
finite absolute action; the compact-variation theorem applies. -/
theorem positive_source_counterexample (x : Space) :
    residual 0 (fun _ => 4 * Real.pi) (timeQuadratic (-2 * Real.pi)) x = 0 ∧
    FlatScalar.original 1 0 (timeQuadratic (-2 * Real.pi)) (fun _ => 1) (fun _ => 0) x =
      -8 * Real.pi := by
  constructor
  · rw [residual, time_quadratic_box]
    ring
  · rw [FlatScalar.original, time_quadratic_box]
    ring

theorem positive_source_is_stationary :
    Stationary 0 (fun _ => 4 * Real.pi) (timeQuadratic (-2 * Real.pi)) := by
  have hc : ContDiff ℝ 2 (timeQuadratic (-2 * Real.pi)) :=
    (time_quadratic_smooth (-2 * Real.pi)).of_le (by decide)
  rw [stationary_iff_residual_zero 0 continuous_const
    hc]
  exact fun x => (positive_source_counterexample x).1

theorem positive_source_not_original_solution :
    ¬ FlatScalar.OriginalSolution 1 0 (timeQuadratic (-2 * Real.pi))
      (fun _ => 1) (fun _ => 0) := by
  intro h
  have hz := h.2.2 (0 : Space)
  rw [(positive_source_counterexample (0 : Space)).2] at hz
  exact (mul_ne_zero (by norm_num : (-8 : ℝ) ≠ 0) Real.pi_ne_zero) hz

end MonolithicAnalysis.ScalarAction
