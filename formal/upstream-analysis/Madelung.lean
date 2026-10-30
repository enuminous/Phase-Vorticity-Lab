import CatalogueAnalysis
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp

/-! Actual polar-wave derivatives and the flat 1+1 current/Madelung relations.
The two evolution equations below are separate assumptions; the polar identity
alone implies neither one. See SPECIFICATIONS.md for conventions and exclusions. -/

noncomputable section
open scoped ComplexConjugate
namespace MonolithicAnalysis.Madelung

def phase (θ : ℝ) : ℂ := Complex.exp (Complex.I * (θ : ℂ))

def first (r rx θ θx : ℝ) : ℂ :=
  ((rx : ℂ) + Complex.I * (r * θx : ℝ)) * phase θ

def second (r rx rxx θ θx θxx : ℝ) : ℂ :=
  ((rxx - r * θx ^ 2 : ℝ) + Complex.I * (2 * rx * θx + r * θxx : ℝ)) * phase θ

theorem phase_ne_zero (θ : ℝ) : phase θ ≠ 0 := Complex.exp_ne_zero _

theorem conj_phase_mul (θ : ℝ) : conj (phase θ) * phase θ = 1 := by
  change conj (Complex.exp _) * Complex.exp _ = 1
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp

theorem wave_hasDerivAt {r θ : ℝ → ℝ} {rx θx x : ℝ}
    (hr : HasDerivAt r rx x) (hθ : HasDerivAt θ θx x) :
    HasDerivAt (fun y => Polar.wave (r y) (θ y)) (first (r x) rx (θ x) θx) x := by
  have h := hr.ofReal_comp.mul ((hθ.ofReal_comp.const_mul Complex.I).cexp)
  convert h using 1
  simp only [first, phase, Complex.ofReal_mul]
  ring

theorem wave_second_deriv {r rx θ θx : ℝ → ℝ} {rxx θxx x : ℝ}
    (hr : ∀ y, HasDerivAt r (rx y) y) (hθ : ∀ y, HasDerivAt θ (θx y) y)
    (hrx : HasDerivAt rx rxx x) (hθx : HasDerivAt θx θxx x) :
    deriv (deriv (fun y => Polar.wave (r y) (θ y))) x =
      second (r x) (rx x) rxx (θ x) (θx x) θxx := by
  have hfirst : deriv (fun y => Polar.wave (r y) (θ y)) =
      fun y => first (r y) (rx y) (θ y) (θx y) := by
    funext y
    exact (wave_hasDerivAt (hr y) (hθ y)).deriv
  rw [hfirst]
  have h := (hrx.ofReal_comp.add
    (((hr x).mul hθx).ofReal_comp.const_mul Complex.I)).mul
      (((hθ x).ofReal_comp.const_mul Complex.I).cexp)
  calc
    _ = _ := h.deriv
    _ = _ := ?_
  simp only [second, phase, Complex.ofReal_add, Complex.ofReal_sub,
    Pi.add_apply, Pi.mul_apply, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_ofNat]
  linear_combination (r x : ℂ) * (θx x : ℂ) ^ 2 *
    Complex.exp (Complex.I * (θ x : ℂ)) * Complex.I_sq

/-- A lower-index phase-current component, without a metric sign choice. -/
def current (r θ : ℝ → ℝ) (x : ℝ) : ℝ := r x ^ 2 * deriv θ x

theorem current_eq_im_conj_wave_deriv {r θ : ℝ → ℝ} {rx θx x : ℝ}
    (hr : HasDerivAt r rx x) (hθ : HasDerivAt θ θx x) :
    (conj (Polar.wave (r x) (θ x)) *
      deriv (fun y => Polar.wave (r y) (θ y)) x).im = current r θ x := by
  rw [(wave_hasDerivAt hr hθ).deriv]
  have h : conj (Polar.wave (r x) (θ x)) * first (r x) rx (θ x) θx =
      (r x : ℂ) * ((rx : ℂ) + Complex.I * (r x * θx : ℝ)) := by
    change conj ((r x : ℂ) * phase (θ x)) *
      (((rx : ℂ) + Complex.I * (r x * θx : ℝ)) * phase (θ x)) = _
    rw [map_mul, Complex.conj_ofReal]
    calc
      _ = (r x : ℂ) * ((rx : ℂ) + Complex.I * (r x * θx : ℝ)) *
          (conj (phase (θ x)) * phase (θ x)) := by ring
      _ = _ := by rw [conj_phase_mul, mul_one]
  rw [h]
  simp [current, hθ.deriv, Complex.mul_im]
  ring

theorem current_deriv {r θ : ℝ → ℝ} {rx θxx x : ℝ}
    (hr : HasDerivAt r rx x) (hθx : HasDerivAt (deriv θ) θxx x) :
    deriv (current r θ) x = 2 * r x * rx * deriv θ x + r x ^ 2 * θxx := by
  have h := (hr.pow 2).mul hθx
  change deriv (fun y => r y ^ 2 * deriv θ y) x = _
  simpa using h.deriv

abbrev Field := ℝ → ℝ → ℝ

/-- Differentiable in time and twice differentiable in space; no mixed-partial premise. -/
structure Regular (f : Field) : Prop where
  time : ∀ x, Differentiable ℝ (fun t => f t x)
  space : ∀ t, Differentiable ℝ (f t)
  space_second : ∀ t, Differentiable ℝ (deriv (f t))

def wave (r θ : Field) (t x : ℝ) : ℂ := Polar.wave (r t x) (θ t x)

def timeD (f : Field) (t x : ℝ) : ℝ := deriv (fun s => f s x) t
def spaceD (f : Field) (t x : ℝ) : ℝ := deriv (f t) x
def spaceDD (f : Field) (t x : ℝ) : ℝ := deriv (deriv (f t)) x

theorem wave_time_deriv {r θ : Field} (hr : Regular r) (hθ : Regular θ) (t x : ℝ) :
    deriv (fun s => wave r θ s x) t =
      first (r t x) (timeD r t x) (θ t x) (timeD θ t x) :=
  (wave_hasDerivAt (hr.time x t).hasDerivAt (hθ.time x t).hasDerivAt).deriv

theorem wave_space_second {r θ : Field} (hr : Regular r) (hθ : Regular θ) (t x : ℝ) :
    deriv (deriv (wave r θ t)) x =
      second (r t x) (spaceD r t x) (spaceDD r t x)
        (θ t x) (spaceD θ t x) (spaceDD θ t x) :=
  wave_second_deriv (fun y => (hr.space t y).hasDerivAt)
    (fun y => (hθ.space t y).hasDerivAt)
    (hr.space_second t x).hasDerivAt (hθ.space_second t x).hasDerivAt

/-- ME-021 in one spatial dimension. Lean division is total; the equivalence
theorem below requires nonzero amplitude. -/
def quantumPotential (hbar m : ℝ) (r : Field) (t x : ℝ) : ℝ :=
  -(hbar ^ 2 / (2 * m)) * (spaceDD r t x / r t x)

/-- ME-020 with S = hbar * theta; both derivatives here are derivatives of S. -/
def hamiltonJacobi (hbar m : ℝ) (r θ V : Field) (t x : ℝ) : ℝ :=
  timeD (fun s y => hbar * θ s y) t x +
    spaceD (fun s y => hbar * θ s y) t x ^ 2 / (2 * m) + V t x +
    quantumPotential hbar m r t x

def probabilityDensity (r : Field) (t x : ℝ) : ℝ := r t x ^ 2

def probabilityCurrent (hbar m : ℝ) (r θ : Field) (t x : ℝ) : ℝ :=
  (hbar / m) * current (r t) (θ t) x

theorem probability_density_eq_norm_sq (r θ : Field) (t x : ℝ) :
    probabilityDensity r t x = ‖wave r θ t x‖ ^ 2 :=
  (Polar.norm_sq (r t x) (θ t x)).symm

theorem probability_current_eq_wave_current {r θ : Field}
    (hr : Regular r) (hθ : Regular θ) (hbar m t x : ℝ) :
    probabilityCurrent hbar m r θ t x =
      (hbar / m) * (conj (wave r θ t x) * deriv (wave r θ t) x).im := by
  exact congrArg (fun j => (hbar / m) * j)
    (current_eq_im_conj_wave_deriv (hr.space t x).hasDerivAt
      (hθ.space t x).hasDerivAt).symm

def continuity (hbar m : ℝ) (r θ : Field) (t x : ℝ) : ℝ :=
  timeD (probabilityDensity r) t x +
    spaceD (probabilityCurrent hbar m r θ) t x

def schrodinger (hbar m : ℝ) (ψ : ℝ → ℝ → ℂ) (V : Field) (t x : ℝ) : ℂ :=
  Complex.I * (hbar : ℂ) * deriv (fun s => ψ s x) t +
    (hbar ^ 2 / (2 * m) : ℝ) * deriv (deriv (ψ t)) x - (V t x : ℂ) * ψ t x

theorem action_derivatives {θ : Field} (hθ : Regular θ) (hbar t x : ℝ) :
    timeD (fun s y => hbar * θ s y) t x = hbar * timeD θ t x ∧
    spaceD (fun s y => hbar * θ s y) t x = hbar * spaceD θ t x := by
  exact ⟨((hθ.time x t).hasDerivAt.const_mul hbar).deriv,
    ((hθ.space t x).hasDerivAt.const_mul hbar).deriv⟩

theorem continuity_expansion {r θ : Field} (hr : Regular r) (hθ : Regular θ)
    (hbar m t x : ℝ) :
    continuity hbar m r θ t x =
      2 * r t x * timeD r t x + (hbar / m) *
        (2 * r t x * spaceD r t x * spaceD θ t x + r t x ^ 2 * spaceDD θ t x) := by
  have hd := ((hr.time x t).hasDerivAt.pow 2).deriv
  have hj := ((hr.space t x).hasDerivAt.pow 2).mul
    (hθ.space_second t x).hasDerivAt
  have hc := (hj.const_mul (hbar / m)).deriv
  simp only [Pi.pow_def, Pi.mul_apply, Pi.pow_apply] at hd hc
  unfold continuity timeD spaceD probabilityDensity probabilityCurrent current
  rw [hd, hc]
  simp only [spaceDD]
  ring

/-- The algebraic split used after the actual derivative identities. -/
theorem schrodinger_jet_factorization
    (hbar m r rt rx rxx θ θt θx θxx V : ℝ) :
    Complex.I * (hbar : ℂ) * first r rt θ θt +
        (hbar ^ 2 / (2 * m) : ℝ) * second r rx rxx θ θx θxx -
        (V : ℂ) * Polar.wave r θ =
      ((-hbar * r * θt + hbar ^ 2 / (2 * m) * (rxx - r * θx ^ 2) - V * r : ℝ) +
        Complex.I * (hbar * rt + hbar ^ 2 / (2 * m) * (2 * rx * θx + r * θxx) : ℝ)) *
        phase θ := by
  simp only [first, second, Polar.wave, phase, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_ofNat]
  linear_combination (hbar : ℂ) * (r : ℂ) * (θt : ℂ) *
    Complex.exp (Complex.I * (θ : ℂ)) * Complex.I_sq

theorem schrodinger_factorization {r θ V : Field} (hr : Regular r) (hθ : Regular θ)
    (hbar m t x : ℝ) (hm : m ≠ 0) (hr0 : r t x ≠ 0) :
    schrodinger hbar m (wave r θ) V t x =
      ((-(r t x) * hamiltonJacobi hbar m r θ V t x : ℝ) +
        Complex.I * (hbar / (2 * r t x) * continuity hbar m r θ t x : ℝ)) *
        phase (θ t x) := by
  unfold schrodinger
  rw [wave_time_deriv hr hθ, wave_space_second hr hθ]
  change Complex.I * (hbar : ℂ) * _ + _ * _ - _ * Polar.wave _ _ = _
  rw [schrodinger_jet_factorization]
  congr 2
  · rw [hamiltonJacobi, (action_derivatives hθ hbar t x).1,
      (action_derivatives hθ hbar t x).2]
    unfold quantumPotential
    field_simp [hm, hr0]
    ring
  · rw [continuity_expansion hr hθ]
    field_simp [hm, hr0]

theorem phase_factor_eq_zero (a b θ : ℝ) :
    ((a : ℂ) + Complex.I * (b : ℂ)) * phase θ = 0 ↔ a = 0 ∧ b = 0 := by
  rw [mul_eq_zero, or_iff_left (phase_ne_zero θ)]
  simp [Complex.ext_iff]

/-- Pointwise equivalence; it does not assume either real equation in the forward direction. -/
theorem schrodinger_iff_madelung {r θ V : Field} (hr : Regular r) (hθ : Regular θ)
    (hbar m t x : ℝ) (hhbar : hbar ≠ 0) (hm : m ≠ 0) (hr0 : r t x ≠ 0) :
    schrodinger hbar m (wave r θ) V t x = 0 ↔
      hamiltonJacobi hbar m r θ V t x = 0 ∧ continuity hbar m r θ t x = 0 := by
  rw [schrodinger_factorization hr hθ hbar m t x hm hr0, phase_factor_eq_zero]
  simp [mul_eq_zero, hhbar, hr0]

theorem schrodinger_solution_iff_madelung {r θ V : Field}
    (hr : Regular r) (hθ : Regular θ) (hbar m : ℝ)
    (hhbar : hbar ≠ 0) (hm : m ≠ 0) (hr0 : ∀ t x, r t x ≠ 0) :
    (∀ t x, schrodinger hbar m (wave r θ) V t x = 0) ↔
      (∀ t x, hamiltonJacobi hbar m r θ V t x = 0) ∧
      (∀ t x, continuity hbar m r θ t x = 0) := by
  simp only [schrodinger_iff_madelung hr hθ hbar m _ _ hhbar hm (hr0 _ _),
    forall_and]

/-- The contravariant time component in Cartesian signature (+−), c = 1. -/
def relativisticCharge (r θ : Field) (t x : ℝ) : ℝ :=
  current (fun s => r s x) (fun s => θ s x) t

/-- Raising the spatial index in (+−) introduces a minus sign. -/
def relativisticFlux (r θ : Field) (t x : ℝ) : ℝ := -current (r t) (θ t) x

theorem relativistic_current_components {r θ : Field}
    (hr : Regular r) (hθ : Regular θ) (t x : ℝ) :
    relativisticCharge r θ t x =
      (conj (wave r θ t x) * deriv (fun s => wave r θ s x) t).im ∧
    relativisticFlux r θ t x =
      -(conj (wave r θ t x) * deriv (wave r θ t) x).im := by
  constructor
  · exact (current_eq_im_conj_wave_deriv (hr.time x t).hasDerivAt
      (hθ.time x t).hasDerivAt).symm
  · exact congrArg Neg.neg (current_eq_im_conj_wave_deriv (hr.space t x).hasDerivAt
      (hθ.space t x).hasDerivAt).symm

def relativisticDivergence (r θ : Field) (t x : ℝ) : ℝ :=
  timeD (relativisticCharge r θ) t x + spaceD (relativisticFlux r θ) t x

def kleinGordon (ψ : ℝ → ℝ → ℂ) (U : Field) (t x : ℝ) : ℂ :=
  deriv (deriv (fun s => ψ s x)) t - deriv (deriv (ψ t)) x + (U t x : ℂ) * ψ t x

theorem im_conj_wave_second (r rx rxx θ θx θxx : ℝ) :
    (conj (Polar.wave r θ) * second r rx rxx θ θx θxx).im =
      2 * r * rx * θx + r ^ 2 * θxx := by
  have h : conj (Polar.wave r θ) * second r rx rxx θ θx θxx =
      (r : ℂ) * ((rxx - r * θx ^ 2 : ℝ) +
        Complex.I * (2 * rx * θx + r * θxx : ℝ)) := by
    change conj ((r : ℂ) * phase θ) *
      (((rxx - r * θx ^ 2 : ℝ) + Complex.I * (2 * rx * θx + r * θxx : ℝ)) *
        phase θ) = _
    rw [map_mul, Complex.conj_ofReal]
    calc
      _ = (r : ℂ) * ((rxx - r * θx ^ 2 : ℝ) +
          Complex.I * (2 * rx * θx + r * θxx : ℝ)) *
          (conj (phase θ) * phase θ) := by ring
      _ = _ := by rw [conj_phase_mul, mul_one]
  rw [h]
  simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, zero_mul, mul_zero, one_mul, zero_add, add_zero]
  ring

theorem im_conj_wave_real_potential (r θ U : ℝ) :
    (conj (Polar.wave r θ) * ((U : ℂ) * Polar.wave r θ)).im = 0 := by
  have h : conj (Polar.wave r θ) * ((U : ℂ) * Polar.wave r θ) = (U * r ^ 2 : ℝ) := by
    change conj ((r : ℂ) * phase θ) * ((U : ℂ) * ((r : ℂ) * phase θ)) = _
    rw [map_mul, Complex.conj_ofReal]
    calc
      _ = (U : ℂ) * (r : ℂ) ^ 2 * (conj (phase θ) * phase θ) := by ring
      _ = _ := by rw [conj_phase_mul]; simp
  rw [h]
  rfl

/-- ME-019's flat current divergence is derived from actual second wave derivatives.
No nonzero-amplitude assumption is needed for this polynomial identity. -/
theorem relativistic_divergence_identity {r θ U : Field}
    (hr : Regular r) (hθ : Regular θ) (t x : ℝ)
    (hrt : DifferentiableAt ℝ (deriv (fun s => r s x)) t)
    (hθt : DifferentiableAt ℝ (deriv (fun s => θ s x)) t) :
    relativisticDivergence r θ t x =
      (conj (wave r θ t x) * kleinGordon (wave r θ) U t x).im := by
  have ht := wave_second_deriv (fun s => (hr.time x s).hasDerivAt)
    (fun s => (hθ.time x s).hasDerivAt) hrt.hasDerivAt hθt.hasDerivAt
  have hcharge := current_deriv (hr.time x t).hasDerivAt hθt.hasDerivAt
  have hflux := (((hr.space t x).hasDerivAt.fun_pow 2).fun_mul
    (hθ.space_second t x).hasDerivAt).neg.deriv
  change deriv (fun y => -(r t y ^ 2 * deriv (θ t) y)) x = _ at hflux
  unfold relativisticDivergence timeD spaceD relativisticCharge relativisticFlux
  rw [hcharge]
  change _ + deriv (fun y => -(r t y ^ 2 * deriv (θ t) y)) x = _
  rw [hflux]
  unfold kleinGordon
  rw [show deriv (deriv (fun s => wave r θ s x)) t = _ from ht,
    wave_space_second hr hθ, mul_add, mul_sub, Complex.add_im, Complex.sub_im]
  change _ = (conj (Polar.wave _ _) * second _ _ _ _ _ _).im -
    (conj (Polar.wave _ _) * second _ _ _ _ _ _).im +
    (conj (Polar.wave _ _) * ((_ : ℂ) * Polar.wave _ _)).im
  rw [im_conj_wave_second, im_conj_wave_second, im_conj_wave_real_potential]
  simp only [spaceD, spaceDD, Nat.cast_ofNat, Nat.reduceSub, pow_one, add_zero]
  ring

theorem kleinGordon_implies_current_conservation {r θ U : Field}
    (hr : Regular r) (hθ : Regular θ) (t x : ℝ)
    (hrt : DifferentiableAt ℝ (deriv (fun s => r s x)) t)
    (hθt : DifferentiableAt ℝ (deriv (fun s => θ s x)) t)
    (hkg : kleinGordon (wave r θ) U t x = 0) :
    relativisticDivergence r θ t x = 0 := by
  rw [relativistic_divergence_identity hr hθ t x hrt hθt, hkg]
  simp

/-- Explicit witnesses check that the regularity class contains nontrivial waves. -/
theorem constant_regular (a : ℝ) : Regular (fun _ _ => a) := by
  constructor
  · intro x
    exact differentiable_const a
  · intro t
    exact differentiable_const a
  · intro t
    simp

def planePhase (k ω : ℝ) (t x : ℝ) : ℝ := k * x - ω * t

theorem planePhase_time (k ω t x : ℝ) :
    HasDerivAt (fun s => planePhase k ω s x) (-ω) t := by
  simpa [planePhase] using
    (hasDerivAt_const t (k * x)).sub ((hasDerivAt_id t).const_mul ω)

theorem planePhase_space (k ω t x : ℝ) :
    HasDerivAt (planePhase k ω t) k x := by
  change HasDerivAt (fun y => k * y - ω * t) k x
  simpa only [mul_one] using ((hasDerivAt_id x).const_mul k).sub_const (ω * t)

theorem planePhase_regular (k ω : ℝ) : Regular (planePhase k ω) := by
  constructor
  · exact fun x t => (planePhase_time k ω t x).differentiableAt
  · exact fun t x => (planePhase_space k ω t x).differentiableAt
  · intro t
    have h : deriv (planePhase k ω t) = fun _ => k := by
      funext x
      exact (planePhase_space k ω t x).deriv
    rw [h]
    exact differentiable_const k

theorem constant_amplitude_quantumPotential (hbar m a t x : ℝ) :
    quantumPotential hbar m (fun _ _ => a) t x = 0 := by
  simp [quantumPotential, spaceDD]

/-- Standard plane-wave dispersion, with the sign conventions checked by actual derivatives. -/
theorem plane_wave_solution_iff (hbar m a k ω V₀ t x : ℝ)
    (hhbar : hbar ≠ 0) (hm : m ≠ 0) (ha : a ≠ 0) :
    schrodinger hbar m (wave (fun _ _ => a) (planePhase k ω)) (fun _ _ => V₀) t x = 0 ↔
      hbar * ω = (hbar * k) ^ 2 / (2 * m) + V₀ := by
  rw [schrodinger_iff_madelung (constant_regular a) (planePhase_regular k ω)
    hbar m t x hhbar hm ha]
  have hspace : deriv (planePhase k ω t) = fun _ => k := by
    funext y
    exact (planePhase_space k ω t y).deriv
  rw [hamiltonJacobi, (action_derivatives (planePhase_regular k ω) hbar t x).1,
    (action_derivatives (planePhase_regular k ω) hbar t x).2,
    constant_amplitude_quantumPotential,
    continuity_expansion (constant_regular a) (planePhase_regular k ω)]
  simp only [timeD, spaceD, spaceDD, (planePhase_time k ω t x).deriv,
    hspace, deriv_const, mul_zero, zero_mul, add_zero, and_true]
  constructor <;> intro h <;> linarith

/-- At an amplitude node the zero wave solves Schrödinger but need not satisfy the
divided Hamilton–Jacobi equation. The nonzero-amplitude premise is essential. -/
theorem zero_amplitude_counterexample (t x : ℝ) :
    schrodinger 1 1 (wave (fun _ _ => 0) (fun _ _ => 0)) (fun _ _ => 1) t x = 0 ∧
      hamiltonJacobi 1 1 (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 1) t x = 1 := by
  have hw : wave (fun _ _ => 0) (fun _ _ => 0) = fun _ _ => 0 := by
    funext s y
    simp [wave, Polar.wave]
  rw [hw]
  simp [schrodinger, hamiltonJacobi, quantumPotential,
    timeD, spaceD, spaceDD]

end MonolithicAnalysis.Madelung
