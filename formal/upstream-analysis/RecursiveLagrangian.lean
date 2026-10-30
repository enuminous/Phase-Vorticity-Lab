import SpecifiedModels
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! ME-011 on a real Hilbert state space. Memory and environment are external
inputs to the position variation. The original signs are preserved. Actual
gradients and time derivatives define the Euler-Lagrange residual. -/

noncomputable section
namespace MonolithicAnalysis.RecursiveLagrangian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- R is the slice q ↦ R(q,m,e), with memory and environment held fixed. -/
def recursive (lam κ η : ℝ) (φ R : E → ℝ) (m w q v : E) : ℝ :=
  lam * (φ q * R q) - (κ / 2) * ‖q - m‖ ^ 2 - (η / 2) * ‖v - w‖ ^ 2

/-- An explicit mechanical extension, not an extra term attributed to ME-011. -/
def lagrangian (M lam κ η : ℝ) (φ R : E → ℝ) (m w q v : E) : ℝ :=
  (M / 2) * ‖v‖ ^ 2 + recursive lam κ η φ R m w q v

def couplingGradient (lam : ℝ) (φ R : E → ℝ) (q gφ gR : E) : E :=
  lam • (R q • gφ + φ q • gR)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem recursive_discrepancy (lam κ η : ℝ) (φ R : E → ℝ) (m w q v : E) :
    recursive lam κ η φ R m w q v =
      -(1 / 2 : ℝ) * Force.discrepancy q m v w κ η (2 * lam) (fun y => φ y * R y) := by
  unfold recursive Force.discrepancy
  ring

theorem recursive_position_gradient (lam κ η : ℝ) (φ R : E → ℝ) (m w q v gφ gR : E)
    (hφ : HasGradientAt φ gφ q) (hR : HasGradientAt R gR q) :
    HasGradientAt (fun y => recursive lam κ η φ R m w y v)
      (couplingGradient lam φ R q gφ gR - κ • (q - m)) q := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hn := ((hasFDerivAt_id q).sub_const m).norm_sq
  have hd := (((hφ.hasFDerivAt.mul hR.hasFDerivAt).const_mul lam).sub
    (hn.const_mul (κ / 2))).sub_const ((η / 2) * ‖v - w‖ ^ 2)
  convert hd using 1
  ext d
  simp [couplingGradient, InnerProductSpace.toDual_apply_apply]
  ring

theorem recursive_velocity_gradient (lam κ η : ℝ) (φ R : E → ℝ) (m w q v : E) :
    HasGradientAt (fun z => recursive lam κ η φ R m w q z) (-(η • (v - w))) v := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hn := ((hasFDerivAt_id v).sub_const w).norm_sq
  have hd := (hn.const_mul (η / 2)).const_sub (lam * (φ q * R q) - (κ / 2) * ‖q - m‖ ^ 2)
  convert hd using 1
  ext d
  simp [InnerProductSpace.toDual_apply_apply]
  ring

theorem position_gradient (M lam κ η : ℝ) (φ R : E → ℝ) (m w q v gφ gR : E)
    (hφ : HasGradientAt φ gφ q) (hR : HasGradientAt R gR q) :
    HasGradientAt (fun y => lagrangian M lam κ η φ R m w y v)
      (couplingGradient lam φ R q gφ gR - κ • (q - m)) q := by
  rw [hasGradientAt_iff_hasFDerivAt]
  exact (recursive_position_gradient lam κ η φ R m w q v gφ gR hφ hR).hasFDerivAt.const_add _

theorem velocity_gradient (M lam κ η : ℝ) (φ R : E → ℝ) (m w q v : E) :
    HasGradientAt (fun z => lagrangian M lam κ η φ R m w q z)
      (M • v - η • (v - w)) v := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hd := (((hasFDerivAt_id v).norm_sq).const_mul (M / 2)).add
    (recursive_velocity_gradient lam κ η φ R m w q v).hasFDerivAt
  convert hd using 1
  ext d
  simp [InnerProductSpace.toDual_apply_apply]
  ring

def momentum (M lam κ η : ℝ) (φ R : E → ℝ) (m w q v : E) : E :=
  gradient (fun z => lagrangian M lam κ η φ R m w q z) v

theorem momentum_eq (M lam κ η : ℝ) (φ R : E → ℝ) (m w q v : E) :
    momentum M lam κ η φ R m w q v = (M - η) • v + η • w := by
  rw [momentum, (velocity_gradient M lam κ η φ R m w q v).gradient]
  module

/-- The memory velocity is its actual time derivative. phi/R may depend on time. -/
def eulerLagrange (M lam κ η : ℝ) (φ R : ℝ → E → ℝ) (m q : ℝ → E) (t : ℝ) : E :=
  deriv (fun s => momentum M lam κ η (φ s) (R s) (m s) (deriv m s) (q s) (deriv q s)) t -
    gradient (fun y => lagrangian M lam κ η (φ t) (R t) (m t) (deriv m t) y (deriv q t)) (q t)

theorem momentum_hasDerivAt (M lam κ η : ℝ) (φ R : ℝ → E → ℝ) (m q : ℝ → E)
    (t : ℝ) (a b : E) (hq : HasDerivAt (deriv q) a t) (hm : HasDerivAt (deriv m) b t) :
    HasDerivAt (fun s => momentum M lam κ η (φ s) (R s) (m s) (deriv m s) (q s) (deriv q s))
      ((M - η) • a + η • b) t := by
  simpa only [momentum_eq] using (hq.const_smul (M - η)).add (hm.const_smul η)

theorem euler_lagrange_eq (M lam κ η : ℝ) (φ R : ℝ → E → ℝ) (m q : ℝ → E)
    (t : ℝ) (a b gφ gR : E)
    (hq : HasDerivAt (deriv q) a t) (hm : HasDerivAt (deriv m) b t)
    (hφ : HasGradientAt (φ t) gφ (q t)) (hR : HasGradientAt (R t) gR (q t)) :
    eulerLagrange M lam κ η φ R m q t =
      (M - η) • a + η • b - couplingGradient lam (φ t) (R t) (q t) gφ gR + κ • (q t - m t) := by
  rw [eulerLagrange, (momentum_hasDerivAt M lam κ η φ R m q t a b hq hm).deriv,
    (position_gradient M lam κ η (φ t) (R t) (m t) (deriv m t) (q t) (deriv q t)
      gφ gR hφ hR).gradient]
  module

theorem euler_lagrange_iff (M lam κ η : ℝ) (φ R : ℝ → E → ℝ) (m q : ℝ → E)
    (t : ℝ) (a b gφ gR : E)
    (hq : HasDerivAt (deriv q) a t) (hm : HasDerivAt (deriv m) b t)
    (hφ : HasGradientAt (φ t) gφ (q t)) (hR : HasGradientAt (R t) gR (q t)) :
    eulerLagrange M lam κ η φ R m q t = 0 ↔
      (M - η) • a = couplingGradient lam (φ t) (R t) (q t) gφ gR - κ • (q t - m t) - η • b := by
  rw [euler_lagrange_eq M lam κ η φ R m q t a b gφ gR hq hm hφ hR]
  constructor
  · intro h
    rw [← sub_eq_zero]
    convert h using 1
    abel
  · intro h
    rw [h]
    abel

theorem acceleration_eq (M lam κ η : ℝ) (hM : M - η ≠ 0)
    (φ R : ℝ → E → ℝ) (m q : ℝ → E) (t : ℝ) (a b gφ gR : E)
    (hq : HasDerivAt (deriv q) a t) (hm : HasDerivAt (deriv m) b t)
    (hφ : HasGradientAt (φ t) gφ (q t)) (hR : HasGradientAt (R t) gR (q t))
    (hEL : eulerLagrange M lam κ η φ R m q t = 0) :
    a = (M - η)⁻¹ • (couplingGradient lam (φ t) (R t) (q t) gφ gR - κ • (q t - m t) - η • b) := by
  have h := (euler_lagrange_iff M lam κ η φ R m q t a b gφ gR hq hm hφ hR).mp hEL
  rw [← h, smul_smul, inv_mul_cancel₀ hM, one_smul]

/-- Actual derivative of the simultaneous position/velocity perturbation at zero. -/
theorem first_variation (M lam κ η : ℝ) (φ R : E → ℝ) (m w q v dq dv gφ gR : E)
    (hφ : HasGradientAt φ gφ q) (hR : HasGradientAt R gR q) :
    HasDerivAt (fun ε : ℝ => lagrangian M lam κ η φ R m w (q + ε • dq) (v + ε • dv))
      (inner ℝ (couplingGradient lam φ R q gφ gR - κ • (q - m)) dq +
        inner ℝ (M • v - η • (v - w)) dv) 0 := by
  have hq : HasDerivAt (fun ε : ℝ => q + ε • dq) dq 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const dq).const_add q
  have hv : HasDerivAt (fun ε : ℝ => v + ε • dv) dv 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const dv).const_add v
  have hp : HasDerivAt (fun ε : ℝ => φ (q + ε • dq)) (inner ℝ gφ dq) 0 := by
    simpa [InnerProductSpace.toDual_apply_apply] using hφ.hasFDerivAt.comp_hasDerivAt_of_eq 0 hq (by simp)
  have hr : HasDerivAt (fun ε : ℝ => R (q + ε • dq)) (inner ℝ gR dq) 0 := by
    simpa [InnerProductSpace.toDual_apply_apply] using hR.hasFDerivAt.comp_hasDerivAt_of_eq 0 hq (by simp)
  have hd := (hv.norm_sq.const_mul (M / 2)).add
    ((((hp.mul hr).const_mul lam).sub ((hq.sub_const m).norm_sq.const_mul (κ / 2))).sub
      ((hv.sub_const w).norm_sq.const_mul (η / 2)))
  convert hd using 1
  simp [couplingGradient, inner_add_left, inner_sub_left, inner_smul_left]
  ring

/-- A classical path includes both actual derivatives; totalized derivatives alone do not suffice. -/
def RegularPath (q : ℝ → E) : Prop := Differentiable ℝ q ∧ Differentiable ℝ (deriv q)

def Solves (M lam κ η : ℝ) (φ R : ℝ → E → ℝ) (m q : ℝ → E) : Prop :=
  RegularPath m ∧ RegularPath q ∧
    (∀ t, DifferentiableAt ℝ (φ t) (q t) ∧ DifferentiableAt ℝ (R t) (q t)) ∧
    ∀ t, eulerLagrange M lam κ η φ R m q t = 0

def staticResidual (M lam κ η : ℝ) (φ R : E → ℝ) (m : E) (q : ℝ → E) : ℝ → E :=
  eulerLagrange M lam κ η (fun _ => φ) (fun _ => R) (fun _ => m) q

theorem static_residual_eq (M lam κ η : ℝ) (φ R : E → ℝ) (m : E) (q : ℝ → E)
    (t : ℝ) (a gφ gR : E) (hqa : HasDerivAt (deriv q) a t)
    (hφ : HasGradientAt φ gφ (q t)) (hR : HasGradientAt R gR (q t)) :
    staticResidual M lam κ η φ R m q t =
      (M - η) • a - couplingGradient lam φ R (q t) gφ gR + κ • (q t - m) := by
  have hm : HasDerivAt (deriv (fun _ : ℝ => m)) 0 t := by
    rw [deriv_const']
    exact hasDerivAt_const t 0
  simpa only [staticResidual, smul_zero, add_zero] using
    euler_lagrange_eq M lam κ η (fun _ => φ) (fun _ => R) (fun _ => m) q
      t a 0 gφ gR hqa hm hφ hR

/-- Canonical mechanical energy for static memory and time-independent phi/R. -/
def energy (M lam κ η : ℝ) (φ R : E → ℝ) (m q v : E) : ℝ :=
  ((M - η) / 2) * ‖v‖ ^ 2 + (κ / 2) * ‖q - m‖ ^ 2 - lam * (φ q * R q)

theorem energy_eq_canonical (M lam κ η : ℝ) (φ R : E → ℝ) (m q v : E) :
    energy M lam κ η φ R m q v =
      inner ℝ v (momentum M lam κ η φ R m 0 q v) - lagrangian M lam κ η φ R m 0 q v := by
  rw [momentum_eq]
  simp [energy, lagrangian, recursive, inner_smul_right]
  ring

theorem energy_hasDerivAt (M lam κ η : ℝ) (φ R : E → ℝ) (m : E) (q : ℝ → E)
    (t : ℝ) (hq : DifferentiableAt ℝ q t) (hqa : DifferentiableAt ℝ (deriv q) t)
    (hφ : DifferentiableAt ℝ φ (q t)) (hR : DifferentiableAt ℝ R (q t)) :
    HasDerivAt (fun s => energy M lam κ η φ R m (q s) (deriv q s))
      (inner ℝ (deriv q t) (staticResidual M lam κ η φ R m q t)) t := by
  have hp := hφ.hasGradientAt.hasFDerivAt.comp_hasDerivAt t hq.hasDerivAt
  have hr := hR.hasGradientAt.hasFDerivAt.comp_hasDerivAt t hq.hasDerivAt
  have hd := ((hqa.hasDerivAt.norm_sq.const_mul ((M - η) / 2)).add
    ((hq.hasDerivAt.sub_const m).norm_sq.const_mul (κ / 2))).sub ((hp.mul hr).const_mul lam)
  rw [static_residual_eq M lam κ η φ R m q t (deriv (deriv q) t)
    (gradient φ (q t)) (gradient R (q t)) hqa.hasDerivAt hφ.hasGradientAt hR.hasGradientAt]
  convert hd using 1
  simp [couplingGradient, InnerProductSpace.toDual_apply_apply, real_inner_comm,
    inner_add_right, inner_sub_right, inner_smul_right]
  ring

theorem energy_derivative (M lam κ η : ℝ) (φ R : E → ℝ) (m : E) (q : ℝ → E)
    (t : ℝ) (hq : DifferentiableAt ℝ q t) (hqa : DifferentiableAt ℝ (deriv q) t)
    (hφ : DifferentiableAt ℝ φ (q t)) (hR : DifferentiableAt ℝ R (q t)) :
    deriv (fun s => energy M lam κ η φ R m (q s) (deriv q s)) t =
      inner ℝ (deriv q t) (staticResidual M lam κ η φ R m q t) :=
  (energy_hasDerivAt M lam κ η φ R m q t hq hqa hφ hR).deriv

theorem energy_conserved (M lam κ η : ℝ) (φ R : E → ℝ) (m : E) (q : ℝ → E)
    (hs : Solves M lam κ η (fun _ => φ) (fun _ => R) (fun _ => m) q) (s t : ℝ) :
    energy M lam κ η φ R m (q s) (deriv q s) = energy M lam κ η φ R m (q t) (deriv q t) := by
  have hd (r : ℝ) := energy_hasDerivAt M lam κ η φ R m q r
    (hs.2.1.1 r) (hs.2.1.2 r) (hs.2.2.1 r).1 (hs.2.2.1 r).2
  apply is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt) _ s t
  intro r
  rw [(hd r).deriv]
  change inner ℝ (deriv q r) (eulerLagrange M lam κ η (fun _ => φ) (fun _ => R) (fun _ => m) q r) = 0
  rw [hs.2.2.2 r, inner_zero_right]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem uncoupled_energy_nonnegative (M κ η : ℝ) (hM : η ≤ M) (hκ : 0 ≤ κ)
    (φ R : E → ℝ) (m q v : E) : 0 ≤ energy M 0 κ η φ R m q v := by
  simp only [energy, zero_mul, sub_zero]
  exact add_nonneg (mul_nonneg (div_nonneg (sub_nonneg.mpr hM) (by norm_num)) (sq_nonneg _))
    (mul_nonneg (div_nonneg hκ (by norm_num)) (sq_nonneg _))

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem uncoupled_energy_zero_iff (M κ η : ℝ) (hM : η < M) (hκ : 0 < κ)
    (φ R : E → ℝ) (m q v : E) :
    energy M 0 κ η φ R m q v = 0 ↔ v = 0 ∧ q = m := by
  have hμ : 0 < M - η := sub_pos.mpr hM
  have hv : 0 ≤ ((M - η) / 2) * ‖v‖ ^ 2 := by positivity
  have hq : 0 ≤ (κ / 2) * ‖q - m‖ ^ 2 := by positivity
  simp only [energy, zero_mul, sub_zero]
  constructor
  · intro h
    have hvs : ‖v‖ ^ 2 = 0 := by nlinarith
    have hqs : ‖q - m‖ ^ 2 = 0 := by nlinarith
    exact ⟨norm_eq_zero.mp (sq_eq_zero_iff.mp hvs),
      sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hqs))⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- A distinct Rayleigh dissipation function; it is not the source Lagrangian. -/
def rayleigh (γ : ℝ) (w v : E) : ℝ := (γ / 2) * ‖v - w‖ ^ 2

theorem rayleigh_gradient (γ : ℝ) (w v : E) :
    HasGradientAt (rayleigh γ w) (γ • (v - w)) v := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hd := (((hasFDerivAt_id v).sub_const w).norm_sq).const_mul (γ / 2)
  convert hd using 1
  ext d
  simp [InnerProductSpace.toDual_apply_apply]
  ring

theorem rayleigh_force (γ : ℝ) (w v : E) :
    -gradient (rayleigh γ w) v = -(γ • (v - w)) := by
  rw [(rayleigh_gradient γ w v).gradient]

theorem damped_energy_derivative (M lam κ η γ : ℝ) (φ R : E → ℝ)
    (m : E) (q : ℝ → E) (t : ℝ)
    (hq : DifferentiableAt ℝ q t) (hqa : DifferentiableAt ℝ (deriv q) t)
    (hφ : DifferentiableAt ℝ φ (q t)) (hR : DifferentiableAt ℝ R (q t))
    (hdamped : staticResidual M lam κ η φ R m q t + γ • deriv q t = 0) :
    deriv (fun s => energy M lam κ η φ R m (q s) (deriv q s)) t = -γ * ‖deriv q t‖ ^ 2 := by
  rw [energy_derivative M lam κ η φ R m q t hq hqa hφ hR,
    eq_neg_of_add_eq_zero_left hdamped]
  simp [inner_smul_right]

theorem damped_energy_antitone (M lam κ η γ : ℝ) (hγ : 0 ≤ γ)
    (φ R : E → ℝ) (m : E) (q : ℝ → E)
    (hq : RegularPath q) (hφ : ∀ t, DifferentiableAt ℝ φ (q t))
    (hR : ∀ t, DifferentiableAt ℝ R (q t))
    (hdamped : ∀ t, staticResidual M lam κ η φ R m q t + γ • deriv q t = 0) :
    Antitone (fun s => energy M lam κ η φ R m (q s) (deriv q s)) := by
  apply antitone_of_deriv_nonpos
  · intro t
    exact (energy_hasDerivAt M lam κ η φ R m q t (hq.1 t) (hq.2 t) (hφ t) (hR t)).differentiableAt
  · intro t
    rw [damped_energy_derivative M lam κ η γ φ R m q t (hq.1 t) (hq.2 t) (hφ t) (hR t) (hdamped t)]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ) (sq_nonneg _)

theorem varying_coherence_counterexample :
    gradient (fun y : ℝ => recursive 1 0 0 id (fun _ => 1) 0 0 y 0) 0 = 1 := by
  rw [(recursive_position_gradient 1 0 0 id (fun _ => 1) 0 0 0 0 1 0
    (hasDerivAt_id 0).hasGradientAt' (hasGradientAt_const _ _)).gradient]
  norm_num [couplingGradient]

/-- With M=0, the original negative velocity-gap term admits constant-velocity free motion. -/
theorem velocity_gap_is_not_drag (t : ℝ) :
    staticResidual 0 0 0 1 (fun _ : ℝ => 0) (fun _ => 0) 0 id t = 0 ∧
      -gradient (rayleigh 1 (0 : ℝ)) (deriv id t) = -1 := by
  have hqa : HasDerivAt (deriv (id : ℝ → ℝ)) 0 t := by
    rw [deriv_id']
    exact hasDerivAt_const t 1
  constructor
  · rw [static_residual_eq 0 0 0 1 (fun _ => 0) (fun _ => 0) 0 id t 0 0 0 hqa
      (hasGradientAt_const _ _) (hasGradientAt_const _ _)]
    simp [couplingGradient]
  · rw [rayleigh_force]
    simp

theorem negative_kinetic_energy_counterexample :
    energy 0 0 0 1 (fun _ : ℝ => 0) (fun _ => 0) 0 0 1 = -(1 / 2 : ℝ) := by
  norm_num [energy]

theorem accelerating_memory_counterexample (t : ℝ) :
    eulerLagrange 0 0 0 1 (fun _ _ : ℝ => 0) (fun _ _ => 0)
      (fun s => s ^ 2) (fun _ => 0) t = 2 := by
  have hq : HasDerivAt (deriv (fun _ : ℝ => (0 : ℝ))) 0 t := by
    rw [deriv_const']
    exact hasDerivAt_const t 0
  have hm : HasDerivAt (deriv (fun s : ℝ => s ^ 2)) 2 t := by
    have heq : deriv (fun s : ℝ => s ^ 2) = fun s => 2 * s := by
      funext s
      simp
    rw [heq]
    simpa using (hasDerivAt_id t).const_mul 2
  rw [euler_lagrange_eq 0 0 0 1 (fun _ _ => 0) (fun _ _ => 0)
    (fun s => s ^ 2) (fun _ => 0) t 0 2 0 0 hq hm
    (hasGradientAt_const _ _) (hasGradientAt_const _ _)]
  norm_num [couplingGradient]

/-- An explicitly time-dependent potential can change canonical energy on an EL solution. -/
theorem time_dependent_energy_counterexample (t : ℝ) :
    eulerLagrange 1 1 0 0 (fun s _ : ℝ => s) (fun _ _ => 1)
      (fun _ => 0) (fun _ => 0) t = 0 ∧
      deriv (fun s => energy 1 1 0 0 (fun _ : ℝ => s) (fun _ => 1) 0 0 0) t = -1 := by
  constructor
  · simp [eulerLagrange, momentum_eq, lagrangian, recursive, gradient_fun_const]
  · simp [energy]

/-- At M=eta, zero coupling and zero stiffness leave no acceleration equation. -/
theorem degenerate_residual (η : ℝ) (q : ℝ → E) (t : ℝ) :
    staticResidual η 0 0 η (fun _ => 0) (fun _ => 0) 0 q t = 0 := by
  simp [staticResidual, eulerLagrange, momentum_eq, lagrangian, recursive, gradient_fun_const]

theorem degenerate_classical_solution (η : ℝ) (q : ℝ → E) (hq : RegularPath q) :
    Solves η 0 0 η (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) q := by
  refine ⟨⟨differentiable_const _, ?_⟩, hq, ?_, degenerate_residual η q⟩
  · rw [deriv_const']
    exact differentiable_const _
  · intro t
    exact ⟨differentiableAt_const _, differentiableAt_const _⟩

/-- Two classical solutions share position and velocity at zero but differ at time one. -/
theorem degenerate_nonuniqueness (η : ℝ) :
    ∃ q₁ q₂ : ℝ → ℝ,
      Solves η 0 0 η (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) q₁ ∧
      Solves η 0 0 η (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) q₂ ∧
      q₁ 0 = q₂ 0 ∧ deriv q₁ 0 = deriv q₂ 0 ∧ q₁ 1 ≠ q₂ 1 := by
  have hsq : deriv (fun t : ℝ => t ^ 2) = fun t => 2 * t := by
    funext t
    simp
  have hzero : RegularPath (fun _ : ℝ => (0 : ℝ)) := by
    constructor
    · exact differentiable_const _
    · rw [deriv_const']
      exact differentiable_const _
  have hreg : RegularPath (fun t : ℝ => t ^ 2) := by
    constructor
    · fun_prop
    · rw [hsq]
      fun_prop
  refine ⟨fun _ => 0, fun t => t ^ 2, degenerate_classical_solution η _ hzero,
    degenerate_classical_solution η _ hreg, ?_⟩
  simp

end MonolithicAnalysis.RecursiveLagrangian
