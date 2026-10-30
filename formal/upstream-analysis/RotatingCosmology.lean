import RotationKinematics

/-!
# ME-056: the positive-scale Friedmann constraint and its exact consequences

This file reuses Cosmology.rateSquared without changing the canonical formula.
It supplies an explicit positive-scale domain, branch and identifiability
theorems, a stated angular-velocity normalization linking ME-055 to ME-056,
and actual differentiable solutions of the stipulated scalar equation.
No rotating spacetime metric, Einstein-equation derivation, or observation is
encoded as a conclusion. The scalar/vector normalization is an authored choice.
-/

noncomputable section
open scoped BigOperators
open MonolithicAnalysis.Vorticity
open MonolithicAnalysis.Cosmology

namespace MonolithicAnalysis.RotatingCosmology

/-- A physically admissible scale domain, plus the retained ME-056 equality. -/
def Constraint (G ρ Λ k a ω H : ℝ) : Prop :=
  0 < a ∧ H^2 = rateSquared G ρ Λ k a ω

theorem zero_scale_excluded (G ρ Λ k ω H : ℝ) :
    ¬ Constraint G ρ Λ k 0 ω H := by
  simp [Constraint]

theorem constraint_rate_nonnegative {G ρ Λ k a ω H : ℝ}
    (h : Constraint G ρ Λ k a ω H) : 0 ≤ rateSquared G ρ Λ k a ω := by
  rw [← h.2]
  exact sq_nonneg H

theorem constraint_branches (G ρ Λ k a ω H : ℝ) :
    Constraint G ρ Λ k a ω H ↔
      0 < a ∧ 0 ≤ rateSquared G ρ Λ k a ω ∧
        (H = Real.sqrt (rateSquared G ρ Λ k a ω) ∨
         H = -Real.sqrt (rateSquared G ρ Λ k a ω)) := by
  constructor
  · intro h
    have hr := constraint_rate_nonnegative h
    refine ⟨h.1, hr, ?_⟩
    apply (sq_eq_sq_iff_eq_or_eq_neg).mp
    rw [Real.sq_sqrt hr]
    exact h.2
  · rintro ⟨ha, hr, hH | hH⟩
    · exact ⟨ha, by rw [hH, Real.sq_sqrt hr]⟩
    · exact ⟨ha, by rw [hH, neg_sq, Real.sq_sqrt hr]⟩

theorem admissible_rate_exists_iff (G ρ Λ k a ω : ℝ) :
    (∃ H, Constraint G ρ Λ k a ω H) ↔
      0 < a ∧ 0 ≤ rateSquared G ρ Λ k a ω := by
  constructor
  · rintro ⟨H,h⟩
    exact ⟨h.1, constraint_rate_nonnegative h⟩
  · rintro ⟨ha,hr⟩
    exact ⟨Real.sqrt _,ha,Real.sq_sqrt hr⟩

theorem rate_rotation_sign (G ρ Λ k a ω : ℝ) :
    rateSquared G ρ Λ k a (-ω) = rateSquared G ρ Λ k a ω := by
  simp [rateSquared]

theorem constraint_rotation_sign (G ρ Λ k a ω H : ℝ) :
    Constraint G ρ Λ k a (-ω) H ↔ Constraint G ρ Λ k a ω H := by
  simp [Constraint, rate_rotation_sign]

theorem constraint_rate_sign (G ρ Λ k a ω H : ℝ) :
    Constraint G ρ Λ k a ω (-H) ↔ Constraint G ρ Λ k a ω H := by
  simp [Constraint]

/-- A squared expansion equation alone permits both signs of the Hubble rate. -/
theorem both_rate_signs :
    Constraint 0 0 0 0 1 1 1 ∧ Constraint 0 0 0 0 1 1 (-1) := by
  norm_num [Constraint, rateSquared]

theorem rotation_excess (G ρ Λ k a ω : ℝ) :
    rateSquared G ρ Λ k a ω-rateSquared G ρ Λ k a 0 = ω^2/a^2 := by
  simp [rateSquared]

theorem rotation_excess_positive_iff (G ρ Λ k a ω : ℝ) (ha : a ≠ 0) :
    0 < rateSquared G ρ Λ k a ω-rateSquared G ρ Λ k a 0 ↔ ω ≠ 0 := by
  rw [rotation_excess]
  constructor
  · intro hp hz
    subst ω
    simp at hp
  · intro hω
    exact div_pos (sq_pos_of_ne_zero hω) (sq_pos_of_ne_zero ha)

theorem effective_curvature (G ρ Λ k a ω : ℝ) :
    rateSquared G ρ Λ k a ω = rateSquared G ρ Λ (k-ω^2) a 0 := by
  simp [rateSquared, sub_div]
  ring

/-- At one nonzero scale, equal rates determine only this curvature combination. -/
theorem rate_eq_iff_effective_curvature (G ρ Λ k₁ k₂ a ω₁ ω₂ : ℝ)
    (ha : a ≠ 0) :
    rateSquared G ρ Λ k₁ a ω₁ = rateSquared G ρ Λ k₂ a ω₂ ↔
      k₁-ω₁^2 = k₂-ω₂^2 := by
  unfold rateSquared
  constructor
  · intro h
    field_simp [ha] at h
    nlinarith
  · intro h
    field_simp [ha]
    nlinarith

/-- This equality is an identifiability obstruction, not evidence of rotation. -/
theorem distinct_parameters_same_rate (G ρ Λ a : ℝ) :
    rateSquared G ρ Λ 0 a 0 = rateSquared G ρ Λ 1 a 1 := by
  simp [rateSquared]

theorem recover_rotation_square {G ρ Λ k a ω H : ℝ}
    (h : Constraint G ρ Λ k a ω H) :
    ω^2 = a^2*(H^2-rateSquared G ρ Λ k a 0) := by
  rw [h.2, rotation_excess]
  field_simp [ne_of_gt h.1]

/-- Choosing the scalar parameter as angular velocity requires a quarter of
the squared vorticity, because the ME-055 curl is twice angular velocity. -/
theorem rate_from_rigid_curl (G ρ Λ k a ω : ℝ) (ha : a ≠ 0) (x : Space) :
    rateSquared G ρ Λ k a ω = rateSquared G ρ Λ k a 0 +
      (∑ i : Fin 3, (curl (rigidRotation ω) x i)^2)/(4*a^2) := by
  rw [rigid_rotation_squared_curl]
  unfold rateSquared
  field_simp [ha]
  ring

/-- An explicitly chosen vector extension: use squared angular velocity. -/
def vectorRateSquared (G ρ Λ k a : ℝ) (w : Space) : ℝ :=
  rateSquared G ρ Λ k a 0 + RotationKinematics.squaredNorm w/a^2

theorem vector_rate_scalar_norm (G ρ Λ k a : ℝ) (w : Space) :
    vectorRateSquared G ρ Λ k a w =
      rateSquared G ρ Λ k a (Real.sqrt (RotationKinematics.squaredNorm w)) := by
  have hw : 0 ≤ RotationKinematics.squaredNorm w :=
    Finset.sum_nonneg (fun i _ => sq_nonneg (w i))
  simp [vectorRateSquared, rateSquared, Real.sq_sqrt hw]

theorem vector_rate_from_curl (G ρ Λ k a : ℝ) (ha : a ≠ 0) (w x : Space) :
    vectorRateSquared G ρ Λ k a w = rateSquared G ρ Λ k a 0 +
      RotationKinematics.squaredNorm (curl (RotationKinematics.angularField w) x)/(4*a^2) := by
  rw [RotationKinematics.angular_field_squared_curl]
  unfold vectorRateSquared
  field_simp [ha]

/-- ME-056 with H = a'/a is equivalent to this first-order squared constraint. -/
theorem velocity_constraint_iff (G ρ Λ k a ω adot : ℝ) (ha : a ≠ 0) :
    (adot/a)^2 = rateSquared G ρ Λ k a ω ↔
      adot^2 = ((8*Real.pi*G/3)*ρ+Λ/3)*a^2-k+ω^2 := by
  unfold rateSquared
  field_simp [ha]

/-- Classical scalar evolution at a time, including real differentiability and
positive scale. It is a predicate for the stipulated equation, not a GR model. -/
def EvolutionAt (G Λ k : ℝ) (ρ ω a : ℝ → ℝ) (t : ℝ) : Prop :=
  0 < a t ∧ DifferentiableAt ℝ a t ∧
    (deriv a t/a t)^2 = rateSquared G (ρ t) Λ k (a t) (ω t)

theorem evolution_iff (G Λ k : ℝ) (ρ ω a : ℝ → ℝ) (t : ℝ) :
    EvolutionAt G Λ k ρ ω a t ↔
      0 < a t ∧ DifferentiableAt ℝ a t ∧
        (deriv a t)^2 = ((8*Real.pi*G/3)*ρ t+Λ/3)*(a t)^2-k+(ω t)^2 := by
  constructor
  · rintro ⟨ha,hd,he⟩
    exact ⟨ha,hd,(velocity_constraint_iff _ _ _ _ _ _ _ (ne_of_gt ha)).mp he⟩
  · rintro ⟨ha,hd,he⟩
    exact ⟨ha,hd,(velocity_constraint_iff _ _ _ _ _ _ _ (ne_of_gt ha)).mpr he⟩

theorem evolution_rotation_sign (G Λ k : ℝ) (ρ ω a : ℝ → ℝ) (t : ℝ) :
    EvolutionAt G Λ k ρ (fun s => -ω s) a t ↔ EvolutionAt G Λ k ρ ω a t := by
  simp [EvolutionAt, rate_rotation_sign]

/-- A constant scalar rotation is exactly degenerate with constant curvature
in this scalar equation, including its differentiable scale-factor solutions. -/
theorem evolution_effective_curvature (G Λ k ω : ℝ) (ρ a : ℝ → ℝ) (t : ℝ) :
    EvolutionAt G Λ k ρ (fun _ => ω) a t ↔
      EvolutionAt G Λ (k-ω^2) ρ (fun _ => 0) a t := by
  simp only [EvolutionAt, effective_curvature G (ρ t) Λ k (a t) ω]

/-- Actual affine-scale solution in the vacuum, zero-Lambda sector. The scale
condition restricts the time domain and avoids the singular zero-scale point. -/
theorem affine_vacuum_solution (G k ω a₀ b t : ℝ)
    (ha : 0 < a₀+b*t) (hb : b^2 = ω^2-k) :
    EvolutionAt G 0 k (fun _ => 0) (fun _ => ω) (fun s => a₀+b*s) t := by
  have hd : HasDerivAt (fun s => a₀+b*s) b t := by
    simpa using ((hasDerivAt_id t).const_mul b).const_add a₀
  refine ⟨ha,hd.differentiableAt,?_⟩
  rw [hd.deriv]
  apply (velocity_constraint_iff _ _ _ _ _ _ _ (ne_of_gt ha)).mpr
  simpa [sub_eq_add_neg, add_comm] using hb

theorem expanding_vacuum_solution (G k ω a₀ t : ℝ)
    (ha₀ : 0 < a₀) (ht : 0 ≤ t) (hallowed : 0 ≤ ω^2-k) :
    EvolutionAt G 0 k (fun _ => 0) (fun _ => ω)
      (fun s => a₀+Real.sqrt (ω^2-k)*s) t := by
  apply affine_vacuum_solution
  · positivity
  · exact Real.sq_sqrt hallowed

/-- A second actual solution family. Its nonzero rotation parameter is
cancelled by k = omega^2; it is not inferred from the exponential scale. -/
theorem exponential_vacuum_solution (G H ω a₀ t : ℝ) (ha₀ : 0 < a₀) :
    EvolutionAt G (3*H^2) (ω^2) (fun _ => 0) (fun _ => ω)
      (fun s => a₀*Real.exp (H*s)) t := by
  have ha : 0 < a₀*Real.exp (H*t) := mul_pos ha₀ (Real.exp_pos _)
  have hd : HasDerivAt (fun s => a₀*Real.exp (H*s))
      (H*(a₀*Real.exp (H*t))) t := by
    convert (((hasDerivAt_id t).const_mul H).exp).const_mul a₀ using 1
    simp
    ring
  refine ⟨ha,hd.differentiableAt,?_⟩
  rw [hd.deriv]
  apply (velocity_constraint_iff _ _ _ _ _ _ _ (ne_of_gt ha)).mpr
  ring

end MonolithicAnalysis.RotatingCosmology
