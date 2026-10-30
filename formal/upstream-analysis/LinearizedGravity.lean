import ScalarAction
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Explicit flat linearized curvature operators for ME-014/039. Derivatives,
regularity and source constraints are mathematical; quantum/cognitive meanings
are not supplied. See LINEARIZED_GRAVITY.md for the frozen target. -/

noncomputable section
open scoped BigOperators ContDiff
namespace MonolithicAnalysis.LinearizedGravity

abbrev Index := Fin 4
abbrev Space := FlatScalar.Spacetime
abbrev Field := Space → ℝ
abbrev Tensor := Index → Index → Field
abbrev Vector := Index → Field
abbrev D := FlatScalar.partialD
abbrev sign := ScalarAction.sign

def metric (i j : Index) : ℝ := if i = j then sign i else 0
def Smooth (n : ℕ) (h : Tensor) : Prop := ∀ i j, ContDiff ℝ n (h i j)
def Symmetric (h : Tensor) : Prop := ∀ i j, h i j = h j i
def trace (h : Tensor) (x : Space) : ℝ := ∑ i, sign i * h i i x
def divergence (h : Tensor) (j : Index) (x : Space) : ℝ :=
  ∑ i, sign i * D i (h i j) x
def vectorDivergence (v : Vector) (x : Space) : ℝ := ∑ i, sign i * D i (v i) x
def wave (f : Field) (x : Space) : ℝ := ∑ i, sign i * D i (D i f) x
def traceReverse (h : Tensor) (i j : Index) (x : Space) : ℝ :=
  h i j x - (metric i j / 2) * trace h x

/-- Standard linearized Ricci operator on a symmetric perturbation. -/
def ricci (h : Tensor) (i j : Index) (x : Space) : ℝ :=
  (1 / 2 : ℝ) * (D i (divergence h j) x + D j (divergence h i) x -
    wave (h i j) x - D i (D j (trace h)) x)
def scalarCurvature (h : Tensor) : Field := trace (ricci h)
def einstein (h : Tensor) (i j : Index) (x : Space) : ℝ :=
  ricci h i j x - (metric i j / 2) * scalarCurvature h x

theorem sign_squared (i : Index) : sign i * sign i = 1 := by
  by_cases hi : i = 0 <;> simp [sign, ScalarAction.sign, hi]

theorem metric_symmetric (i j : Index) : metric i j = metric j i := by
  by_cases hij : i = j <;> simp_all [metric, eq_comm]

theorem wave_eq_box (f : Field) (x : Space) : wave f x = FlatScalar.box 1 f x :=
  (ScalarAction.box_eq_sum f x).symm

theorem partial_const (i : Index) (a : ℝ) (x : Space) : D i (fun _ => a) x = 0 := by
  simp [D, FlatScalar.partialD]

theorem partial_coordinate (i j : Index) (x : Space) :
    D i (fun y => y j) x = if j = i then 1 else 0 := by
  rw [D, FlatScalar.partialD, (hasFDerivAt_apply j x).fderiv]
  simp [Pi.single_apply, eq_comm]

theorem partial_add (i : Index) {f g : Field} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    D i (fun y => f y + g y) x = D i f x + D i g x := by
  simp [D, FlatScalar.partialD, fderiv_fun_add hf hg]

theorem partial_sub (i : Index) {f g : Field} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    D i (fun y => f y - g y) x = D i f x - D i g x := by
  simp [D, FlatScalar.partialD, fderiv_fun_sub hf hg]

theorem partial_const_mul (i : Index) {f : Field} {x : Space}
    (hf : DifferentiableAt ℝ f x) (a : ℝ) :
    D i (fun y => a * f y) x = a * D i f x := by
  simp [D, FlatScalar.partialD, fderiv_const_mul hf a]

theorem partial_mul (i : Index) {f g : Field} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    D i (fun y => f y * g y) x = f x * D i g x + g x * D i f x := by
  simp [D, FlatScalar.partialD, fderiv_fun_mul hf hg]

theorem partial_sum (i : Index) {f : Index → Field} {x : Space}
    (hf : ∀ j, DifferentiableAt ℝ (f j) x) :
    D i (fun y => ∑ j, f j y) x = ∑ j, D i (f j) x := by
  simp [D, FlatScalar.partialD, fderiv_fun_sum (fun j _ => hf j)]

theorem partial_contDiff {f : Field} {n : ℕ} (hf : ContDiff ℝ (n + 1) f)
    (i : Index) : ContDiff ℝ n (D i f) := ScalarAction.partial_contDiff hf i

theorem second_partial_eq {f : Field} (hf : ContDiff ℝ 2 f) (i j : Index) (x : Space) :
    D i (D j f) x = fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiable (by norm_num) x
  unfold D FlatScalar.partialD
  rw [fderiv_clm_apply hd (differentiableAt_const (Pi.single j 1))]
  simp

theorem mixed_partials {f : Field} (hf : ContDiff ℝ 2 f) (i j : Index) (x : Space) :
    D i (D j f) x = D j (D i f) x := by
  rw [second_partial_eq hf, second_partial_eq hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq (Pi.single i 1) (Pi.single j 1)

theorem trace_contDiff {h : Tensor} {n : ℕ} (hh : Smooth n h) : ContDiff ℝ n (trace h) :=
  ContDiff.sum (fun i _ => contDiff_const.mul (hh i i))

theorem divergence_contDiff {h : Tensor} {n : ℕ} (hh : Smooth (n + 1) h) (j : Index) :
    ContDiff ℝ n (divergence h j) :=
  ContDiff.sum (fun i _ => contDiff_const.mul (partial_contDiff (hh i j) i))

theorem wave_contDiff {f : Field} {n : ℕ} (hf : ContDiff ℝ (n + 2) f) :
    ContDiff ℝ n (wave f) :=
  ContDiff.sum (fun i _ => contDiff_const.mul (partial_contDiff (partial_contDiff hf i) i))

theorem partial_linear_combination (a : Index → ℝ) {f : Index → Field}
    (hf : ∀ j, Differentiable ℝ (f j)) (i : Index) (x : Space) :
    D i (fun y => ∑ j, a j * f j y) x = ∑ j, a j * D i (f j) x := by
  rw [partial_sum i (fun j => (hf j x).const_mul (a j))]
  simp_rw [partial_const_mul i (hf _ x)]

theorem wave_linear_combination (a : Index → ℝ) {f : Index → Field}
    (hf : ∀ j, ContDiff ℝ 2 (f j)) (x : Space) :
    wave (fun y => ∑ j, a j * f j y) x = ∑ j, a j * wave (f j) x := by
  have hd (j : Index) := (hf j).differentiable (by norm_num)
  have hp (i j : Index) := (partial_contDiff (hf j) i).differentiable (by norm_num)
  have he (i : Index) : D i (fun y => ∑ j, a j * f j y) =
      fun y => ∑ j, a j * D i (f j) y := funext (partial_linear_combination a hd i)
  simp only [wave, he, partial_linear_combination a (hp _), Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem partial_wave {f : Field} (hf : ContDiff ℝ 3 f) (i : Index) (x : Space) :
    D i (wave f) x = wave (D i f) x := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hd (j : Index) :=
    (partial_contDiff (partial_contDiff hf j) j).differentiable (by norm_num)
  rw [show wave f = fun y => ∑ j, sign j * D j (D j f) y from rfl,
    partial_linear_combination sign hd]
  unfold wave
  apply Finset.sum_congr rfl
  intro j _
  rw [mixed_partials (partial_contDiff hf j) i j]
  rw [show D i (D j f) = D j (D i f) from funext (mixed_partials hf2 i j)]

theorem ricci_contDiff {h : Tensor} {n : ℕ} (hh : Smooth (n + 2) h) :
    Smooth n (ricci h) := by
  intro i j
  exact contDiff_const.mul
    ((((partial_contDiff (divergence_contDiff hh j) i).add
      (partial_contDiff (divergence_contDiff hh i) j)).sub (wave_contDiff (hh i j))).sub
      (partial_contDiff (partial_contDiff (trace_contDiff hh) j) i))

theorem scalar_contDiff {h : Tensor} {n : ℕ} (hh : Smooth (n + 2) h) :
    ContDiff ℝ n (scalarCurvature h) := trace_contDiff (ricci_contDiff hh)

theorem einstein_contDiff {h : Tensor} {n : ℕ} (hh : Smooth (n + 2) h) :
    Smooth n (einstein h) := by
  intro i j
  exact (ricci_contDiff hh i j).sub (contDiff_const.mul (scalar_contDiff hh))

theorem ricci_symmetric {h : Tensor} (hh : Smooth 2 h) (hs : Symmetric h) :
    Symmetric (ricci h) := by
  intro i j
  funext x
  simp only [ricci, hs i j, mixed_partials (trace_contDiff hh) i j x]
  ring

theorem einstein_symmetric {h : Tensor} (hh : Smooth 2 h) (hs : Symmetric h) :
    Symmetric (einstein h) := by
  intro i j
  funext x
  rw [einstein, einstein, ricci_symmetric hh hs i j, metric_symmetric i j]

theorem trace_reverse_trace (h : Tensor) (x : Space) : trace (traceReverse h) x = -trace h x := by
  simp [trace, traceReverse, metric, sign, ScalarAction.sign, Fin.sum_univ_succ]
  ring

theorem trace_reverse_involution (h : Tensor) : traceReverse (traceReverse h) = h := by
  funext i j x
  rw [traceReverse, trace_reverse_trace, traceReverse]
  ring

theorem trace_reverse_contDiff {h : Tensor} {n : ℕ} (hh : Smooth n h) :
    Smooth n (traceReverse h) := fun i j =>
  (hh i j).sub (contDiff_const.mul (trace_contDiff hh))

theorem scalar_curvature_formula {h : Tensor} (hh : Smooth 2 h) (x : Space) :
    scalarCurvature h x = vectorDivergence (divergence h) x - wave (trace h) x := by
  have hw : wave (trace h) x = ∑ i, sign i * wave (h i i) x :=
    wave_linear_combination sign (fun i => hh i i) x
  calc
    scalarCurvature h x = vectorDivergence (divergence h) x -
        (1 / 2 : ℝ) * (∑ i, sign i * wave (h i i) x) - (1 / 2 : ℝ) * wave (trace h) x := by
      change (∑ i, sign i * ricci h i i x) =
        (∑ i, sign i * D i (divergence h i) x) -
          (1 / 2 : ℝ) * (∑ i, sign i * wave (h i i) x) -
          (1 / 2 : ℝ) * (∑ i, sign i * D i (D i (trace h)) x)
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      unfold ricci
      ring
    _ = _ := by rw [← hw]; ring

theorem partial_ricci {h : Tensor} (hh : Smooth 3 h) (k i j : Index) (x : Space) :
    D k (ricci h i j) x = (1 / 2 : ℝ) *
      (D k (D i (divergence h j)) x + D k (D j (divergence h i)) x -
        D k (wave (h i j)) x - D k (D i (D j (trace h))) x) := by
  have ha := (partial_contDiff (divergence_contDiff hh j) i).differentiable (by norm_num) x
  have hb := (partial_contDiff (divergence_contDiff hh i) j).differentiable (by norm_num) x
  have hc := (wave_contDiff (hh i j)).differentiable (by norm_num) x
  have hd := (partial_contDiff (partial_contDiff (trace_contDiff hh) j) i).differentiable (by norm_num) x
  change D k (fun y => (1 / 2 : ℝ) *
    (D i (divergence h j) y + D j (divergence h i) y - wave (h i j) y -
      D i (D j (trace h)) y)) x = _
  have hab : DifferentiableAt ℝ (fun y => D i (divergence h j) y + D j (divergence h i) y) x := by
    simpa only [Pi.add_apply] using ha.add hb
  have habc : DifferentiableAt ℝ
      (fun y => D i (divergence h j) y + D j (divergence h i) y - wave (h i j) y) x := by
    simpa only [Pi.sub_apply] using hab.sub hc
  have habcd : DifferentiableAt ℝ
      (fun y => D i (divergence h j) y + D j (divergence h i) y - wave (h i j) y -
        D i (D j (trace h)) y) x := by
    simpa only [Pi.sub_apply] using habc.sub hd
  rw [partial_const_mul k habcd,
    partial_sub k habc hd, partial_sub k hab hc,
    partial_add k ha hb]

theorem divergence_ricci {h : Tensor} (hh : Smooth 3 h) (j : Index) (x : Space) :
    divergence (ricci h) j x = (1 / 2 : ℝ) * D j (scalarCurvature h) x := by
  have hd (i : Index) := (partial_contDiff (divergence_contDiff hh i) i).differentiable (by norm_num)
  have ht : ContDiff ℝ 3 (trace h) := trace_contDiff hh
  have hdiv : (∑ i, sign i * D i (D j (divergence h i)) x) =
      D j (vectorDivergence (divergence h)) x := by
    change _ = D j (fun y => ∑ i, sign i * D i (divergence h i) y) x
    rw [partial_linear_combination sign hd]
    apply Finset.sum_congr rfl
    intro i _
    rw [mixed_partials (divergence_contDiff hh i) i j]
  have hw : (∑ i, sign i * D i (wave (h i j)) x) = wave (divergence h j) x := by
    simp_rw [partial_wave (hh _ _) _ x]
    exact (wave_linear_combination sign (fun i => partial_contDiff (hh i j) i) x).symm
  have hsc : scalarCurvature h = fun y => vectorDivergence (divergence h) y - wave (trace h) y :=
    funext (scalar_curvature_formula (fun i j => (hh i j).of_le (by norm_num)))
  have hsv : DifferentiableAt ℝ (vectorDivergence (divergence h)) x :=
    DifferentiableAt.fun_sum (fun i _ => (hd i x).const_mul (sign i))
  rw [hsc, partial_sub j hsv ((wave_contDiff ht).differentiable (by norm_num) x), partial_wave ht]
  calc
    divergence (ricci h) j x = (1 / 2 : ℝ) *
        (wave (divergence h j) x + (∑ i, sign i * D i (D j (divergence h i)) x) -
          (∑ i, sign i * D i (wave (h i j)) x) - wave (D j (trace h)) x) := by
      simp only [divergence, partial_ricci hh]
      change _ = (1 / 2 : ℝ) *
        ((∑ i, sign i * D i (D i (divergence h j)) x) + _ - _ -
          (∑ i, sign i * D i (D i (D j (trace h))) x))
      simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hdiv, hw]; ring

theorem divergence_metric_mul {f : Field} (hf : Differentiable ℝ f) (j : Index) (x : Space) :
    divergence (fun i k y => metric i k * f y) j x = D j f x := by
  simp only [divergence, partial_const_mul _ (hf x)]
  simp [metric, ← mul_assoc, sign_squared]

theorem contracted_bianchi {h : Tensor} (hh : Smooth 3 h) (j : Index) (x : Space) :
    divergence (einstein h) j x = 0 := by
  have hr (i : Index) := (ricci_contDiff hh i j).differentiable (by norm_num) x
  have hs := (scalar_contDiff hh).differentiable (by norm_num)
  have hm := divergence_metric_mul (hs.const_mul (1 / 2 : ℝ)) j x
  simp only [divergence, partial_const_mul _ ((hs x).const_mul (1 / 2 : ℝ))] at hm
  simp only [partial_const_mul _ (hs x)] at hm
  have hp (i : Index) : D i (einstein h i j) x =
      D i (ricci h i j) x - (metric i j / 2) * D i (scalarCurvature h) x := by
    change D i (fun y => ricci h i j y - (metric i j / 2) * scalarCurvature h y) x = _
    rw [partial_sub i (hr i) ((hs x).const_mul _), partial_const_mul i (hs x)]
  simp only [divergence, hp, mul_sub, Finset.sum_sub_distrib]
  change divergence (ricci h) j x - _ = 0
  rw [divergence_ricci hh]
  have hm' : (∑ i, sign i * (metric i j / 2 * D i (scalarCurvature h) x)) =
      (1 / 2 : ℝ) * D j (scalarCurvature h) x := by
    calc
      _ = ∑ i, sign i * (metric i j * ((1 / 2 : ℝ) * D i (scalarCurvature h) x)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := hm
  rw [hm', sub_self]

theorem wave_sub_scaled {f g : Field} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (a : ℝ) (x : Space) :
    wave (fun y => f y - a * g y) x = wave f x - a * wave g x := by
  have hd := hf.differentiable (by norm_num)
  have he := hg.differentiable (by norm_num)
  have hp (i : Index) : D i (fun y => f y - a * g y) = fun y => D i f y - a * D i g y := by
    funext y
    rw [partial_sub i (hd y) ((he y).const_mul a), partial_const_mul i (he y)]
  simp only [wave, hp]
  have hh (i : Index) : D i (fun y => D i f y - a * D i g y) x =
      D i (D i f) x - a * D i (D i g) x := by
    rw [partial_sub i ((partial_contDiff hf i).differentiable (by norm_num) x)
      (((partial_contDiff hg i).differentiable (by norm_num) x).const_mul a),
      partial_const_mul i ((partial_contDiff hg i).differentiable (by norm_num) x)]
  simp only [hh, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem divergence_add {T S : Tensor} (hT : Smooth 1 T) (hS : Smooth 1 S)
    (j : Index) (x : Space) :
    divergence (fun i k y => T i k y + S i k y) j x = divergence T j x + divergence S j x := by
  simp only [divergence, partial_add _ ((hT _ _).differentiable (by norm_num) x)
    ((hS _ _).differentiable (by norm_num) x), mul_add, Finset.sum_add_distrib]

theorem divergence_const_mul {T : Tensor} (hT : Smooth 1 T) (a : ℝ)
    (j : Index) (x : Space) :
    divergence (fun i k y => a * T i k y) j x = a * divergence T j x := by
  simp only [divergence, partial_const_mul _ ((hT _ _).differentiable (by norm_num) x), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem divergence_trace_reverse {h : Tensor} (hh : Smooth 1 h) (j : Index) (x : Space) :
    divergence (traceReverse h) j x = divergence h j x - (1 / 2 : ℝ) * D j (trace h) x := by
  have ht := (trace_contDiff hh).differentiable (by norm_num)
  have hd (i : Index) : D i (traceReverse h i j) x =
      D i (h i j) x - (metric i j / 2) * D i (trace h) x := by
    change D i (fun y => h i j y - (metric i j / 2) * trace h y) x = _
    rw [partial_sub i ((hh i j).differentiable (by norm_num) x) ((ht x).const_mul _),
      partial_const_mul i (ht x)]
  simp only [divergence, hd, mul_sub, Finset.sum_sub_distrib]
  congr 1
  have hm := divergence_metric_mul (ht.const_mul (1 / 2 : ℝ)) j x
  simp only [divergence, partial_const_mul _ ((ht x).const_mul (1 / 2 : ℝ)),
    partial_const_mul _ (ht x)] at hm
  convert hm using 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A gauge condition, not an assertion that a gauge-fixing transformation exists. -/
def LorenzGauge (h : Tensor) : Prop := ∀ j x, divergence (traceReverse h) j x = 0

theorem lorenz_gauge_iff {h : Tensor} (hh : Smooth 1 h) :
    LorenzGauge h ↔ ∀ j, divergence h j = fun x => (1 / 2 : ℝ) * D j (trace h) x := by
  simp only [LorenzGauge, divergence_trace_reverse hh, sub_eq_zero, funext_iff]

theorem einstein_in_lorenz_gauge {h : Tensor} (hh : Smooth 2 h) (hg : LorenzGauge h)
    (i j : Index) (x : Space) :
    einstein h i j x = -(1 / 2 : ℝ) * wave (traceReverse h i j) x := by
  have hh1 : Smooth 1 h := fun i j => (hh i j).of_le (by norm_num)
  have ht := trace_contDiff hh
  have hd (k : Index) := (partial_contDiff ht k).differentiable (by norm_num)
  have hg' := (lorenz_gauge_iff hh1).mp hg
  have hr (k l : Index) (y : Space) : ricci h k l y = -(1 / 2 : ℝ) * wave (h k l) y := by
    simp only [ricci, hg', partial_const_mul _ (hd _ y), mixed_partials ht l k y]
    ring
  have hs : scalarCurvature h x = -(1 / 2 : ℝ) * wave (trace h) x := by
    change (∑ k, sign k * ricci h k k x) = _
    simp only [hr]
    change _ = -(1 / 2 : ℝ) * wave (fun y => ∑ k, sign k * h k k y) x
    rw [wave_linear_combination sign (fun k => hh k k) x, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [einstein, hr, hs]
  change _ = -(1 / 2 : ℝ) * wave (fun y => h i j y - (metric i j / 2) * trace h y) x
  rw [wave_sub_scaled (hh i j) ht]
  ring

/-- Classical linearized equation. Symmetry and regularity are not hidden in a label. -/
def Solves (coupling : ℝ) (T h : Tensor) : Prop :=
  Smooth 3 h ∧ Symmetric h ∧ ∀ i j x, einstein h i j x = coupling * T i j x

theorem source_conservation {coupling : ℝ} {T h : Tensor}
    (hc : coupling ≠ 0) (hT : Smooth 1 T) (hsol : Solves coupling T h) :
    ∀ j x, divergence T j x = 0 := by
  have he : einstein h = fun i j x => coupling * T i j x := by
    funext i j x
    exact hsol.2.2 i j x
  intro j x
  have hb := contracted_bianchi hsol.1 j x
  rw [he, divergence_const_mul hT] at hb
  exact (mul_eq_zero.mp hb).resolve_left hc

def semiclassicalSource (expectation scalar recursive : Tensor) : Tensor :=
  fun i j x => expectation i j x + scalar i j x + recursive i j x
def cognitiveSource (thought recursive : Tensor) : Tensor :=
  fun i j x => thought i j x + recursive i j x

/-- ME-014: the expectation is an input, not a constructed or renormalized quantum state. -/
theorem semiclassical_balance {G : ℝ} {expectation scalar recursive h : Tensor}
    (hG : G ≠ 0) (hE : Smooth 1 expectation) (hS : Smooth 1 scalar) (hR : Smooth 1 recursive)
    (hsol : Solves (8 * Real.pi * G) (semiclassicalSource expectation scalar recursive) h) :
    ∀ j x, divergence expectation j x + divergence scalar j x + divergence recursive j x = 0 := by
  have ht : Smooth 1 (semiclassicalSource expectation scalar recursive) :=
    fun i j => ((hE i j).add (hS i j)).add (hR i j)
  have hc : 8 * Real.pi * G ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hG
  have hz := source_conservation hc ht hsol
  intro j x
  have htotal := hz j x
  change divergence (fun i k y => (expectation i k y + scalar i k y) + recursive i k y) j x = 0
    at htotal
  rw [divergence_add (T := fun i k y => expectation i k y + scalar i k y)
    (S := recursive) (fun i k => (hE i k).add (hS i k)) hR,
    divergence_add hE hS] at htotal
  exact htotal

/-- ME-039 with an authored linearized geometry and constant nonzero chi. -/
theorem cognitive_balance {chi : ℝ} {thought recursive h : Tensor}
    (hc : chi ≠ 0) (hT : Smooth 1 thought) (hR : Smooth 1 recursive)
    (hsol : Solves chi (cognitiveSource thought recursive) h) :
    ∀ j x, divergence thought j x + divergence recursive j x = 0 := by
  have ht : Smooth 1 (cognitiveSource thought recursive) := fun i j => (hT i j).add (hR i j)
  intro j x
  have hz := source_conservation hc ht hsol j x
  change divergence (fun i k y => thought i k y + recursive i k y) j x = 0 at hz
  rwa [divergence_add hT hR] at hz

theorem lorenz_field_equation_iff {h : Tensor} (hh : Smooth 2 h) (hg : LorenzGauge h)
    (coupling : ℝ) (T : Tensor) :
    (∀ i j x, einstein h i j x = coupling * T i j x) ↔
      ∀ i j x, wave (traceReverse h i j) x = -2 * coupling * T i j x := by
  simp only [einstein_in_lorenz_gauge hh hg]
  constructor <;> intro he i j x <;> have hp := he i j x <;> linarith

/-- Product rule makes the additional gradient term for a varying coupling explicit. -/
theorem divergence_variable_mul {a : Field} {T : Tensor}
    (ha : ContDiff ℝ 1 a) (hT : Smooth 1 T) (j : Index) (x : Space) :
    divergence (fun i k y => a y * T i k y) j x =
      (∑ i, sign i * D i a x * T i j x) + a x * divergence T j x := by
  simp only [divergence, partial_mul _ (ha.differentiable (by norm_num) x)
    ((hT _ _).differentiable (by norm_num) x), Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

def timeTensor (f : Field) : Tensor := fun i j x => if i = 0 ∧ j = 0 then f x else 0

theorem time_tensor_component (f : Field) (i j : Index) :
    timeTensor f i j = if i = 0 ∧ j = 0 then f else fun _ => 0 := by
  funext x
  by_cases hij : i = 0 ∧ j = 0 <;> simp [timeTensor, hij]

theorem time_tensor_smooth {f : Field} {n : ℕ} (hf : ContDiff ℝ n f) :
    Smooth n (timeTensor f) := by
  intro i j
  rw [time_tensor_component]
  split_ifs
  · exact hf
  · exact contDiff_const

theorem time_tensor_symmetric (f : Field) : Symmetric (timeTensor f) := by
  intro i j
  funext x
  simp [timeTensor, and_comm]

theorem divergence_time_tensor (f : Field) (x : Space) :
    divergence (timeTensor f) 0 x = D 0 f x := by
  simp [divergence, time_tensor_component, Fin.sum_univ_succ, partial_const, sign, ScalarAction.sign]

theorem time_source_divergence (x : Space) :
    divergence (timeTensor (fun y => y 0)) 0 x = 1 := by
  rw [divergence_time_tensor, partial_coordinate]
  norm_num

/-- A smooth symmetric source for which the linearized equation has no C3 solution. -/
theorem nonconserved_source_no_solution {coupling : ℝ} (hc : coupling ≠ 0) :
    ¬ ∃ h, Solves coupling (timeTensor (fun y => y 0)) h := by
  rintro ⟨h, hh⟩
  have hz := source_conservation hc (time_tensor_smooth (contDiff_apply ℝ ℝ 0)) hh 0 0
  rw [time_source_divergence] at hz
  norm_num at hz

/-- Constant source conservation does not survive multiplication by the time coordinate. -/
theorem varying_coupling_counterexample (x : Space) :
    divergence (timeTensor (fun _ => 1)) 0 x = 0 ∧
      divergence (fun i j y => y 0 * timeTensor (fun _ => 1) i j y) 0 x = 1 := by
  constructor
  · rw [divergence_time_tensor, partial_const]
  · have he : (fun i j y => y 0 * timeTensor (fun _ => 1) i j y) =
        timeTensor (fun y => y 0) := by
      funext i j y
      by_cases hij : i = 0 ∧ j = 0 <;> simp [timeTensor, hij]
    rw [he, time_source_divergence]

/-- A spatially varying coupling also creates divergence in a constant tensor source. -/
theorem spatial_coupling_counterexample (x : Space) :
    divergence (fun i j _ => metric i j) 1 x = 0 ∧
      divergence (fun i j y => y 1 * metric i j) 1 x = 1 := by
  constructor
  · simp [divergence, partial_const]
  · have he : (fun (i j : Index) (y : Space) => y 1 * metric i j) =
        (fun i j y => metric i j * y 1) := by
      funext i j y
      ring
    rw [he, divergence_metric_mul (fun y => (hasFDerivAt_apply 1 y).differentiableAt),
      partial_coordinate]
    norm_num

/-- The bracket in ME-015/040, with quadratic potential and the frozen (+---) metric. -/
def scalarEnergy (m2 : ℝ) (φ : Field) (x : Space) : ℝ :=
  (1 / 2 : ℝ) * (∑ k, sign k * (D k φ x) ^ 2) + (m2 / 2) * φ x ^ 2
def scalarStress (m2 : ℝ) (φ : Field) : Tensor := fun i j x =>
  D i φ x * D j φ x - metric i j * scalarEnergy m2 φ x

theorem scalar_stress_eq_catalogue (m2 : ℝ) (φ : Field) (i j : Index) (x : Space) :
    scalarStress m2 φ i j x =
      TensorModels.scalarStress metric (FlatScalar.minkowskiInverseMetric 1)
        (fun k => D k φ x) ((m2 / 2) * φ x ^ 2) i j := by
  rw [TensorModels.scalarStress, ScalarAction.contraction_eq_pairing]
  simp only [scalarStress, scalarEnergy, ScalarAction.pairing, pow_two, mul_assoc]
  ring

theorem scalar_energy_contDiff (m2 : ℝ) {φ : Field} (hφ : ContDiff ℝ 2 φ) :
    ContDiff ℝ 1 (scalarEnergy m2 φ) :=
  (contDiff_const.mul (ContDiff.sum (fun k _ =>
    contDiff_const.mul ((partial_contDiff hφ k).pow 2)))).add
      (contDiff_const.mul ((hφ.of_le (by norm_num)).pow 2))

theorem scalar_stress_smooth (m2 : ℝ) {φ : Field} (hφ : ContDiff ℝ 2 φ) :
    Smooth 1 (scalarStress m2 φ) := fun i j =>
  ((partial_contDiff hφ i).mul (partial_contDiff hφ j)).sub
    (contDiff_const.mul (scalar_energy_contDiff m2 hφ))

theorem partial_square {f : Field} {x : Space} (hf : DifferentiableAt ℝ f x) (j : Index) :
    D j (fun y => f y ^ 2) x = 2 * f x * D j f x := by
  simp only [pow_two]
  rw [partial_mul j hf hf]
  ring

theorem partial_scalar_energy (m2 : ℝ) {φ : Field} (hφ : ContDiff ℝ 2 φ)
    (j : Index) (x : Space) :
    D j (scalarEnergy m2 φ) x =
      (∑ k, sign k * D k φ x * D j (D k φ) x) + m2 * φ x * D j φ x := by
  have hd (k : Index) := (partial_contDiff hφ k).differentiable (by norm_num)
  have hf := hφ.differentiable (by norm_num)
  have hsq (k : Index) : Differentiable ℝ (fun y => (D k φ y) ^ 2) := by
    simpa only [Pi.pow_apply] using (hd k).pow 2
  have hf2 : DifferentiableAt ℝ (fun y => φ y ^ 2) x := by
    simpa only [Pi.pow_apply] using (hf x).pow 2
  have hs : Differentiable ℝ (fun y => ∑ k, sign k * (D k φ y) ^ 2) :=
    fun y => DifferentiableAt.fun_sum (fun k _ => (hsq k y).const_mul (sign k))
  change D j (fun y => (1 / 2 : ℝ) * (∑ k, sign k * (D k φ y) ^ 2) +
    (m2 / 2) * φ y ^ 2) x = _
  rw [partial_add j ((hs x).const_mul _) (hf2.const_mul _),
    partial_const_mul j (hs x), partial_const_mul j hf2,
    partial_linear_combination sign hsq]
  simp only [partial_square (hf x), partial_square (hd _ x), Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    ring
  · ring

/-- Off-shell scalar stress divergence, derived from the actual Hessian and product rule. -/
theorem scalar_stress_divergence (m2 : ℝ) {φ : Field} (hφ : ContDiff ℝ 2 φ)
    (j : Index) (x : Space) :
    divergence (scalarStress m2 φ) j x = (wave φ x - m2 * φ x) * D j φ x := by
  have hd (k : Index) := (partial_contDiff hφ k).differentiable (by norm_num) x
  have he := (scalar_energy_contDiff m2 hφ).differentiable (by norm_num)
  have hdprod (i : Index) : DifferentiableAt ℝ (fun y => D i φ y * D j φ y) x := by
    simpa only [Pi.mul_apply] using (hd i).mul (hd j)
  have hp (i : Index) : D i (scalarStress m2 φ i j) x =
      D i φ x * D i (D j φ) x + D j φ x * D i (D i φ) x -
        metric i j * D i (scalarEnergy m2 φ) x := by
    change D i (fun y => D i φ y * D j φ y - metric i j * scalarEnergy m2 φ y) x = _
    rw [partial_sub i (hdprod i) ((he x).const_mul _),
      partial_mul i (hd i) (hd j), partial_const_mul i (he x)]
  have hm := divergence_metric_mul he j x
  simp only [divergence, partial_const_mul _ (he x)] at hm
  have hh : divergence (scalarStress m2 φ) j x =
      (∑ i, sign i * D i φ x * D j (D i φ) x) + wave φ x * D j φ x -
        D j (scalarEnergy m2 φ) x := by
    simp only [divergence, hp, mixed_partials hφ _ j x, mul_sub, mul_add,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, hm]
    congr 1
    · congr 1
      · apply Finset.sum_congr rfl
        intro i _
        ring
      · simp only [wave, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
  rw [hh, partial_scalar_energy m2 hφ]
  ring

theorem stationary_scalar_exchange (m2 : ℝ) {J φ : Field} (hJ : Continuous J)
    (hφ : ContDiff ℝ 2 φ) (hs : ScalarAction.Stationary m2 J φ) (j : Index) (x : Space) :
    divergence (scalarStress m2 φ) j x = -J x * D j φ x := by
  have hr := (ScalarAction.stationary_iff_residual_zero m2 hJ hφ).mp hs x
  change FlatScalar.box 1 φ x - m2 * φ x + J x = 0 at hr
  rw [scalar_stress_divergence m2 hφ, wave_eq_box]
  have he : FlatScalar.box 1 φ x - m2 * φ x = -J x := by linarith
  rw [he]

/-- Other ME-014 source sectors must absorb the scalar source's exchange. -/
theorem semiclassical_scalar_exchange {G m2 : ℝ} {J φ : Field}
    {expectation recursive h : Tensor} (hG : G ≠ 0) (hE : Smooth 1 expectation)
    (hR : Smooth 1 recursive) (hJ : Continuous J) (hφ : ContDiff ℝ 2 φ)
    (hs : ScalarAction.Stationary m2 J φ)
    (hsol : Solves (8 * Real.pi * G)
      (semiclassicalSource expectation (scalarStress m2 φ) recursive) h) (j : Index) (x : Space) :
    divergence expectation j x + divergence recursive j x = J x * D j φ x := by
  have hb := semiclassical_balance hG hE (scalar_stress_smooth m2 hφ) hR hsol j x
  rw [stationary_scalar_exchange m2 hJ hφ hs] at hb
  linarith

/-- ME-039/040's real scalar specialization requires the same exchange in its recursive source. -/
theorem cognitive_scalar_exchange {chi m2 : ℝ} {J φ : Field}
    {recursive h : Tensor} (hc : chi ≠ 0) (hR : Smooth 1 recursive)
    (hJ : Continuous J) (hφ : ContDiff ℝ 2 φ) (hs : ScalarAction.Stationary m2 J φ)
    (hsol : Solves chi (cognitiveSource (scalarStress m2 φ) recursive) h) (j : Index) (x : Space) :
    divergence recursive j x = J x * D j φ x := by
  have hb := cognitive_balance hc (scalar_stress_smooth m2 hφ) hR hsol j x
  rw [stationary_scalar_exchange m2 hJ hφ hs] at hb
  linarith

end MonolithicAnalysis.LinearizedGravity
