module

public import Involution.Folding.GeneralBCFoldForward

/-! # Развёртывание решения системы в собственную функцию (C24, шаг 2, обратное)

Для `v ∈ ker (V₀ + V₁ Φ(1, λ))` решение `X = Φ(·, λ) v` склеивается в
`y(x) = X₁(x)` при `x ≥ 0`, `y(x) = X₂(-x)` при `x < 0` и т. д.; доказывается, что
`(y, y', y'')` — решение задачи (1), (2) (`foldY_isSolution`): `y`, `y'` абсолютно непрерывны
на `[-1,1]` (кусочная формула Ньютона–Лейбница), (1) выполнено почти всюду, (2) — по ядру. -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Interval Matrix

namespace Involution
namespace GeneralBC
variable {a : ℝ → ℝ} {U : Forms} {lam : ℂ}

/-- Решение системы с начальным вектором `v`. -/
def foldX (a : ℝ → ℝ) (lam : ℂ) (v : Fin 4 → ℂ) (x : ℝ) : Fin 4 → ℂ := foldPhi a x lam *ᵥ v

/-- Производная решения: `(A₀ + λ A₁) X`. -/
def foldXd (a : ℝ → ℝ) (lam : ℂ) (v : Fin 4 → ℂ) (x : ℝ) : Fin 4 → ℂ :=
  (foldA0 x + lam • foldA1 a x) *ᵥ foldX a lam v x

theorem foldB_mulVec' (a : ℝ → ℝ) (lam : ℂ) (u : Fin 4 → ℂ) (t : ℝ) :
    (foldA0 t + lam • foldA1 a t) *ᵥ u =
      ![u 2, u 3, lam * qfun a t * ((a t : ℂ) * u 1 - u 0),
        lam * qfun a t * ((a (-t) : ℂ) * u 0 - u 1)] := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, foldA0, foldA1] <;> ring

theorem foldX_continuousOn (a : ℝ → ℝ) (lam : ℂ) (v : Fin 4 → ℂ) :
    ContinuousOn (foldX a lam v) (Icc 0 1) :=
  (LinearCauchy.continuous_cauchy_mulVec foldA0 (foldA1 a) lam v).continuousOn

theorem foldXd_continuousOn {m κ : ℝ} (hH : HypH a m κ) (lam : ℂ) (v : Fin 4 → ℂ) :
    ContinuousOn (foldXd a lam v) (Icc 0 1) :=
  LinearCauchy.continuousOn_mulVec (foldB_continuousOn hH lam) (foldX_continuousOn a lam v)

theorem foldX_hasDerivWithinAt {m κ : ℝ} (hH : HypH a m κ) (lam : ℂ) (v : Fin 4 → ℂ)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (i : Fin 4) :
    HasDerivWithinAt (fun s => foldX a lam v s i) (foldXd a lam v x i) (Icc 0 1) x := by
  have := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun j _ =>
    (linearCauchy_hasDerivWithinAt (A₀ := foldA0) (A₁ := foldA1 a) continuousOn_const
      (foldA1_continuousOn ⟨m, κ, hH⟩) lam hx i j).mul_const (v j))
  convert this using 1
  · ext s; simp [foldX, foldPhi, Matrix.mulVec, dotProduct]
  · simp only [foldXd, Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, foldX, foldPhi, Matrix.mul_apply, Finset.sum_mul]
    simp_rw [Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm

theorem hasDerivAt_foldX_pos {m κ : ℝ} (hH : HypH a m κ) (lam : ℂ) (v : Fin 4 → ℂ) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (i : Fin 4) :
    HasDerivAt (fun s => foldX a lam v s i) (foldXd a lam v u i) u :=
  (foldX_hasDerivWithinAt hH lam v (Ioo_subset_Icc_self hu) i).hasDerivAt
    (Icc_mem_nhds hu.1 hu.2)

theorem hasDerivAt_foldX_neg {m κ : ℝ} (hH : HypH a m κ) (lam : ℂ) (v : Fin 4 → ℂ) {x : ℝ}
    (hx : -x ∈ Ioo (0 : ℝ) 1) (i : Fin 4) :
    HasDerivAt (fun s => foldX a lam v (-s) i) (-foldXd a lam v (-x) i) x := by
  have h1 := hasDerivAt_foldX_pos hH lam v hx i
  have h2 := h1.scomp x (hasDerivAt_neg x)
  simp only [neg_smul, one_smul] at h2
  exact h2

/-- Склейка: `y(x) = X₀(x)` при `x ≥ 0`, `y(x) = X₁(-x)` при `x < 0`. -/
def foldY (a : ℝ → ℝ) (lam : ℂ) (v : Fin 4 → ℂ) (x : ℝ) : ℂ :=
  if 0 ≤ x then foldX a lam v x 0 else foldX a lam v (-x) 1

def foldY' (a : ℝ → ℝ) (lam : ℂ) (v : Fin 4 → ℂ) (x : ℝ) : ℂ :=
  if 0 ≤ x then foldX a lam v x 2 else -foldX a lam v (-x) 3

def foldY'' (a : ℝ → ℝ) (lam : ℂ) (v : Fin 4 → ℂ) (x : ℝ) : ℂ :=
  if 0 < x then foldXd a lam v x 2 else foldXd a lam v (-x) 3

theorem foldX_zero (a : ℝ → ℝ) (lam : ℂ) (v : Fin 4 → ℂ) : foldX a lam v 0 = v := by
  simp [foldX, foldPhi, linearCauchy_zero]

theorem ker_glue (hv : foldMat a U lam *ᵥ v = 0) : v 0 = v 1 ∧ v 2 + v 3 = 0 := by
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  simp only [Matrix.mulVec, dotProduct, foldMat, foldV0, foldV1, Fin.isValue, Matrix.cons_mul,
    Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.zero_vecMul, Matrix.empty_mul,
    Equiv.symm_apply_apply, Matrix.add_apply, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_fin_one, Matrix.cons_val_zero, Pi.zero_apply, add_zero, Fin.sum_univ_four,
    one_mul, Matrix.cons_val_one, neg_mul, Matrix.cons_val, zero_mul, zero_add] at h0 h1
  exact ⟨by linear_combination h0, h1⟩

theorem hasDerivAt_foldY {m κ : ℝ} (hH : HypH a m κ) (lam : ℂ) (v : Fin 4 → ℂ) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    HasDerivAt (foldY a lam v) (foldY' a lam v x) x := by
  rcases lt_or_gt_of_ne hx0 with h | h
  · have hu : -x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith [hx.1]⟩
    have := hasDerivAt_foldX_neg hH lam v hu 1
    refine this.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · filter_upwards [Iio_mem_nhds h] with t (ht : t < 0)
      simp [foldY, not_le.2 ht]
    · simp [foldY', not_le.2 h, foldXd, foldB_mulVec']
  · have hu : x ∈ Ioo (0 : ℝ) 1 := ⟨h, hx.2⟩
    have := hasDerivAt_foldX_pos hH lam v hu 0
    refine this.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · filter_upwards [Ioi_mem_nhds h] with t (ht : 0 < t)
      simp [foldY, le_of_lt ht]
    · simp [foldY', h.le, foldXd, foldB_mulVec']

theorem hasDerivAt_foldY' {m κ : ℝ} (hH : HypH a m κ) (lam : ℂ) (v : Fin 4 → ℂ) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    HasDerivAt (foldY' a lam v) (foldY'' a lam v x) x := by
  rcases lt_or_gt_of_ne hx0 with h | h
  · have hu : -x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith [hx.1]⟩
    have := (hasDerivAt_foldX_neg hH lam v hu 3).neg
    refine this.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · filter_upwards [Iio_mem_nhds h] with t (ht : t < 0)
      simp [foldY', not_le.2 ht]
    · simp [foldY'', not_lt.2 h.le]
  · have hu : x ∈ Ioo (0 : ℝ) 1 := ⟨h, hx.2⟩
    have := hasDerivAt_foldX_pos hH lam v hu 2
    refine this.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · filter_upwards [Ioi_mem_nhds h] with t (ht : 0 < t)
      simp [foldY', le_of_lt ht]
    · simp [foldY'', h]

theorem glue_continuousOn {f g h : ℝ → ℂ} (hf : ∀ x, f x = if 0 ≤ x then g x else h (-x))
    (hg : ContinuousOn g (Icc 0 1)) (hh : ContinuousOn h (Icc 0 1)) (h0 : g 0 = h 0) :
    ContinuousOn f (Icc (-1) 1) := by
  have e : Icc (-1 : ℝ) 1 = Icc (-1) 0 ∪ Icc 0 1 :=
    (Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)).symm
  rw [e]
  refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
  · have h1 : ContinuousOn (fun x => h (-x)) (Icc (-1) 0) :=
      hh.comp continuous_neg.continuousOn (fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩)
    refine h1.congr (fun x hx => ?_)
    rw [hf x]
    rcases eq_or_lt_of_le hx.2 with h | h
    · subst h; simp [h0]
    · simp [not_le.2 h]
  · refine hg.congr (fun x hx => ?_)
    rw [hf x]; simp [hx.1]

theorem glue_integrable {f g h : ℝ → ℂ} (hf : ∀ x, f x = if 0 < x then g x else h (-x))
    (hg : ContinuousOn g (Icc 0 1)) (hh : ContinuousOn h (Icc 0 1)) :
    IntervalIntegrable f volume (-1) 1 := by
  have i1 : IntervalIntegrable f volume (-1) 0 := by
    have h1 : ContinuousOn (fun x => h (-x)) (uIcc (-1) 0) := by
      rw [uIcc_of_le (by norm_num)]
      exact hh.comp continuous_neg.continuousOn
        (fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩)
    refine h1.intervalIntegrable.congr (fun x hx => ?_)
    rw [uIoc_of_le (by norm_num)] at hx
    rw [hf x]; simp [not_lt.2 hx.2]
  have i2 : IntervalIntegrable f volume 0 1 := by
    have h1 : ContinuousOn g (uIcc 0 1) := by rw [uIcc_of_le (by norm_num)]; exact hg
    refine h1.intervalIntegrable.congr (fun x hx => ?_)
    rw [uIoc_of_le (by norm_num)] at hx
    rw [hf x]; simp [hx.1]
  exact i1.trans i2

theorem ac_of_repr {g g' : ℝ → ℂ} (hi : IntervalIntegrable g' volume (-1) 1)
    (hg : ∀ x ∈ Icc (-1 : ℝ) 1, g x = g 0 + ∫ t in (0 : ℝ)..x, g' t) :
    AbsolutelyContinuousOnInterval g (-1) 1 := by
  have h0 : (0 : ℝ) ∈ uIcc (-1 : ℝ) 1 := by
    rw [uIcc_of_le (by norm_num)]; exact ⟨by norm_num, by norm_num⟩
  have h1 := ac_integral_complex hi h0
  have h2 : AbsolutelyContinuousOnInterval (fun _ : ℝ => g 0) (-1) 1 :=
    ContDiffOn.absolutelyContinuousOnInterval (f := fun _ : ℝ => g 0) contDiffOn_const
  have h3 := h2.add h1
  refine h3.congr (fun x hx => ?_)
  rw [uIcc_of_le (by norm_num)] at hx
  simp [hg x hx]

theorem foldX_comp_continuousOn (a : ℝ → ℝ) (lam : ℂ) (v : Fin 4 → ℂ) (i : Fin 4) :
    ContinuousOn (fun x => foldX a lam v x i) (Icc 0 1) :=
  continuousOn_pi.1 (foldX_continuousOn a lam v) i

theorem foldXd_comp_continuousOn {m κ : ℝ} (hH : HypH a m κ) (lam : ℂ) (v : Fin 4 → ℂ)
    (i : Fin 4) : ContinuousOn (fun x => foldXd a lam v x i) (Icc 0 1) :=
  continuousOn_pi.1 (foldXd_continuousOn hH lam v) i

theorem foldY_continuousOn (hv : foldMat a U lam *ᵥ v = 0) :
    ContinuousOn (foldY a lam v) (Icc (-1) 1) :=
  glue_continuousOn (g := fun x => foldX a lam v x 0) (h := fun x => foldX a lam v x 1)
    (fun _ => rfl) (foldX_comp_continuousOn a lam v 0) (foldX_comp_continuousOn a lam v 1)
    (by simp [foldX_zero, (ker_glue hv).1])

theorem foldY'_continuousOn (hv : foldMat a U lam *ᵥ v = 0) :
    ContinuousOn (foldY' a lam v) (Icc (-1) 1) :=
  glue_continuousOn (g := fun x => foldX a lam v x 2) (h := fun x => -foldX a lam v x 3)
    (fun _ => rfl) (foldX_comp_continuousOn a lam v 2) (foldX_comp_continuousOn a lam v 3).neg
    (by have := (ker_glue hv).2; simp [foldX_zero]; linear_combination this)

theorem foldY''_integrable {m κ : ℝ} (hH : HypH a m κ) (lam : ℂ) (v : Fin 4 → ℂ) :
    IntervalIntegrable (foldY'' a lam v) volume (-1) 1 :=
  glue_integrable (g := fun x => foldXd a lam v x 2) (h := fun x => foldXd a lam v x 3)
    (fun _ => rfl) (foldXd_comp_continuousOn hH lam v 2) (foldXd_comp_continuousOn hH lam v 3)

theorem ae_ne_zero : ∀ᵐ t : ℝ, t ≠ 0 := (Set.countable_singleton (0 : ℝ)).ae_notMem _

theorem foldY_eqn {m κ : ℝ} (hH : HypH a m κ) (lam : ℂ) (v : Fin 4 → ℂ) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    -foldY'' a lam v x - (a x : ℂ) * foldY'' a lam v (-x) = lam * foldY a lam v x := by
  rcases lt_or_gt_of_ne hx0 with h | h
  · have hq := qfun_mul hH (t := -x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
    simp only [neg_neg] at hq
    simp [foldY'', foldY, not_lt.2 h.le, not_le.2 h, neg_pos.2 h, foldXd, foldB_mulVec']
    linear_combination (lam * foldX a lam v (-x) 1) * hq
  · have hq := qfun_mul hH (t := x) (Ioo_subset_Icc_self hx)
    simp [foldY'', foldY, h, h.le, not_lt.2 (neg_nonpos.2 h.le), foldXd, foldB_mulVec']
    linear_combination (lam * foldX a lam v x 0) * hq

theorem foldMat_mulVec_eq (a : ℝ → ℝ) (U : Forms) (lam : ℂ) (v : Fin 4 → ℂ) :
    foldMat a U lam *ᵥ v = foldV0 *ᵥ v + foldV1 U *ᵥ foldX a lam v 1 := by
  rw [foldMat, Matrix.add_mulVec, ← Matrix.mulVec_mulVec]; rfl

theorem foldY_bc (hv : foldMat a U lam *ᵥ v = 0) (j : Fin 2) :
    U.eval j (foldY a lam v) (foldY' a lam v) = 0 := by
  rw [foldMat_mulVec_eq] at hv
  have h2 := congrFun hv 2
  have h3 := congrFun hv 3
  simp [foldV0, foldV1, dotProduct, Fin.sum_univ_four] at h2 h3
  have h10 : ¬ (1 : ℝ) ≤ 0 := by norm_num
  fin_cases j
  · simp [Forms.eval, foldY, foldY', h10]
    linear_combination h2
  · simp [Forms.eval, foldY, foldY', h10]
    linear_combination h3

theorem foldY_isSolution {m κ : ℝ} (hH : HypH a m κ) (hv : foldMat a U lam *ᵥ v = 0) :
    IsSolution a U lam (foldY a lam v) (foldY' a lam v) (foldY'' a lam v) := by
  have hI : ∀ {f : ℝ → ℂ}, ContinuousOn f (Icc (-1) 1) → IntervalIntegrable f volume (-1) 1 :=
    fun hf => (hf.mono (by rw [uIcc_of_le (by norm_num)])).intervalIntegrable
  have hI' := hI (foldY'_continuousOn hv)
  have hI'' := foldY''_integrable hH lam v
  exact
  { ac_y := ac_of_repr hI' (ftc_piecewise (foldY_continuousOn hv)
      (fun x hx hx0 => hasDerivAt_foldY hH lam v hx hx0) hI')
    ac_y' := ac_of_repr hI'' (ftc_piecewise (foldY'_continuousOn hv)
      (fun x hx hx0 => hasDerivAt_foldY' hH lam v hx hx0) hI'')
    deriv_y := by
      filter_upwards [ae_ne_zero] with x hx0 hx using hasDerivAt_foldY hH lam v hx hx0
    deriv_y' := by
      filter_upwards [ae_ne_zero] with x hx0 hx using hasDerivAt_foldY' hH lam v hx hx0
    eqn := by
      filter_upwards [ae_ne_zero] with x hx0 hx using foldY_eqn hH lam v hx hx0
    bc := foldY_bc hv }
end GeneralBC
end Involution
