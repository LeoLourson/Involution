module

public import Involution.Setup.LinearCauchy

/-! Единственность решений интегрального уравнения `X(x) = X(0) + ∫₀ˣ (A₀ + λ A₁) X` и
обратимость матрицы Коши `Φ(x, λ)`. -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Matrix Matrix.Norms.Operator

namespace Involution

variable {n : ℕ}

namespace LinearCauchy

/-- Векторная форма интегрального уравнения для столбцов `Φ`. -/
theorem mulVec_integral {A₀ A₁ : ℝ → Matrix (Fin n) (Fin n) ℂ}
    (hA₀ : ContinuousOn A₀ (Icc 0 1)) (hA₁ : ContinuousOn A₁ (Icc 0 1)) (l : ℂ)
    (v : Fin n → ℂ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    linearCauchy A₀ A₁ x l *ᵥ v
      = v + ∫ t in (0 : ℝ)..x, (A₀ t + l • A₁ t) *ᵥ (linearCauchy A₀ A₁ t l *ᵥ v) := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun M => M *ᵥ v
      map_add' := fun M N => Matrix.add_mulVec M N v
      map_smul' := fun c M => Matrix.smul_mulVec c M v }
  have h1 : linearCauchy A₀ A₁ x l = 1 + ∫ t in (0 : ℝ)..x, (ext (coeff A₀) t
      + l • ext (coeff A₁) t) * ext (psi (coeff A₀) (coeff A₁) l) t := by
    rw [linearCauchy_eq_ext, ext_of_mem _ hx]
    exact psi_apply (coeff A₀) (coeff A₁) l ⟨x, hx⟩
  have h2 := integral_linear_comm L (a := 0) (b := x) (continuous_integrand A₀ A₁ l)
  have h3 : L (∫ t in (0 : ℝ)..x, (ext (coeff A₀) t + l • ext (coeff A₁) t)
      * ext (psi (coeff A₀) (coeff A₁) l) t)
      = ∫ t in (0 : ℝ)..x, (A₀ t + l • A₁ t) *ᵥ (linearCauchy A₀ A₁ t l *ᵥ v) := by
    rw [← h2]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le hx.1] at ht
    have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hx.2⟩
    change (_ * _) *ᵥ v = _
    rw [← Matrix.mulVec_mulVec, ext_coeff hA₀ ht1, ext_coeff hA₁ ht1]
    rfl
  rw [← h3, h1, Matrix.add_mulVec, Matrix.one_mulVec]
  rfl

lemma continuousOn_mulVec {A : ℝ → Matrix (Fin n) (Fin n) ℂ} {X : ℝ → Fin n → ℂ} {s : Set ℝ}
    (hA : ContinuousOn A s) (hX : ContinuousOn X s) :
    ContinuousOn (fun t => A t *ᵥ X t) s := by
  refine continuousOn_pi.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  refine continuousOn_finsetSum _ fun j _ => ?_
  exact ((continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hA)).mul
    ((continuous_apply j).comp_continuousOn hX)

lemma continuous_cauchy_mulVec (A₀ A₁ : ℝ → Matrix (Fin n) (Fin n) ℂ) (l : ℂ)
    (v : Fin n → ℂ) : Continuous fun x => linearCauchy A₀ A₁ x l *ᵥ v := by
  refine continuous_pi fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact continuous_finsetSum _ fun j _ => (continuous_linearCauchy A₀ A₁ l i j).mul
    continuous_const

/-- Оценка `‖(A₀ t + λ A₁ t) w‖ ≤ M ‖w‖` с `M = ‖a₀‖ + |λ| ‖a₁‖`. -/
lemma norm_mulVec_le {A₀ A₁ : ℝ → Matrix (Fin n) (Fin n) ℂ}
    (hA₀ : ContinuousOn A₀ (Icc 0 1)) (hA₁ : ContinuousOn A₁ (Icc 0 1)) (l : ℂ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (w : Fin n → ℂ) :
    ‖(A₀ t + l • A₁ t) *ᵥ w‖ ≤ (‖coeff A₀‖ + ‖l‖ * ‖coeff A₁‖) * ‖w‖ := by
  refine (Matrix.linfty_opNorm_mulVec _ w).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul]
  have h0 : ‖A₀ t‖ ≤ ‖coeff A₀‖ := by rw [← ext_coeff hA₀ ht]; exact norm_ext_le _ _
  have h1 : ‖A₁ t‖ ≤ ‖coeff A₁‖ := by rw [← ext_coeff hA₁ ht]; exact norm_ext_le _ _
  gcongr

end LinearCauchy

/-- Единственность. Пусть `X : ℝ → ℂⁿ` непрерывна на `[0,1]` и удовлетворяет
`X(x) = X(0) + ∫₀ˣ (A₀ + λ A₁) X` при `x ∈ [0,1]`. Тогда `X(x) = Φ(x, λ) X(0)`. -/
theorem linearCauchy_unique {A₀ A₁ : ℝ → Matrix (Fin n) (Fin n) ℂ}
    (hA₀ : ContinuousOn A₀ (Icc 0 1)) (hA₁ : ContinuousOn A₁ (Icc 0 1)) (l : ℂ)
    {X : ℝ → Fin n → ℂ} (hX : ContinuousOn X (Icc 0 1))
    (hint : ∀ x ∈ Icc (0 : ℝ) 1,
      X x = X 0 + ∫ t in (0 : ℝ)..x, (A₀ t + l • A₁ t) *ᵥ X t) :
    ∀ x ∈ Icc (0 : ℝ) 1, X x = linearCauchy A₀ A₁ x l *ᵥ X 0 := by
  set Y : ℝ → Fin n → ℂ := fun x => linearCauchy A₀ A₁ x l *ᵥ X 0 with hY
  have hYc : ContinuousOn Y (Icc 0 1) :=
    (LinearCauchy.continuous_cauchy_mulVec A₀ A₁ l _).continuousOn
  have hBc : ContinuousOn (fun t => A₀ t + l • A₁ t) (Icc 0 1) := hA₀.add (hA₁.const_smul l)
  have hXi := LinearCauchy.continuousOn_mulVec hBc hX
  have hYi := LinearCauchy.continuousOn_mulVec hBc hYc
  have hsub : ∀ x ∈ Icc (0 : ℝ) 1, uIcc 0 x ⊆ Icc (0 : ℝ) 1 := fun x hx => by
    rw [uIcc_of_le hx.1]; exact Icc_subset_Icc le_rfl hx.2
  have hmain : ∀ x ∈ Icc (0 : ℝ) 1,
      X x - Y x = ∫ t in (0 : ℝ)..x, (A₀ t + l • A₁ t) *ᵥ (X t - Y t) := by
    intro x hx
    have h1 := hint x hx
    have h2 := LinearCauchy.mulVec_integral hA₀ hA₁ l (X 0) hx
    have hi1 : IntervalIntegrable (fun t => (A₀ t + l • A₁ t) *ᵥ X t) volume 0 x :=
      (hXi.mono (hsub x hx)).intervalIntegrable
    have hi2 : IntervalIntegrable (fun t => (A₀ t + l • A₁ t) *ᵥ Y t) volume 0 x :=
      (hYi.mono (hsub x hx)).intervalIntegrable
    simp only [Matrix.mulVec_sub]
    rw [intervalIntegral.integral_sub hi1 hi2]
    change X x - linearCauchy A₀ A₁ x l *ᵥ X 0 = _
    rw [h1, h2]
    abel
  have key := eq_zero_of_integral_eq (u := fun x => X x - Y x)
    (F := fun t => (A₀ t + l • A₁ t) *ᵥ (X t - Y t))
    (M := ‖LinearCauchy.coeff A₀‖ + ‖l‖ * ‖LinearCauchy.coeff A₁‖) (hX.sub hYc)
    (add_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    (fun t ht => LinearCauchy.norm_mulVec_le hA₀ hA₁ l ht _) hmain
  exact fun x hx => sub_eq_zero.mp (key x hx)

/-- Обратимость: `det Φ(x, λ) ≠ 0` при `x ∈ [0,1]`. -/
theorem linearCauchy_det_ne_zero {A₀ A₁ : ℝ → Matrix (Fin n) (Fin n) ℂ}
    (hA₀ : ContinuousOn A₀ (Icc 0 1)) (hA₁ : ContinuousOn A₁ (Icc 0 1)) (l : ℂ) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Icc (0 : ℝ) 1) : (linearCauchy A₀ A₁ x₀ l).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set Y : ℝ → Fin n → ℂ := fun x => linearCauchy A₀ A₁ x l *ᵥ v with hY
  have hYc : ContinuousOn Y (Icc 0 1) :=
    (LinearCauchy.continuous_cauchy_mulVec A₀ A₁ l _).continuousOn
  have hBc : ContinuousOn (fun t => A₀ t + l • A₁ t) (Icc 0 1) := hA₀.add (hA₁.const_smul l)
  have hYi := LinearCauchy.continuousOn_mulVec hBc hYc
  have hsub : ∀ x ∈ Icc (0 : ℝ) 1, uIcc 0 x ⊆ Icc (0 : ℝ) 1 := fun x hx => by
    rw [uIcc_of_le hx.1]; exact Icc_subset_Icc le_rfl hx.2
  have hint : ∀ x ∈ Icc (0 : ℝ) 1, Y x = v + ∫ t in (0 : ℝ)..x, (A₀ t + l • A₁ t) *ᵥ Y t :=
    fun x hx => LinearCauchy.mulVec_integral hA₀ hA₁ l v hx
  have hY0 : Y x₀ = 0 := hv0
  have h0 := eq_zero_at_zero_of_integral_eq (u := Y) (F := fun t => (A₀ t + l • A₁ t) *ᵥ Y t)
    (M := ‖LinearCauchy.coeff A₀‖ + ‖l‖ * ‖LinearCauchy.coeff A₁‖) hx₀ hYc
    (add_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    (fun t ht => LinearCauchy.norm_mulVec_le hA₀ hA₁ l ht _) (fun x hx => by
      have e1 := hint x hx
      have e2 := hint x₀ hx₀
      have hi : ∀ y ∈ Icc (0 : ℝ) 1, IntervalIntegrable
          (fun t => (A₀ t + l • A₁ t) *ᵥ Y t) volume 0 y := fun y hy =>
        (hYi.mono (hsub y hy)).intervalIntegrable
      rw [← intervalIntegral.integral_interval_sub_left (hi x hx) (hi x₀ hx₀)]
      rw [hY0] at e2
      have : (∫ t in (0 : ℝ)..x₀, (A₀ t + l • A₁ t) *ᵥ Y t) = -v := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact e2.symm
      rw [this, e1]
      abel)
  have hv' : Y 0 = v := by
    change linearCauchy A₀ A₁ 0 l *ᵥ v = v
    rw [linearCauchy_zero, Matrix.one_mulVec]
  exact hv (hv'.symm.trans h0)

end Involution

end
