module

public import Involution.Folding.GeneralBCFoldSol
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Складывание собственной функции в решение системы (C24, шаг 2)

Для решения `y ∈ W²₁(-1,1)` задачи (1), (2) вектор `w = (y(x), y(-x), y'(x), -y'(-x))`
непрерывен и удовлетворяет интегральному уравнению `w(x) = w(0) + ∫₀ˣ (A₀ + λA₁) w`
на `[0,1]`; по единственности `w(x) = Φ(x, λ) w(0)`, и `w(0)` лежит в ядре
`V₀ + V₁ Φ(1, λ)`. Формула Ньютона–Лейбница для абсолютно непрерывных функций —
`GeneralBCFoldCalc`. -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Interval Matrix

namespace Involution
namespace GeneralBC

variable {a : ℝ → ℝ} {U : Forms} {lam : ℂ} {y y' y'' : ℝ → ℂ}

theorem ae_comp_neg {P : ℝ → Prop} (h : ∀ᵐ x : ℝ, P x) : ∀ᵐ x : ℝ, P (-x) := by
  rw [ae_iff] at h ⊢
  have := Real.volume_preimage_mul_left (a := (-1 : ℝ)) (by norm_num) {x | ¬ P x}
  simp only [neg_mul, one_mul] at this
  have e : {x : ℝ | ¬ P (-x)} = (fun x => -x) ⁻¹' {x | ¬ P x} := rfl
  rw [e]
  simpa [h] using this

theorem qfun_mul {m κ : ℝ} (hH : HypH a m κ) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    qfun a t * (1 - (a t : ℂ) * (a (-t) : ℂ)) = 1 := by
  have h1 := hH.upper t ht
  have h2 := hH.kappa_lt
  have hne : (1 - a t * a (-t)) ≠ 0 := by linarith
  unfold qfun
  have : ((1 - a t * a (-t))⁻¹ : ℝ) * (1 - a t * a (-t)) = 1 := inv_mul_cancel₀ hne
  exact_mod_cast this

theorem ode_ae {m κ : ℝ} (hH : HypH a m κ) (h : IsSolution a U lam y y' y'') :
    ∀ᵐ t : ℝ, t ∈ Ioo (-1 : ℝ) 1 →
      y'' t = lam * qfun a t * ((a t : ℂ) * y (-t) - y t) ∧
      y'' (-t) = lam * qfun a t * ((a (-t) : ℂ) * y t - y (-t)) := by
  filter_upwards [h.eqn, ae_comp_neg h.eqn] with t h1 h2 ht
  have ht' : t ∈ Icc (-1 : ℝ) 1 := Ioo_subset_Icc_self ht
  have E1 := h1 ht
  have E2 := h2 ⟨by linarith [ht.2], by linarith [ht.1]⟩
  rw [neg_neg] at E2
  have hq := qfun_mul hH ht'
  set q := qfun a t
  constructor
  · have key : y'' t * (1 - (a t : ℂ) * a (-t)) = lam * ((a t : ℂ) * y (-t) - y t) := by
      linear_combination (-1) * E1 + (a t : ℂ) * E2
    calc y'' t = y'' t * (q * (1 - (a t : ℂ) * a (-t))) := by rw [hq, mul_one]
      _ = _ := by linear_combination q * key
  · have key : y'' (-t) * (1 - (a t : ℂ) * a (-t)) = lam * ((a (-t) : ℂ) * y t - y (-t)) := by
      linear_combination (-1) * E2 + (a (-t) : ℂ) * E1
    calc y'' (-t) = y'' (-t) * (q * (1 - (a t : ℂ) * a (-t))) := by rw [hq, mul_one]
      _ = _ := by linear_combination q * key

/-- Складывание `w = (y(x), y(-x), y'(x), -y'(-x))`. -/
def foldW (y y' : ℝ → ℂ) (x : ℝ) : Fin 4 → ℂ := ![y x, y (-x), y' x, -y' (-x)]

theorem foldB_mulVec (a : ℝ → ℝ) (lam : ℂ) (y y' : ℝ → ℂ) (t : ℝ) :
    (foldA0 t + lam • foldA1 a t) *ᵥ foldW y y' t =
      ![y' t, -y' (-t), lam * qfun a t * ((a t : ℂ) * y (-t) - y t),
        lam * qfun a t * ((a (-t) : ℂ) * y t - y (-t))] := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, foldA0, foldA1, foldW] <;> ring

theorem integral_apply_pi {f : ℝ → Fin 4 → ℂ} {a b : ℝ} (hf : IntervalIntegrable f volume a b)
    (i : Fin 4) : (∫ t in a..b, f t) i = ∫ t in a..b, f t i :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 4 => ℂ) i).intervalIntegral_comp_comm
    hf).symm

theorem ae_ne_one : ∀ᵐ t : ℝ, t ≠ 1 := (Set.countable_singleton (1 : ℝ)).ae_notMem _

theorem foldW_continuousOn (h : IsSolution a U lam y y' y'') :
    ContinuousOn (foldW y y') (Icc 0 1) := by
  have hy := h.continuousOn_y
  have hy' := h.continuousOn_y'
  have hneg : MapsTo (fun t : ℝ => -t) (Icc 0 1) (Icc (-1) 1) := fun t ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hpos : Icc (0 : ℝ) 1 ⊆ Icc (-1) 1 := Icc_subset_Icc (by norm_num) le_rfl
  refine continuousOn_pi.2 fun i => ?_
  fin_cases i
  · exact hy.mono hpos
  · exact hy.comp continuous_neg.continuousOn hneg
  · exact hy'.mono hpos
  · exact (hy'.comp continuous_neg.continuousOn hneg).neg

theorem foldB_continuousOn {m κ : ℝ} (hH : HypH a m κ) (lam : ℂ) :
    ContinuousOn (fun t => foldA0 t + lam • foldA1 a t) (Icc 0 1) :=
  continuousOn_const.add ((foldA1_continuousOn ⟨m, κ, hH⟩).const_smul lam)

theorem foldW_integral {m κ : ℝ} (hH : HypH a m κ) (h : IsSolution a U lam y y' y'')
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    foldW y y' x = foldW y y' 0 +
      ∫ t in (0 : ℝ)..x, (foldA0 t + lam • foldA1 a t) *ᵥ foldW y y' t := by
  have hxI : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
  have hnxI : -x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hcont : ContinuousOn (fun t => (foldA0 t + lam • foldA1 a t) *ᵥ foldW y y' t)
      (Icc 0 1) :=
    LinearCauchy.continuousOn_mulVec (foldB_continuousOn hH lam) (foldW_continuousOn h)
  have hint : IntervalIntegrable (fun t => (foldA0 t + lam • foldA1 a t) *ᵥ foldW y y' t)
      volume 0 x := hcont.mono (by rw [uIcc_of_le hx.1]; exact Icc_subset_Icc le_rfl hx.2)
        |>.intervalIntegrable
  ext i
  rw [Pi.add_apply, integral_apply_pi hint]
  simp only [foldB_mulVec]
  have f0 := (ftc_Icc h.ac_y h.deriv_y IsSolution.zero_mem_Icc hxI).2
  have f0' := (ftc_Icc h.ac_y h.deriv_y hnxI IsSolution.zero_mem_Icc).2
  have f1 := (ftc_Icc h.ac_y' h.deriv_y' IsSolution.zero_mem_Icc hxI).2
  have f1' := (ftc_Icc h.ac_y' h.deriv_y' hnxI IsSolution.zero_mem_Icc)
  have hode : ∀ᵐ t : ℝ, t ∈ Ι 0 x → y'' t = lam * qfun a t * ((a t : ℂ) * y (-t) - y t) ∧
      y'' (-t) = lam * qfun a t * ((a (-t) : ℂ) * y t - y (-t)) := by
    filter_upwards [ode_ae hH h, ae_ne_one] with t ht hne htI
    rw [uIoc_of_le hx.1] at htI
    refine ht ⟨?_, ?_⟩
    · linarith [htI.1]
    · exact lt_of_le_of_ne (by linarith [htI.2, hx.2]) hne
  have e1 : ∫ t in (0 : ℝ)..x, -y' (-t) = y (-x) - y 0 := by
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_neg (fun s => y' s)]
    simp only [neg_zero]
    rw [f0']; ring
  have e2 : ∫ t in (0 : ℝ)..x, lam * qfun a t * ((a t : ℂ) * y (-t) - y t) = y' x - y' 0 := by
    rw [← f1]
    exact intervalIntegral.integral_congr_ae (by
      filter_upwards [hode] with t ht htI using (ht htI).1.symm)
  have e3 : ∫ t in (0 : ℝ)..x, lam * qfun a t * ((a (-t) : ℂ) * y t - y (-t)) =
      y' 0 - y' (-x) := by
    have c := intervalIntegral.integral_comp_neg (a := 0) (b := x) (fun s => y'' s)
    simp only [neg_zero] at c
    rw [← f1'.2, ← c]
    exact intervalIntegral.integral_congr_ae (by
      filter_upwards [hode] with t ht htI using (ht htI).2.symm)
  fin_cases i
  · change y x = y 0 + ∫ t in (0 : ℝ)..x, y' t
    rw [f0]; ring
  · change y (-x) = y (-0) + ∫ t in (0 : ℝ)..x, -y' (-t)
    rw [e1, neg_zero]; ring
  · change y' x = y' 0 + ∫ t in (0 : ℝ)..x, lam * qfun a t * ((a t : ℂ) * y (-t) - y t)
    rw [e2]; ring
  · change -y' (-x) = -y' (-0) + ∫ t in (0 : ℝ)..x, lam * qfun a t * ((a (-t) : ℂ) * y t - y (-t))
    rw [e3, neg_zero]; ring

theorem foldW_eq_phi {m κ : ℝ} (hH : HypH a m κ) (h : IsSolution a U lam y y' y'')
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    foldW y y' x = foldPhi a x lam *ᵥ foldW y y' 0 :=
  linearCauchy_unique continuousOn_const (foldA1_continuousOn ⟨m, κ, hH⟩) lam
    (foldW_continuousOn h) (fun _ hx => foldW_integral hH h hx) x hx

/-- Начальный вектор собственной функции лежит в ядре `V₀ + V₁ Φ(1, λ)`. -/
theorem foldMat_mulVec_foldW {m κ : ℝ} (hH : HypH a m κ) (h : IsSolution a U lam y y' y'') :
    foldMat a U lam *ᵥ foldW y y' 0 = 0 := by
  have h1 := foldW_eq_phi hH h (x := 1) ⟨by norm_num, le_rfl⟩
  have e : foldMat a U lam *ᵥ foldW y y' 0 =
      foldV0 *ᵥ foldW y y' 0 + foldV1 U *ᵥ foldW y y' 1 := by
    rw [h1, foldMat, Matrix.add_mulVec, Matrix.mulVec_mulVec]
  rw [e]
  have b0 := h.bc 0
  have b1 := h.bc 1
  simp only [Forms.eval] at b0 b1
  ext i
  fin_cases i <;>
    simp [foldV0, foldV1, foldW]
  · linear_combination b0
  · linear_combination b1
end GeneralBC
end Involution
