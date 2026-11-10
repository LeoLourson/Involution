module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Оценки для нулей `cos ρL + γ cos ρd`: модуль комплексного косинуса и сравнение
`|γ cos ρd| < |cos ρL|` вне кругов радиуса `r` вокруг точек `π(n - 1/2)/L`. -/

@[expose] public noncomputable section

open Metric Set

namespace Involution

/-- Центры кругов: `π(n - 1/2)/L`, нули `cos ρL`. -/
def reflCenter (L : ℝ) (n : ℤ) : ℝ := Real.pi * ((n : ℝ) - 1 / 2) / L

/-- `‖cos w‖² = cos²(Re w) + sinh²(Im w)`. -/
theorem norm_cos_sq (w : ℂ) :
    ‖Complex.cos w‖ ^ 2 = Real.cos w.re ^ 2 + Real.sinh w.im ^ 2 := by
  have h : Complex.cos w = ((Real.cos w.re * Real.cosh w.im : ℝ) : ℂ)
      - ((Real.sin w.re * Real.sinh w.im : ℝ) : ℂ) * Complex.I := by
    conv_lhs => rw [← Complex.re_add_im w]
    rw [Complex.cos_add_mul_I]
    push_cast
    ring
  rw [Complex.sq_norm, h, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  nlinarith [Real.cosh_sq w.im, Real.sin_sq_add_cos_sq w.re]

theorem norm_cos_le_cosh (w : ℂ) : ‖Complex.cos w‖ ≤ Real.cosh w.im := by
  refine (sq_le_sq₀ (norm_nonneg _) (Real.cosh_pos _).le).1 ?_
  rw [norm_cos_sq, Real.cosh_sq]; nlinarith [Real.cos_sq_le_one w.re]

theorem sinh_le_norm_cos (w : ℂ) : Real.sinh |w.im| ≤ ‖Complex.cos w‖ := by
  have h0 : 0 ≤ Real.sinh |w.im| := Real.sinh_nonneg_iff.2 (abs_nonneg _)
  refine (sq_le_sq₀ h0 (norm_nonneg _)).1 ?_
  rw [norm_cos_sq]
  have : Real.sinh |w.im| ^ 2 = Real.sinh w.im ^ 2 := by
    rcases abs_choice w.im with h | h <;> rw [h]; simp
  rw [this]; nlinarith [sq_nonneg (Real.cos w.re)]

/-- Вещественное неравенство: `sin² s ≤ sin² u₁ + sinh² u₂` при `|u₁| ≤ π/2`,
`s ≤ π/2`, `s² ≤ u₁² + u₂²`. -/
theorem sin_sq_le_aux {u₁ u₂ s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ Real.pi / 2)
    (hu : |u₁| ≤ Real.pi / 2) (h : s ^ 2 ≤ u₁ ^ 2 + u₂ ^ 2) :
    Real.sin s ^ 2 ≤ Real.sin u₁ ^ 2 + Real.sinh u₂ ^ 2 := by
  have hsh : u₂ ^ 2 ≤ Real.sinh u₂ ^ 2 := by
    rw [← sq_abs u₂, ← sq_abs (Real.sinh u₂)]
    have : |u₂| ≤ |Real.sinh u₂| := by
      rcases le_total 0 u₂ with h0 | h0
      · rw [abs_of_nonneg h0, abs_of_nonneg (Real.sinh_nonneg_iff.2 h0)]
        exact Real.self_le_sinh_iff.2 h0
      · rw [abs_of_nonpos h0, abs_of_nonpos (Real.sinh_nonpos_iff.2 h0)]
        have := Real.sinh_le_self_iff.2 h0; linarith
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  set t := |u₁| with ht
  have hsin : Real.sin u₁ ^ 2 = Real.sin t ^ 2 := by
    rcases abs_choice u₁ with h1 | h1
    · rw [ht, h1]
    · rw [ht, h1, Real.sin_neg]; ring
  have ht0 : 0 ≤ t := abs_nonneg _
  have hu2 : u₁ ^ 2 = t ^ 2 := (sq_abs u₁).symm
  rw [hsin]
  rcases le_total s t with hst | hts
  · have := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hu hst
    have h0 : 0 ≤ Real.sin s := Real.sin_nonneg_of_nonneg_of_le_pi hs0 (by linarith [Real.pi_pos])
    nlinarith [sq_nonneg (Real.sinh u₂)]
  · -- sin²s - sin²t = sin(s+t) sin(s-t) ≤ s² - t²
    have key : Real.sin s ^ 2 - Real.sin t ^ 2 = Real.sin (s + t) * Real.sin (s - t) := by
      rw [Real.sin_add, Real.sin_sub]
      nlinarith [Real.sin_sq_add_cos_sq s, Real.sin_sq_add_cos_sq t]
    have h1 : Real.sin (s - t) ≤ s - t := Real.sin_le (by linarith)
    have h2 : 0 ≤ Real.sin (s - t) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
    have h3 : Real.sin (s + t) ≤ s + t := Real.sin_le (by linarith)
    have h4 : Real.sin (s + t) * Real.sin (s - t) ≤ (s + t) * (s - t) := by
      rcases le_total 0 (Real.sin (s + t)) with h5 | h5
      · exact mul_le_mul h3 h1 h2 (by linarith)
      · nlinarith
    nlinarith

/-- Вне кругов при `|Im ρ| ≤ r`: `sin(Lr) ≤ ‖cos ρL‖`. -/
theorem sin_le_norm_cos {L r : ℝ} (hL : 0 < L) (hr0 : 0 ≤ r) (hr : r ≤ Real.pi / (2 * L))
    {ρ : ℂ} (hout : ∀ n : ℤ, r ≤ ‖ρ - (reflCenter L n : ℂ)‖) :
    Real.sin (L * r) ≤ ‖Complex.cos (ρ * L)‖ := by
  set x := ρ.re
  set y := ρ.im
  have hLr : L * r ≤ Real.pi / 2 := by
    calc L * r ≤ L * (Real.pi / (2 * L)) := by gcongr
      _ = Real.pi / 2 := by field_simp
  set n : ℤ := ⌈L * x / Real.pi⌉ with hn
  have hn1 := Int.ceil_lt_add_one (L * x / Real.pi)
  have hn2 := Int.le_ceil (L * x / Real.pi)
  rw [← hn] at hn1 hn2
  have hpi := Real.pi_pos
  set u₁ := L * x - Real.pi * ((n : ℝ) - 1 / 2) with hu₁
  have hb1 : L * x ≤ Real.pi * n := by
    have := mul_le_mul_of_nonneg_left hn2 hpi.le
    rwa [mul_div_cancel₀ _ hpi.ne'] at this
  have hb2 : Real.pi * ((n : ℝ) - 1) < L * x := by
    have := mul_lt_mul_of_pos_left hn1 hpi
    have e : Real.pi * (L * x / Real.pi + 1) = L * x + Real.pi := by field_simp
    rw [e] at this; linarith
  have hu : |u₁| ≤ Real.pi / 2 := by
    rw [abs_le]; constructor <;> nlinarith
  have hcos : Real.cos (L * x) ^ 2 = Real.sin u₁ ^ 2 := by
    have : L * x = (u₁ - Real.pi / 2) + (n : ℝ) * Real.pi := by rw [hu₁]; ring
    rw [this, Real.cos_add_int_mul_pi, Real.cos_sub_pi_div_two, mul_pow]
    rcases Int.even_or_odd n with h | h
    · simp [h.neg_one_zpow]
    · simp [h.neg_one_zpow]
  have hnorm : ‖ρ - (reflCenter L n : ℂ)‖ ^ 2 = (u₁ / L) ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
    have : x - reflCenter L n = u₁ / L := by
      unfold reflCenter; rw [hu₁]; field_simp
    rw [show ρ.re = x from rfl, show ρ.im = y from rfl, this]; ring
  have hd := hout n
  have hsq : (L * r) ^ 2 ≤ u₁ ^ 2 + (L * y) ^ 2 := by
    have h1 : r ^ 2 ≤ ‖ρ - (reflCenter L n : ℂ)‖ ^ 2 := pow_le_pow_left₀ hr0 hd 2
    rw [hnorm] at h1
    have : (L * r) ^ 2 ≤ L ^ 2 * ((u₁ / L) ^ 2 + y ^ 2) := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left h1 (sq_nonneg L)
    have e : L ^ 2 * ((u₁ / L) ^ 2 + y ^ 2) = u₁ ^ 2 + (L * y) ^ 2 := by
      field_simp
    linarith
  have hre : (ρ * L).re = L * x := by simp [x, mul_comm]
  have him : (ρ * L).im = L * y := by simp [y, mul_comm]
  have key := sin_sq_le_aux (mul_nonneg hL.le hr0) hLr hu hsq
  have hsq2 : Real.sin (L * r) ^ 2 ≤ ‖Complex.cos (ρ * L)‖ ^ 2 := by
    rw [norm_cos_sq, hre, him, hcos]; exact key
  have hs0 : 0 ≤ Real.sin (L * r) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg hL.le hr0) (by linarith [Real.pi_pos])
  exact (sq_le_sq₀ hs0 (norm_nonneg _)).1 hsq2

end Involution
