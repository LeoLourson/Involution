module

public import Involution.Estimates.ReflectionZeros
public import Involution.Setup.Rouche

/-! Нули `H(ρ) = cos ρL + γ cos ρd`: по одному простому нулю в каждом круге (теорема Руше). -/

@[expose] public noncomputable section

open Metric Set

namespace Involution

variable {L d r : ℝ} {γ : ℂ}

theorem reflCenter_sub (hL : 0 < L) (m n : ℤ) :
    reflCenter L m - reflCenter L n = Real.pi * ((m : ℝ) - n) / L := by
  unfold reflCenter; field_simp; ring

/-- Расстояние между разными центрами не меньше `π/L`. -/
theorem pi_div_le_center_dist (hL : 0 < L) {m n : ℤ} (h : m ≠ n) :
    Real.pi / L ≤ |reflCenter L m - reflCenter L n| := by
  rw [reflCenter_sub hL, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hL]
  have : (1 : ℝ) ≤ |(m : ℝ) - n| := by
    have : 1 ≤ |m - n| := Int.one_le_abs (sub_ne_zero.2 h)
    exact_mod_cast this
  exact div_le_div_of_nonneg_right (by nlinarith [Real.pi_pos]) hL.le

theorem cos_center_eq_zero (hL : 0 < L) (n : ℤ) :
    Complex.cos ((reflCenter L n : ℂ) * L) = 0 := by
  rw [Complex.cos_eq_zero_iff]
  refine ⟨n - 1, ?_⟩
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL.ne'
  unfold reflCenter
  push_cast
  field_simp
  ring

theorem cos_eq_zero_center (hL : 0 < L) {ρ : ℂ} (h : Complex.cos (ρ * L) = 0) :
    ∃ m : ℤ, ρ = reflCenter L m := by
  rw [Complex.cos_eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨k + 1, ?_⟩
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL.ne'
  unfold reflCenter
  push_cast
  field_simp
  linear_combination 2 * hk

theorem mem_ball_center_unique (hL : 0 < L) (hr : r ≤ Real.pi / (2 * L)) {m n : ℤ} {ρ : ℂ}
    (hm : ρ = reflCenter L m) (hn : ρ ∈ ball (reflCenter L n : ℂ) r) : m = n := by
  by_contra hne
  have h1 := pi_div_le_center_dist hL hne
  rw [mem_ball, hm, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at hn
  have : Real.pi / L = 2 * (Real.pi / (2 * L)) := by field_simp
  have : 0 < Real.pi / (2 * L) := by positivity
  linarith

theorem sphere_out (hL : 0 < L) (hr : r ≤ Real.pi / (2 * L)) {n : ℤ} {ρ : ℂ}
    (hρ : ρ ∈ sphere (reflCenter L n : ℂ) r) (m : ℤ) : r ≤ ‖ρ - (reflCenter L m : ℂ)‖ := by
  rw [mem_sphere, dist_eq_norm] at hρ
  by_cases hmn : m = n
  · subst hmn; exact hρ.ge
  · have h1 := pi_div_le_center_dist hL (Ne.symm hmn)
    have h2 : ‖(reflCenter L n : ℂ) - reflCenter L m‖ ≤ ‖ρ - (reflCenter L m : ℂ)‖ + r := by
      calc _ = ‖(ρ - (reflCenter L m : ℂ)) - (ρ - (reflCenter L n : ℂ))‖ := by ring_nf
        _ ≤ ‖ρ - (reflCenter L m : ℂ)‖ + ‖ρ - (reflCenter L n : ℂ)‖ := norm_sub_le _ _
        _ = _ := by rw [hρ]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h2
    have : Real.pi / L = 2 * (Real.pi / (2 * L)) := by field_simp
    linarith

theorem order_cos_center (hL : 0 < L) (n : ℤ) :
    analyticOrderAt (fun ρ : ℂ => Complex.cos (ρ * L)) (reflCenter L n : ℂ) = 1 := by
  have hz := cos_center_eq_zero hL n
  have han : AnalyticAt ℂ (fun ρ : ℂ => Complex.cos (ρ * L)) (reflCenter L n : ℂ) := by
    fun_prop
  refine han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz ?_
  have hd : HasDerivAt (fun ρ : ℂ => Complex.cos (ρ * L))
      (-Complex.sin ((reflCenter L n : ℂ) * L) * (L : ℂ)) (reflCenter L n : ℂ) := by
    have := ((hasDerivAt_id (reflCenter L n : ℂ)).mul_const (L : ℂ)).ccos
    simpa using this
  rw [hd.deriv]
  have hs : Complex.sin ((reflCenter L n : ℂ) * L) ≠ 0 := by
    intro h
    have := Complex.sin_sq_add_cos_sq ((reflCenter L n : ℂ) * L)
    rw [h, hz] at this; norm_num at this
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL.ne'
  simp [hs, hL']

/-- (ii): в каждом круге `ball (π(n-1/2)/L, r)` ровно один нуль `H`, и он простой. -/
theorem reflH_ball_unique_simple (hL : 0 < L) (hd : |d| ≤ L) (hr0 : 0 < r)
    (hr : r ≤ Real.pi / (2 * L)) (hγ : ‖γ‖ * Real.cosh (|d| * r) < Real.sin (L * r)) (n : ℤ) :
    ∃ w ∈ ball (reflCenter L n : ℂ) r, reflH L d γ w = 0 ∧
      analyticOrderAt (reflH L d γ) w = 1 ∧
      ∀ z ∈ ball (reflCenter L n : ℂ) r, reflH L d γ z = 0 → z = w := by
  have hfg : ∀ z ∈ sphere (reflCenter L n : ℂ) r,
      ‖(fun ρ : ℂ => γ * Complex.cos (ρ * d)) z‖ < ‖(fun ρ : ℂ => Complex.cos (ρ * L)) z‖ :=
    fun z hz => norm_mul_cos_lt hL hd hr0 hr hγ (sphere_out hL hr hz)
  have := rouche_simple (f := fun ρ : ℂ => Complex.cos (ρ * L))
    (g := fun ρ : ℂ => γ * Complex.cos (ρ * d)) (c := (reflCenter L n : ℂ)) (r := r)
    isOpen_univ (subset_univ _) hr0 (by fun_prop) (by fun_prop) hfg
    (z₀ := (reflCenter L n : ℂ)) (mem_ball_self hr0) (cos_center_eq_zero hL n)
    (order_cos_center hL n) (by
      intro z hz h0
      obtain ⟨m, hm⟩ := cos_eq_zero_center hL h0
      have := mem_ball_center_unique hL hr hm hz
      subst this; exact hm)
  exact this

/-- (i): каждый нуль `H` лежит в одном из открытых кругов. -/
theorem reflH_zero_mem_ball (hL : 0 < L) (hd : |d| ≤ L) (hr0 : 0 < r)
    (hr : r ≤ Real.pi / (2 * L)) (hγ : ‖γ‖ * Real.cosh (|d| * r) < Real.sin (L * r)) {ρ : ℂ}
    (h : reflH L d γ ρ = 0) : ∃ n : ℤ, ρ ∈ ball (reflCenter L n : ℂ) r := by
  by_contra hne
  push Not at hne
  have hout : ∀ n : ℤ, r ≤ ‖ρ - (reflCenter L n : ℂ)‖ := fun n => by
    have := hne n
    rwa [mem_ball, dist_eq_norm, not_lt] at this
  have hlt := norm_mul_cos_lt hL hd hr0 hr hγ hout
  have : Complex.cos (ρ * L) = -(γ * Complex.cos (ρ * d)) := eq_neg_of_add_eq_zero_left h
  rw [this, norm_neg] at hlt
  exact lt_irrefl _ hlt

end Involution
