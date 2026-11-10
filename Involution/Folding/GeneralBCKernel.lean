module

public import Involution.Folding.GeneralBCSystem
public import Involution.Folding.GeneralBCLeading
public import Involution.Folding.GeneralBCAdmissible

/-! # Ядро главной части: числовые факты при (H) (C24 шаги 7–8, лемма `lem:kernel`)

Положительность `σ_s`, `τ_s`, ненулевость `ϰ`, `τ⁰_s`, значения `D(0) = 1`, `t(0) = 0`, `k(0) = ε`,
а также значения `ε² = 1`. Нормировка `D(0) = 1` записи C24. -/

@[expose] public noncomputable section

open Set

namespace Involution
namespace GeneralBC

theorem eps_sq (a : ℝ → ℝ) : eps a * eps a = 1 := by
  unfold eps; split_ifs <;> norm_num

theorem a_zero_ne {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) : a 0 ≠ 0 := fun h0 => by
  have := h.lower 0 (by simp)
  rw [h0] at this; simp at this; linarith [h.m_pos]

/-- `σ_s(x) > 0` в точках, где `a(x)a(-x) > 0` (при (H): `x = 0`, `x = 1`). -/
theorem sigma_pos {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1)
    (s : ℝ) (hs : s = 1 ∨ s = -1) : 0 < sigma a s x := by
  have hq : Real.sqrt (a x * a (-x)) < 1 := by
    rw [Real.sqrt_lt' one_pos]; nlinarith [h.upper x hx, h.kappa_lt]
  have hq0 := Real.sqrt_nonneg (a x * a (-x))
  unfold sigma
  rcases hs with rfl | rfl <;> linarith

theorem tau_pos {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1)
    (s : ℝ) (hs : s = 1 ∨ s = -1) : 0 < tau a s x := by
  unfold tau
  exact inv_pos.2 (Real.sqrt_pos.2 (sigma_pos h hx s hs))

theorem tau0_pos {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    0 < tau0 a s := tau_pos h (by simp) s hs

theorem omega_pos {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    0 < omega a s := tau_pos h (by simp) s hs

theorem kfun_zero {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) : kfun a 0 = eps a := by
  have := a_zero_ne h
  simp [kfun, this]

theorem varkappa_ne_zero {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) : varkappa a ≠ 0 := by
  have hp := h.prod_pos
  have h1 : a 1 ≠ 0 := fun h0 => by simp [h0] at hp
  have hr : 0 < a (-1) / a 1 := by
    have : a (-1) / a 1 = (a 1 * a (-1)) / (a 1) ^ 2 := by field_simp
    rw [this]; exact div_pos hp (by positivity)
  unfold varkappa kfun
  have := eps_sq a
  intro h0
  have h2 : eps a ≠ 0 := fun h' => by rw [h'] at this; simp at this
  rcases mul_eq_zero.1 h0 with h3 | h3
  · exact h2 h3
  · exact (Real.sqrt_pos.2 hr).ne' h3

theorem tPhase_zero (a : ℝ → ℝ) (s : ℝ) : tPhase a s 0 = 0 := by
  simp [tPhase]

theorem Damp_zero {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    Damp a s 0 = 1 := by
  have h0 := (tau0_pos h s hs).ne'
  have hk : |kfun a 0| = 1 := by
    rw [kfun_zero h]; unfold eps; split_ifs <;> simp
  unfold Damp
  rw [hk]
  have : tau0 a s / (1 * tau a s 0) = 1 := by
    have : tau a s 0 = tau0 a s := rfl
    rw [this]; field_simp
  rw [this]; simp

theorem Damp_pos {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    0 < Damp a s 1 := by
  have hk : 0 < |kfun a 1| := abs_pos.2 (varkappa_ne_zero h)
  unfold Damp
  apply Real.sqrt_pos.2
  exact div_pos (tau0_pos h s hs) (mul_pos hk (tau_pos h (by simp) s hs))

end GeneralBC
end Involution

