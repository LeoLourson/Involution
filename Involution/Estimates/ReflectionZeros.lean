module

public import Involution.Estimates.ReflectionZerosTrig

/-! Сравнение `|γ cos ρd| < |cos ρL|` вне кругов радиуса `r` вокруг точек `π(n - 1/2)/L`
(предложение `prop:10` статьи, оценочная часть). -/

@[expose] public noncomputable section

open Metric Set

namespace Involution

/-- `H(ρ) = cos ρL + γ cos ρd`. -/
def reflH (L d : ℝ) (γ ρ : ℂ) : ℂ := Complex.cos (ρ * L) + γ * Complex.cos (ρ * d)

/-- Монотонность отношения `sinh(at)/cosh(bt)` при `b ≤ a`. -/
theorem sinh_mul_cosh_le {a b s t : ℝ} (hb : b ≤ a) (hb0 : 0 ≤ b) (hs : s ≤ t) :
    Real.sinh (a * s) * Real.cosh (b * t) ≤ Real.sinh (a * t) * Real.cosh (b * s) := by
  have e1 : ∀ A B : ℝ, 2 * (Real.sinh A * Real.cosh B) = Real.sinh (A + B) + Real.sinh (A - B) := by
    intro A B; simp only [Real.sinh_add, Real.sinh_sub]; ring
  have h1 : Real.sinh (a * s + b * t) ≤ Real.sinh (a * t + b * s) :=
    Real.sinh_le_sinh.2 (by nlinarith)
  have h2 : Real.sinh (a * s - b * t) ≤ Real.sinh (a * t - b * s) :=
    Real.sinh_le_sinh.2 (by nlinarith)
  have := e1 (a * s) (b * t)
  have := e1 (a * t) (b * s)
  linarith

theorem norm_mul_cos_lt {L d r : ℝ} {γ : ℂ} (hL : 0 < L) (hd : |d| ≤ L) (hr0 : 0 < r)
    (hr : r ≤ Real.pi / (2 * L)) (hγ : ‖γ‖ * Real.cosh (|d| * r) < Real.sin (L * r))
    {ρ : ℂ} (hout : ∀ n : ℤ, r ≤ ‖ρ - (reflCenter L n : ℂ)‖) :
    ‖γ * Complex.cos (ρ * d)‖ < ‖Complex.cos (ρ * L)‖ := by
  rw [norm_mul]
  have him : ∀ c : ℝ, (ρ * c).im = c * ρ.im := fun c => by simp [mul_comm]
  have hcd : ‖Complex.cos (ρ * d)‖ ≤ Real.cosh (d * ρ.im) := by
    have := norm_cos_le_cosh (ρ * d); rwa [him] at this
  have hg0 : 0 ≤ ‖γ‖ := norm_nonneg _
  by_cases hy : |ρ.im| ≤ r
  · have h1 : Real.cosh (d * ρ.im) ≤ Real.cosh (|d| * r) := by
      rw [Real.cosh_le_cosh, abs_mul, abs_of_nonneg (by positivity : 0 ≤ |d| * r)]
      exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)
    calc ‖γ‖ * ‖Complex.cos (ρ * d)‖ ≤ ‖γ‖ * Real.cosh (|d| * r) :=
          mul_le_mul_of_nonneg_left (hcd.trans h1) hg0
      _ < Real.sin (L * r) := hγ
      _ ≤ _ := sin_le_norm_cos hL hr0.le hr hout
  · rw [not_le] at hy
    set t := |ρ.im| with ht
    have hcosh : Real.cosh (d * ρ.im) = Real.cosh (|d| * t) := by
      rw [← Real.cosh_abs (d * ρ.im), abs_mul]
    have hmono := sinh_mul_cosh_le (a := L) (b := |d|) hd (abs_nonneg d) hy.le
    have hsin : Real.sin (L * r) ≤ Real.sinh (L * r) := by
      have := Real.sin_le (mul_nonneg hL.le hr0.le)
      have := Real.self_le_sinh_iff.2 (mul_nonneg hL.le hr0.le)
      linarith
    have hc1 : 0 < Real.cosh (|d| * r) := Real.cosh_pos _
    have hlow : Real.sinh (L * t) ≤ ‖Complex.cos (ρ * L)‖ := by
      have := sinh_le_norm_cos (ρ * L)
      rwa [him, abs_mul, abs_of_pos hL] at this
    have : ‖γ‖ * Real.cosh (|d| * t) < Real.sinh (L * t) := by
      have h3 : ‖γ‖ * Real.cosh (|d| * r) * Real.cosh (|d| * t)
          < Real.sinh (L * r) * Real.cosh (|d| * t) :=
        mul_lt_mul_of_pos_right (hγ.trans_le hsin) (Real.cosh_pos _)
      have h4 : ‖γ‖ * Real.cosh (|d| * t) * Real.cosh (|d| * r)
          < Real.sinh (L * t) * Real.cosh (|d| * r) := by nlinarith
      exact lt_of_mul_lt_mul_right h4 hc1.le
    calc ‖γ‖ * ‖Complex.cos (ρ * d)‖ ≤ ‖γ‖ * Real.cosh (d * ρ.im) :=
          mul_le_mul_of_nonneg_left hcd hg0
      _ = ‖γ‖ * Real.cosh (|d| * t) := by rw [hcosh]
      _ < _ := this.trans_le hlow

end Involution
