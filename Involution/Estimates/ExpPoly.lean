module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! Экспоненциальный многочлен `F` линии G:
`F(ρ) = θ₊ e^{iρL} + θ₋ e^{-iρL} + θ_d⁺ e^{iρd} + θ_d⁻ e^{-iρd}`, `L > 0`, `|d| < L`.
Здесь определение, оценка сверху `|F| ≤ C e^{L|Im ρ|}` и лемма статьи `lem:F` (a):
оценка снизу вне горизонтальной полосы. Гипотеза `‖θ₋‖ = ‖θ₊‖` (в статье `θ₋ = ±θ₊`)
нужна в (a): при `Im ρ ≥ h₀` главным служит слагаемое с `θ₋`, при `Im ρ ≤ -h₀` — с `θ₊`. -/

@[expose] public noncomputable section

open Complex Real Filter Topology

namespace Involution

/-- Экспоненциальный многочлен `F` из леммы `lem:F`. -/
def expPoly (θp θm θdp θdm : ℂ) (L d : ℝ) (ρ : ℂ) : ℂ :=
  θp * cexp (I * ρ * L) + θm * cexp (-(I * ρ * L)) +
    θdp * cexp (I * ρ * d) + θdm * cexp (-(I * ρ * d))

theorem norm_cexp_I_mul (ρ : ℂ) (c : ℝ) : ‖cexp (I * ρ * c)‖ = Real.exp (-(c * ρ.im)) := by
  rw [Complex.norm_exp]; congr 1; simp; ring

theorem norm_cexp_neg_I_mul (ρ : ℂ) (c : ℝ) : ‖cexp (-(I * ρ * c))‖ = Real.exp (c * ρ.im) := by
  rw [Complex.norm_exp]; congr 1; simp; ring

theorem expPoly_analytic (θp θm θdp θdm : ℂ) (L d : ℝ) :
    AnalyticOnNhd ℂ (expPoly θp θm θdp θdm L d) Set.univ := by
  intro z _
  unfold expPoly
  fun_prop

theorem expPoly_differentiable (θp θm θdp θdm : ℂ) (L d : ℝ) :
    Differentiable ℂ (expPoly θp θm θdp θdm L d) := by
  unfold expPoly; fun_prop

theorem norm_expPoly_le {θp θm θdp θdm : ℂ} {L d : ℝ} (hd : |d| ≤ L) (ρ : ℂ) :
    ‖expPoly θp θm θdp θdm L d ρ‖ ≤
      (‖θp‖ + ‖θm‖ + ‖θdp‖ + ‖θdm‖) * Real.exp (L * |ρ.im|) := by
  have h1 : ∀ c : ℝ, |c| ≤ L → Real.exp (c * ρ.im) ≤ Real.exp (L * |ρ.im|) := by
    intro c hc
    apply Real.exp_le_exp.2
    calc c * ρ.im ≤ |c * ρ.im| := le_abs_self _
      _ = |c| * |ρ.im| := abs_mul _ _
      _ ≤ L * |ρ.im| := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
  have h2 : ∀ c : ℝ, |c| ≤ L → Real.exp (-(c * ρ.im)) ≤ Real.exp (L * |ρ.im|) := by
    intro c hc
    have := h1 (-c) (by simpa using hc)
    simpa using this
  have hL : |L| ≤ L := by
    have : 0 ≤ L := (abs_nonneg d).trans hd
    rw [abs_of_nonneg this]
  have t1 : ‖θp * cexp (I * ρ * L)‖ ≤ ‖θp‖ * Real.exp (L * |ρ.im|) := by
    rw [norm_mul, norm_cexp_I_mul]
    exact mul_le_mul_of_nonneg_left (h2 L hL) (norm_nonneg _)
  have t2 : ‖θm * cexp (-(I * ρ * L))‖ ≤ ‖θm‖ * Real.exp (L * |ρ.im|) := by
    rw [norm_mul, norm_cexp_neg_I_mul]
    exact mul_le_mul_of_nonneg_left (h1 L hL) (norm_nonneg _)
  have t3 : ‖θdp * cexp (I * ρ * d)‖ ≤ ‖θdp‖ * Real.exp (L * |ρ.im|) := by
    rw [norm_mul, norm_cexp_I_mul]
    exact mul_le_mul_of_nonneg_left (h2 d hd) (norm_nonneg _)
  have t4 : ‖θdm * cexp (-(I * ρ * d))‖ ≤ ‖θdm‖ * Real.exp (L * |ρ.im|) := by
    rw [norm_mul, norm_cexp_neg_I_mul]
    exact mul_le_mul_of_nonneg_left (h1 d hd) (norm_nonneg _)
  unfold expPoly
  have n1 := norm_add_le (θp * cexp (I * ρ * L) + θm * cexp (-(I * ρ * L)) +
    θdp * cexp (I * ρ * d)) (θdm * cexp (-(I * ρ * d)))
  have n2 := norm_add_le (θp * cexp (I * ρ * L) + θm * cexp (-(I * ρ * L)))
    (θdp * cexp (I * ρ * d))
  have n3 := norm_add_le (θp * cexp (I * ρ * L)) (θm * cexp (-(I * ρ * L)))
  nlinarith

/-- Остаточная функция `g(y) = |θ₊| e^{-2Ly} + (|θ_d⁺|+|θ_d⁻|) e^{-(L-|d|)y}` убывает. -/
theorem expPoly_tail_antitone {L d : ℝ} (hL : 0 < L) (hd : |d| < L) (a S : ℝ)
    (ha : 0 ≤ a) (hS : 0 ≤ S) :
    Antitone (fun y : ℝ => a * Real.exp (-2 * L * y) + S * Real.exp (-(L - |d|) * y)) := by
  intro y z hyz
  have h1 : Real.exp (-2 * L * z) ≤ Real.exp (-2 * L * y) :=
    Real.exp_le_exp.2 (by nlinarith)
  have h2 : Real.exp (-(L - |d|) * z) ≤ Real.exp (-(L - |d|) * y) :=
    Real.exp_le_exp.2 (by nlinarith)
  simp only
  gcongr

theorem expPoly_tail_tendsto {L d : ℝ} (hL : 0 < L) (hd : |d| < L) (a S : ℝ) :
    Tendsto (fun y : ℝ => a * Real.exp (-2 * L * y) + S * Real.exp (-(L - |d|) * y))
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => Real.exp (-2 * L * y)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_id.const_mul_atTop_of_neg (by linarith)
  have h2 : Tendsto (fun y : ℝ => Real.exp (-(L - |d|) * y)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_id.const_mul_atTop_of_neg (by linarith)
  simpa using (h1.const_mul a).add (h2.const_mul S)

theorem exp_mul_tail (L d y : ℝ) (a S : ℝ) :
    Real.exp (L * y) * (a * Real.exp (-2 * L * y) + S * Real.exp (-(L - |d|) * y)) =
      a * Real.exp (-(L * y)) + S * Real.exp (|d| * y) := by
  rw [mul_add, mul_left_comm, ← Real.exp_add, mul_left_comm, ← Real.exp_add]
  congr 3 <;> ring

/-- Лемма `lem:F` (a): при `|Im ρ| ≥ h₀` выполнено `|F(ρ)| ≥ ½|θ₊| e^{L|Im ρ|}`. -/
theorem expPoly_lower_outside {θp θm θdp θdm : ℂ} {L d : ℝ} (hL : 0 < L) (hd : |d| < L)
    (hp : θp ≠ 0) (hm : ‖θm‖ = ‖θp‖) :
    ∃ h₀ : ℝ, 1 ≤ h₀ ∧ ∀ ρ : ℂ, h₀ ≤ |ρ.im| →
      (1 / 2) * ‖θp‖ * Real.exp (L * |ρ.im|) ≤ ‖expPoly θp θm θdp θdm L d ρ‖ := by
  set S := ‖θdp‖ + ‖θdm‖ with hS
  have hpos : 0 < ‖θp‖ := norm_pos_iff.2 hp
  have hev := (expPoly_tail_tendsto hL hd ‖θp‖ S).eventually
    (Iic_mem_nhds (show (0 : ℝ) < (1 / 2) * ‖θp‖ by positivity))
  obtain ⟨h₀, hh⟩ := (hev.and (eventually_ge_atTop 1)).exists
  have hg := expPoly_tail_antitone hL hd ‖θp‖ S hpos.le (by positivity)
  have key : ∀ y : ℝ, h₀ ≤ y → Real.exp (L * y) * (‖θp‖ * Real.exp (-2 * L * y) +
      S * Real.exp (-(L - |d|) * y)) ≤ Real.exp (L * y) * ((1 / 2) * ‖θp‖) := fun y hy =>
    mul_le_mul_of_nonneg_left ((hg hy).trans hh.1) (Real.exp_pos _).le
  refine ⟨h₀, hh.2, fun ρ hρ => ?_⟩
  have ed : ∀ y : ℝ, 0 ≤ y → Real.exp (d * y) ≤ Real.exp (|d| * y) ∧
      Real.exp (-(d * y)) ≤ Real.exp (|d| * y) := fun y hy =>
    ⟨Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_abs_self d) hy),
     Real.exp_le_exp.2 (by nlinarith [neg_abs_le d])⟩
  have hy1 : 0 < |ρ.im| := lt_of_lt_of_le (by linarith [hh.2]) hρ
  have K := key _ hρ
  rw [exp_mul_tail] at K
  have aux : ∀ (A R : ℂ) (m r : ℝ), expPoly θp θm θdp θdm L d ρ = A + R → ‖A‖ = m →
      ‖R‖ ≤ r → m - r ≤ ‖expPoly θp θm θdp θdm L d ρ‖ := by
    intro A R m r hF hA hR
    have := norm_sub_norm_le A (-R)
    rw [sub_neg_eq_add, norm_neg] at this
    rw [hF]; linarith
  have n3 : ∀ x y z : ℂ, ‖x + y + z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ := fun x y z => norm_add₃_le
  rcases le_total 0 ρ.im with hi | hi
  · rw [abs_of_nonneg hi] at hy1 K ⊢
    have := ed ρ.im hi
    have e3 : ‖θdp‖ * Real.exp (-(d * ρ.im)) ≤ ‖θdp‖ * Real.exp (|d| * ρ.im) :=
      mul_le_mul_of_nonneg_left this.2 (norm_nonneg _)
    have e4 : ‖θdm‖ * Real.exp (d * ρ.im) ≤ ‖θdm‖ * Real.exp (|d| * ρ.im) :=
      mul_le_mul_of_nonneg_left this.1 (norm_nonneg _)
    have := aux (θm * cexp (-(I * ρ * L)))
      (θp * cexp (I * ρ * L) + θdp * cexp (I * ρ * d) + θdm * cexp (-(I * ρ * d)))
      (‖θp‖ * Real.exp (L * ρ.im)) (‖θp‖ * Real.exp (-(L * ρ.im)) + S * Real.exp (|d| * ρ.im))
      (by unfold expPoly; ring)
      (by rw [norm_mul, norm_cexp_neg_I_mul, hm])
      ((n3 _ _ _).trans (by
        rw [norm_mul, norm_mul, norm_mul, norm_cexp_I_mul, norm_cexp_I_mul,
          norm_cexp_neg_I_mul]
        rw [hS]; nlinarith))
    nlinarith
  · rw [abs_of_nonpos hi] at hy1 K ⊢
    have := ed (-ρ.im) (by linarith)
    have e3 : ‖θdp‖ * Real.exp (-(d * ρ.im)) ≤ ‖θdp‖ * Real.exp (|d| * -ρ.im) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa using this.1
    have e4 : ‖θdm‖ * Real.exp (d * ρ.im) ≤ ‖θdm‖ * Real.exp (|d| * -ρ.im) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa using this.2
    have := aux (θp * cexp (I * ρ * L))
      (θm * cexp (-(I * ρ * L)) + θdp * cexp (I * ρ * d) + θdm * cexp (-(I * ρ * d)))
      (‖θp‖ * Real.exp (L * -ρ.im)) (‖θp‖ * Real.exp (-(L * -ρ.im)) + S * Real.exp (|d| * -ρ.im))
      (by unfold expPoly; ring)
      (by rw [norm_mul, norm_cexp_I_mul]; congr 2; ring)
      ((n3 _ _ _).trans (by
        rw [norm_mul, norm_mul, norm_mul, norm_cexp_neg_I_mul, norm_cexp_I_mul,
          norm_cexp_neg_I_mul, hm]
        rw [hS]
        have : Real.exp (L * ρ.im) = Real.exp (-(L * -ρ.im)) := by congr 1; ring
        rw [this]
        nlinarith))
    nlinarith

/-- Нули `F` лежат в полосе `|Im ρ| < h₀`, если выполнена оценка (a). -/
theorem expPoly_zero_im_lt {θp θm θdp θdm : ℂ} {L d h₀ : ℝ} (hp : θp ≠ 0)
    (h : ∀ ρ : ℂ, h₀ ≤ |ρ.im| →
      (1 / 2) * ‖θp‖ * Real.exp (L * |ρ.im|) ≤ ‖expPoly θp θm θdp θdm L d ρ‖)
    {ρ : ℂ} (hρ : expPoly θp θm θdp θdm L d ρ = 0) : |ρ.im| < h₀ := by
  by_contra hc
  have := h ρ (not_lt.1 hc)
  rw [hρ, norm_zero] at this
  have hpos : 0 < ‖θp‖ := norm_pos_iff.2 hp
  have := Real.exp_pos (L * |ρ.im|)
  nlinarith

end Involution
