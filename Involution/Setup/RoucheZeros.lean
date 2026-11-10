module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.CauchyIntegral

/-! Нули голоморфной функции в круге: конечность и кратности. -/

@[expose] public noncomputable section

open Metric Set Filter Topology

namespace Involution

/-- Кратность нуля `f` в точке `z` как натуральное число (`analyticOrderNatAt`). -/
abbrev zeroMult (f : ℂ → ℂ) (z : ℂ) : ℕ := analyticOrderNatAt f z

/-- Голоморфная в круге функция, не равная нулю в одной точке, имеет конечный порядок везде. -/
theorem analyticOrderAt_ne_top_of_ball {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hd : DifferentiableOn ℂ f (ball c R)) {z₀ : ℂ} (hz₀ : z₀ ∈ ball c R) (hf : f z₀ ≠ 0)
    {z : ℂ} (hz : z ∈ ball c R) : analyticOrderAt f z ≠ ⊤ := by
  have han : AnalyticOnNhd ℂ f (ball c R) := hd.analyticOnNhd isOpen_ball
  refine han.analyticOrderAt_ne_top_of_isPreconnected (convex_ball c R).isPreconnected hz₀ hz ?_
  rw [(han z₀ hz₀).analyticOrderAt_eq_zero.2 hf]
  simp

/-- Нули голоморфной в круге функции в меньшем замкнутом круге образуют конечное множество. -/
theorem zeros_finite {f : ℂ → ℂ} {c : ℂ} {r R : ℝ} (hrR : r < R)
    (hd : DifferentiableOn ℂ f (ball c R)) {z₀ : ℂ} (hz₀ : z₀ ∈ ball c R) (hf : f z₀ ≠ 0) :
    {z | z ∈ closedBall c r ∧ f z = 0}.Finite := by
  by_contra hinf
  have hsub : {z | z ∈ closedBall c r ∧ f z = 0} ⊆ closedBall c r := fun z hz => hz.1
  obtain ⟨w, hwK, hw⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf
    (isCompact_closedBall c r) hsub
  have hwB : w ∈ ball c R := by
    have := mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hwK) hrR)
    exact this
  have han : AnalyticAt ℂ f w := (hd.analyticOnNhd isOpen_ball) w hwB
  have hfr : ∃ᶠ z in 𝓝[≠] w, f z = 0 := by
    rw [accPt_iff_frequently_nhdsNE] at hw
    exact hw.mono fun z hz => hz.2
  have := han.frequently_zero_iff_eventually_zero.1 hfr
  exact analyticOrderAt_ne_top_of_ball hd hz₀ hf hwB (analyticOrderAt_eq_top.2 this)

end Involution
