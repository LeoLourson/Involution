module

public import Involution.Estimates.ExpPoly
public import Mathlib.Analysis.Complex.JensenFormula

/-! Лемма `lem:F` (c): равномерная по `X` оценка числа нулей `F` с учётом кратности в
прямоугольнике `[X, X+1] × [-h₀, h₀]` через неравенство Йенсена
(`AnalyticOnNhd.sum_divisor_le`) на круге с центром `X + 1/2 + i(h₀+1)`. Кратность —
`analyticOrderAt`; число нулей в конечном множестве `s` — сумма кратностей. -/

@[expose] public noncomputable section

open Complex Real Filter Topology Metric

namespace Involution

theorem divisor_expPoly_eq {θp θm θdp θdm : ℂ} {L d : ℝ} (U : Set ℂ) {z : ℂ} (hz : z ∈ U) :
    MeromorphicOn.divisor (expPoly θp θm θdp θdm L d) U z =
      ((analyticOrderAt (expPoly θp θm θdp θdm L d) z).toNat : ℤ) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply
    ((expPoly_analytic θp θm θdp θdm L d).mono (Set.subset_univ U)) hz]
  generalize analyticOrderAt (expPoly θp θm θdp θdm L d) z = o
  induction o using ENat.recTopCoe <;> simp

/-- Сумма кратностей по конечному множеству внутри шара не больше суммы дивизора. -/
theorem sum_order_le_finsum {θp θm θdp θdm : ℂ} {L d : ℝ} (c : ℂ) (r : ℝ) (s : Finset ℂ)
    (hs : ∀ z ∈ s, z ∈ closedBall c |r|) :
    ((∑ z ∈ s, (analyticOrderAt (expPoly θp θm θdp θdm L d) z).toNat : ℕ) : ℝ) ≤
      ((∑ᶠ u, MeromorphicOn.divisor (expPoly θp θm θdp θdm L d) (closedBall c |r|) u : ℤ) : ℝ) := by
  set D := MeromorphicOn.divisor (expPoly θp θm θdp θdm L d) (closedBall c |r|) with hD
  have hfin : (Function.support D).Finite := D.finiteSupport (isCompact_closedBall c |r|)
  have hnn : ∀ u, 0 ≤ D u := by
    intro u
    by_cases hu : u ∈ closedBall c |r|
    · rw [hD, divisor_expPoly_eq _ hu]; positivity
    · have : D u = 0 := Function.locallyFinsuppWithin.apply_eq_zero_of_notMem D hu
      rw [this]
  have h1 : ∑ᶠ u, D u = ∑ u ∈ hfin.toFinset ∪ s, D u :=
    finsum_eq_sum_of_support_subset _ (by
      intro u hu; exact Finset.mem_union_left _ (hfin.mem_toFinset.2 hu))
  have h2 : (∑ z ∈ s, D z) ≤ ∑ u ∈ hfin.toFinset ∪ s, D u :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right (fun u _ _ => hnn u)
  have h3 : (∑ z ∈ s, D z) =
      ((∑ z ∈ s, (analyticOrderAt (expPoly θp θm θdp θdm L d) z).toNat : ℕ) : ℤ) := by
    push_cast
    exact Finset.sum_congr rfl fun z hz => by rw [hD, divisor_expPoly_eq _ (hs z hz)]
  rw [h1]
  exact_mod_cast h3 ▸ h2

/-- Лемма `lem:F` (c): в каждом прямоугольнике `[X, X+1] × [-h₀, h₀]` не больше `N₀` нулей
`F` с учётом кратности (`h₀` — любое число, для которого верна оценка (a)). -/
theorem expPoly_count_rect {θp θm θdp θdm : ℂ} {L d h₀ : ℝ} (hL : 0 < L) (hd : |d| < L)
    (hp : θp ≠ 0) (hh : 0 ≤ h₀)
    (hA : ∀ ρ : ℂ, h₀ ≤ |ρ.im| →
      (1 / 2) * ‖θp‖ * Real.exp (L * |ρ.im|) ≤ ‖expPoly θp θm θdp θdm L d ρ‖) :
    ∃ N : ℕ, ∀ (X : ℝ) (s : Finset ℂ),
      (∀ z ∈ s, X ≤ z.re ∧ z.re ≤ X + 1 ∧ |z.im| ≤ h₀ ∧ expPoly θp θm θdp θdm L d z = 0) →
      ∑ z ∈ s, (analyticOrderAt (expPoly θp θm θdp θdm L d) z).toNat ≤ N := by
  set F := expPoly θp θm θdp θdm L d with hF
  have hpos : 0 < ‖θp‖ := norm_pos_iff.2 hp
  set r : ℝ := 2 * h₀ + 2 with hr
  have hrpos : 0 < r := by positivity
  set C : ℝ := ‖θp‖ + ‖θm‖ + ‖θdp‖ + ‖θdm‖ with hC
  set M₀ : ℝ := C * Real.exp (L * (5 * h₀ + 5)) with hM₀
  set m₀ : ℝ := (1 / 2) * ‖θp‖ * Real.exp (L * (h₀ + 1)) with hm₀
  have hm₀pos : 0 < m₀ := by positivity
  refine ⟨⌈Real.log (max 1 M₀ / m₀) / Real.log 2⌉₊, fun X s hs => ?_⟩
  set c : ℂ := ((X + 1 / 2 : ℝ) : ℂ) + ((h₀ + 1 : ℝ) : ℂ) * I with hc
  have hcim : c.im = h₀ + 1 := by simp [hc]
  have hFc : m₀ ≤ ‖F c‖ := by
    have := hA c (by rw [hcim, abs_of_nonneg (by linarith)]; linarith)
    rwa [hcim, abs_of_nonneg (by linarith)] at this
  have hFc0 : F c ≠ 0 := fun h => by rw [h, norm_zero] at hFc; linarith
  have hs' : ∀ z ∈ s, z ∈ closedBall c |r| := by
    intro z hz
    obtain ⟨h1, h2, h3, -⟩ := hs z hz
    rw [mem_closedBall, dist_eq_norm, abs_of_pos hrpos]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have e1 : (z - c).re = z.re - (X + 1 / 2) := by simp [hc]
    have e2 : (z - c).im = z.im - (h₀ + 1) := by simp [hc]
    rw [e1, e2]
    have : |z.re - (X + 1 / 2)| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    have h3' := abs_le.1 h3
    have : |z.im - (h₀ + 1)| ≤ 2 * h₀ + 1 :=
      abs_le.2 ⟨by linarith [h3'.1, h3'.2], by linarith [h3'.1, h3'.2]⟩
    linarith
  have hJ := AnalyticOnNhd.sum_divisor_le (c := c) (r := r) (R := 2 * r) (M := max 1 M₀)
    (f := F) (by rw [abs_of_pos hrpos]; exact hrpos)
    (by rw [abs_of_pos hrpos, abs_of_pos (by positivity)]; linarith) (le_max_left _ _)
    ((expPoly_analytic θp θm θdp θdm L d).mono (Set.subset_univ _)) hFc0 (by
      intro z hz
      refine (le_max_right _ _).trans' ?_
      have h1 := norm_expPoly_le (θp := θp) (θm := θm) (θdp := θdp) (θdm := θdm) hd.le z
      have h2 : |z.im| ≤ 5 * h₀ + 5 := by
        have : ‖z - c‖ = |2 * r| := by rw [← dist_eq_norm]; exact mem_sphere.1 hz
        have h4 : |z.im - c.im| ≤ ‖z - c‖ := by
          simpa using Complex.abs_im_le_norm (z - c)
        rw [abs_of_pos (by positivity : 0 < 2 * r)] at this
        rw [this] at h4
        have := abs_le.1 h4
        rw [hcim] at this
        rw [abs_le]; constructor <;> nlinarith [this.1, this.2]
      refine h1.trans ?_
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h2 hL.le))
        (by positivity))
  have hcount := sum_order_le_finsum (θp := θp) (θm := θm) (θdp := θdp) (θdm := θdm) (L := L)
    (d := d) c r s hs'
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : Real.log (2 * r / r) = Real.log 2 := by
    rw [mul_div_assoc, div_self hrpos.ne', mul_one]
  rw [abs_of_pos hrpos, hq] at hJ
  rw [abs_of_pos hrpos] at hcount
  have hle : Real.log (max 1 M₀ / ‖F c‖) ≤ Real.log (max 1 M₀ / m₀) := by
    apply Real.log_le_log (by have := le_max_left 1 M₀; positivity)
    exact div_le_div_of_nonneg_left (by positivity) hm₀pos hFc
  have h5 : ((∑ z ∈ s, (analyticOrderAt F z).toNat : ℕ) : ℝ) ≤
      Real.log (max 1 M₀ / m₀) / Real.log 2 := by
    refine hcount.trans (hJ.trans ?_)
    exact div_le_div_of_nonneg_right hle hlog2.le
  exact Nat.cast_le.1 (h5.trans (Nat.le_ceil _))

end Involution
