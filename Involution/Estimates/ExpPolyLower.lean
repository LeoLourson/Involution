module

public import Involution.Estimates.ExpPoly
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.Liouville

/-! Лемма `lem:F` (b): оценка `|F(ρ)| ≥ c_δ e^{L|Im ρ|}` вне `δ`-окрестности нулей.
Вместо теоремы Гурвица используется принцип максимума для `1/g` (лемма
`exists_zero_of_close`): если `g` близка к `f` на круге, `f(z₀) = 0` и `|f| ≥ μ` на
окружности, то `g` имеет нуль в круге. Сдвиг `ρ ↦ ρ + t` умножает коэффициенты на
единичные множители (`expPoly_shift`), и семейство сдвигов лежит в компакте. -/

@[expose] public noncomputable section

open Complex Real Filter Topology Metric

namespace Involution

/-- Сдвиг по вещественной оси умножает коэффициенты на фазы. -/
theorem expPoly_shift (θp θm θdp θdm : ℂ) (L d t : ℝ) (z : ℂ) :
    expPoly θp θm θdp θdm L d (t + z) =
      expPoly (θp * cexp (I * t * L)) (θm * cexp (-(I * t * L)))
        (θdp * cexp (I * t * d)) (θdm * cexp (-(I * t * d))) L d z := by
  unfold expPoly
  simp only [mul_add, add_mul, neg_add, Complex.exp_add]
  ring

theorem expPoly_sub (a b c e a' b' c' e' : ℂ) (L d : ℝ) (z : ℂ) :
    expPoly a b c e L d z - expPoly a' b' c' e' L d z =
      expPoly (a - a') (b - b') (c - c') (e - e') L d z := by
  unfold expPoly; ring

/-- Облегчённый вариант теоремы Гурвица: принцип максимума для `1/g`. -/
theorem exists_zero_of_close {f g : ℂ → ℂ} (hg : Differentiable ℂ g) {z₀ : ℂ} {r μ : ℝ}
    (hr : 0 < r) (hμ : 0 < μ) (hf0 : f z₀ = 0)
    (hfs : ∀ z ∈ sphere z₀ r, μ ≤ ‖f z‖)
    (hclose : ∀ z ∈ closedBall z₀ r, ‖g z - f z‖ < μ / 2) :
    ∃ z ∈ closedBall z₀ r, g z = 0 := by
  by_contra hne
  push Not at hne
  have hd : DifferentiableOn ℂ (fun z => (g z)⁻¹) (closedBall z₀ r) := fun z hz =>
    ((hg z).inv (hne z hz)).differentiableWithinAt
  have hd' : DifferentiableOn ℂ (fun z => (g z)⁻¹) (closure (ball z₀ r)) := by
    rw [closure_ball _ hr.ne']; exact hd
  have hbd := Complex.norm_le_of_forall_mem_frontier_norm_le (f := fun z => (g z)⁻¹)
    (U := ball z₀ r) isBounded_ball hd'.diffContOnCl (C := 2 / μ) (by
      intro z hz
      rw [frontier_ball _ hr.ne'] at hz
      have h1 := hclose z (sphere_subset_closedBall hz)
      have h2 := hfs z hz
      have h3 : μ / 2 ≤ ‖g z‖ := by
        have := norm_sub_norm_le (f z) (f z - g z)
        have h4 : ‖f z - g z‖ = ‖g z - f z‖ := norm_sub_rev _ _
        rw [sub_sub_cancel] at this
        linarith
      rw [norm_inv]
      calc (‖g z‖)⁻¹ ≤ (μ / 2)⁻¹ := inv_anti₀ (by positivity) h3
        _ = 2 / μ := by field_simp) (z := z₀) (by simp [closure_ball _ hr.ne', hr.le])
  have h5 := hclose z₀ (mem_closedBall_self hr.le)
  rw [hf0, sub_zero] at h5
  have hgpos : 0 < ‖g z₀‖ := norm_pos_iff.2 (hne z₀ (mem_closedBall_self hr.le))
  rw [norm_inv] at hbd
  have : μ / 2 ≤ ‖g z₀‖ := by
    have := (inv_le_comm₀ hgpos (by positivity)).1 hbd
    rwa [inv_div] at this
  linarith

/-- Нули целой функции, не равной тождественно нулю, изолированы. -/
theorem exists_ball_ne_zero {G : ℂ → ℂ} (hG : Differentiable ℂ G) {w : ℂ} (hw : G w ≠ 0)
    (z₀ : ℂ) : ∃ r₀ > 0, ∀ z, z ≠ z₀ → dist z z₀ < r₀ → G z ≠ 0 := by
  have han : AnalyticOnNhd ℂ G Set.univ := fun z _ => hG.analyticAt z
  rcases (hG.analyticAt z₀).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact absurd (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ z₀) h (Set.mem_univ w)) hw
  · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
    obtain ⟨r₀, hr₀, hh⟩ := h
    exact ⟨r₀, hr₀, fun z hz hd => hh hd hz⟩

/-- Коэффициенты `(θ₊, θ₋, θ_d⁺, θ_d⁻)` одним кортежем. -/
abbrev ExpPolyCoef := ℂ × ℂ × ℂ × ℂ

/-- Экспоненциальный многочлен с коэффициентами-кортежем. -/
def expPolyC (L d : ℝ) (q : ExpPolyCoef) (z : ℂ) : ℂ :=
  expPoly q.1 q.2.1 q.2.2.1 q.2.2.2 L d z

/-- Расстояние между кортежами коэффициентов (сумма норм разностей). -/
def coefDist (q q' : ExpPolyCoef) : ℝ :=
  ‖q.1 - q'.1‖ + ‖q.2.1 - q'.2.1‖ + ‖q.2.2.1 - q'.2.2.1‖ + ‖q.2.2.2 - q'.2.2.2‖

theorem expPolyC_differentiable (L d : ℝ) (q : ExpPolyCoef) :
    Differentiable ℂ (expPolyC L d q) := expPoly_differentiable _ _ _ _ _ _

theorem continuous_expPolyC (L d : ℝ) :
    Continuous fun p : ExpPolyCoef × ℂ => expPolyC L d p.1 p.2 := by
  unfold expPolyC expPoly; fun_prop

theorem norm_expPolyC_sub_le {L d : ℝ} (hd : |d| ≤ L) (q q' : ExpPolyCoef) (z : ℂ) :
    ‖expPolyC L d q z - expPolyC L d q' z‖ ≤ coefDist q q' * Real.exp (L * |z.im|) := by
  unfold expPolyC coefDist
  rw [expPoly_sub]
  exact norm_expPoly_le hd z

/-- Нули устойчивы: у близкого набора коэффициентов есть нуль вблизи нуля `z₀`. -/
theorem expPolyC_zero_stable {L d : ℝ} (hd : |d| ≤ L) {q : ExpPolyCoef}
    (hq : ∃ w, expPolyC L d q w ≠ 0) {z₀ : ℂ} (hz : expPolyC L d q z₀ = 0) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ ε > 0, ∀ q' : ExpPolyCoef, coefDist q' q < ε →
      ∃ z', expPolyC L d q' z' = 0 ∧ dist z' z₀ < δ := by
  obtain ⟨w, hw⟩ := hq
  obtain ⟨r₀, hr₀, hiso⟩ := exists_ball_ne_zero (expPolyC_differentiable L d q) hw z₀
  set r := min (min (r₀ / 2) (δ / 2)) 1 with hr
  have hrpos : 0 < r := by positivity
  have hrδ : r ≤ δ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hrr₀ : r < r₀ := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _))
    (by linarith)
  have hr1 : r ≤ 1 := min_le_right _ _
  obtain ⟨zm, hzm, hmin⟩ := (isCompact_sphere z₀ r).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 hrpos.le) (continuous_norm.comp (continuous_expPolyC L d |>.comp
      (Continuous.prodMk continuous_const continuous_id))).continuousOn
  set μ := ‖expPolyC L d q zm‖ with hμ
  have hzm0 : expPolyC L d q zm ≠ 0 := by
    apply hiso zm
    · intro h; rw [h, mem_sphere, dist_self] at hzm; linarith
    · rw [mem_sphere] at hzm; rw [hzm]; exact hrr₀
  have hμpos : 0 < μ := norm_pos_iff.2 hzm0
  set E := Real.exp (L * (|z₀.im| + 1)) with hE
  have hEpos : 0 < E := Real.exp_pos _
  refine ⟨μ / 2 / E, by positivity, fun q' hq' => ?_⟩
  have hclose : ∀ z ∈ closedBall z₀ r, ‖expPolyC L d q' z - expPolyC L d q z‖ < μ / 2 := by
    intro z hzb
    have h1 := norm_expPolyC_sub_le hd q' q z
    have hL : 0 ≤ L := (abs_nonneg d).trans hd
    have him : |z.im| ≤ |z₀.im| + 1 := by
      have : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
        simpa using Complex.abs_im_le_norm (z - z₀)
      rw [mem_closedBall, dist_eq_norm] at hzb
      calc |z.im| = |(z.im - z₀.im) + z₀.im| := by ring_nf
        _ ≤ |z.im - z₀.im| + |z₀.im| := abs_add_le _ _
        _ ≤ _ := by linarith
    have h2 : Real.exp (L * |z.im|) ≤ E := Real.exp_le_exp.2 (by nlinarith)
    have h3 : 0 ≤ coefDist q' q := by unfold coefDist; positivity
    calc _ ≤ coefDist q' q * Real.exp (L * |z.im|) := h1
      _ ≤ coefDist q' q * E := mul_le_mul_of_nonneg_left h2 h3
      _ < μ / 2 / E * E := mul_lt_mul_of_pos_right hq' hEpos
      _ = μ / 2 := by field_simp
  obtain ⟨z', hz'b, hz'⟩ := exists_zero_of_close (expPolyC_differentiable L d q') hrpos hμpos hz
    (fun z hz => by
      have := hmin (a := z) hz
      simpa [hμ] using this) hclose
  exact ⟨z', hz', lt_of_le_of_lt (mem_closedBall.1 hz'b) (by linarith)⟩

theorem expPolyC_exists_ne {L d : ℝ} (hL : 0 < L) (hd : |d| < L) {q : ExpPolyCoef}
    (hp : q.1 ≠ 0) (hm : ‖q.2.1‖ = ‖q.1‖) : ∃ w, expPolyC L d q w ≠ 0 := by
  obtain ⟨h₀, h1, h⟩ := expPoly_lower_outside (θdp := q.2.2.1) (θdm := q.2.2.2) hL hd hp hm
  refine ⟨(h₀ : ℂ) * I, fun h0 => ?_⟩
  have := h (h₀ * I) (by simp [abs_of_nonneg (by linarith : 0 ≤ h₀)])
  have h0' : expPoly q.1 q.2.1 q.2.2.1 q.2.2.2 L d (↑h₀ * I) = 0 := h0
  rw [h0', norm_zero] at this
  have hpos : 0 < ‖q.1‖ := norm_pos_iff.2 hp
  have := Real.exp_pos (L * |((h₀ : ℂ) * I).im|)
  nlinarith

/-- Кортеж коэффициентов после сдвига на `t`. -/
def phaseCoef (θp θm θdp θdm : ℂ) (L d t : ℝ) : ExpPolyCoef :=
  (θp * cexp (I * t * L), θm * cexp (-(I * t * L)),
    θdp * cexp (I * t * d), θdm * cexp (-(I * t * d)))

theorem expPoly_eq_phase (θp θm θdp θdm : ℂ) (L d : ℝ) (ρ : ℂ) :
    expPoly θp θm θdp θdm L d ρ =
      expPolyC L d (phaseCoef θp θm θdp θdm L d ρ.re) ((ρ.im : ℂ) * I) := by
  have : ρ = (ρ.re : ℂ) + (ρ.im : ℂ) * I := (Complex.re_add_im ρ).symm
  conv_lhs => rw [this]
  exact expPoly_shift θp θm θdp θdm L d ρ.re _

theorem expPolyC_phase (θp θm θdp θdm : ℂ) (L d t : ℝ) (z : ℂ) :
    expPolyC L d (phaseCoef θp θm θdp θdm L d t) z =
      expPoly θp θm θdp θdm L d (t + z) := (expPoly_shift _ _ _ _ _ _ _ _).symm

theorem phaseCoef_mem (θp θm θdp θdm : ℂ) (L d t : ℝ) :
    phaseCoef θp θm θdp θdm L d t ∈
      sphere (0 : ℂ) ‖θp‖ ×ˢ sphere (0 : ℂ) ‖θm‖ ×ˢ sphere (0 : ℂ) ‖θdp‖ ×ˢ
        sphere (0 : ℂ) ‖θdm‖ := by
  have h1 : ∀ c : ℝ, ‖cexp (I * (t : ℂ) * c)‖ = 1 := fun c => by
    have := norm_cexp_I_mul (t : ℂ) c; simpa using this
  have h2 : ∀ c : ℝ, ‖cexp (-(I * (t : ℂ) * c))‖ = 1 := fun c => by
    have := norm_cexp_neg_I_mul (t : ℂ) c; simpa using this
  simp [phaseCoef, h1, h2]

theorem dist_real_mul_I (a b : ℝ) : dist ((a : ℂ) * I) ((b : ℂ) * I) = dist a b := by
  rw [dist_eq_norm, ← sub_mul, norm_mul, Complex.norm_I, mul_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.dist_eq, Real.norm_eq_abs]

/-- Предельный шаг: последовательность в полосе с `F(ρ_n) → 0` не может быть на расстоянии
`≥ δ` от нулей. -/
theorem expPoly_no_seq {θp θm θdp θdm : ℂ} {L d : ℝ} (hL : 0 < L) (hd : |d| < L)
    (hp : θp ≠ 0) (hm : ‖θm‖ = ‖θp‖) {δ h₀ : ℝ} (hδ : 0 < δ) (ρ : ℕ → ℂ)
    (hρ : ∀ n z, expPoly θp θm θdp θdm L d z = 0 → δ ≤ dist (ρ n) z)
    (hρim : ∀ n, |(ρ n).im| ≤ h₀)
    (hF : Tendsto (fun n => expPoly θp θm θdp θdm L d (ρ n)) atTop (𝓝 0)) : False := by
  have hcomp : IsCompact ((sphere (0 : ℂ) ‖θp‖ ×ˢ sphere (0 : ℂ) ‖θm‖ ×ˢ
      sphere (0 : ℂ) ‖θdp‖ ×ˢ sphere (0 : ℂ) ‖θdm‖ : Set ExpPolyCoef) ×ˢ Set.Icc (-h₀) h₀) :=
    ((isCompact_sphere _ _).prod ((isCompact_sphere _ _).prod ((isCompact_sphere _ _).prod
      (isCompact_sphere _ _)))).prod isCompact_Icc
  have hx : ∀ n, (phaseCoef θp θm θdp θdm L d (ρ n).re, (ρ n).im) ∈
      (sphere (0 : ℂ) ‖θp‖ ×ˢ sphere (0 : ℂ) ‖θm‖ ×ˢ
      sphere (0 : ℂ) ‖θdp‖ ×ˢ sphere (0 : ℂ) ‖θdm‖ : Set ExpPolyCoef) ×ˢ Set.Icc (-h₀) h₀ :=
    fun n => ⟨phaseCoef_mem _ _ _ _ _ _ _, abs_le.1 (hρim n)⟩
  obtain ⟨⟨q, y⟩, hS, φ, hφ, hlim⟩ := hcomp.tendsto_subseq hx
  have hq : Tendsto (fun n => phaseCoef θp θm θdp θdm L d (ρ (φ n)).re) atTop (𝓝 q) :=
    (continuous_fst.tendsto _).comp hlim
  have hy : Tendsto (fun n => (ρ (φ n)).im) atTop (𝓝 y) :=
    (continuous_snd.tendsto _).comp hlim
  have hF0 := hF.comp hφ.tendsto_atTop
  have hI : Tendsto (fun n => (((ρ (φ n)).im : ℝ) : ℂ) * I) atTop (𝓝 ((y : ℂ) * I)) :=
    ((Complex.continuous_ofReal.tendsto y).comp hy).mul_const I
  have hpair := hq.prodMk_nhds hI
  have hlim0 := ((continuous_expPolyC L d).tendsto _).comp hpair
  have hz0 : expPolyC L d q ((y : ℂ) * I) = 0 := by
    refine tendsto_nhds_unique hlim0 (hF0.congr fun n => ?_)
    exact expPoly_eq_phase θp θm θdp θdm L d (ρ (φ n))
  obtain ⟨hq1, hq2, hq3, hq4⟩ := hS.1
  rw [mem_sphere_zero_iff_norm] at hq1 hq2
  have hq1' : ‖q.1‖ = ‖θp‖ := hq1
  have hq2' : ‖q.2.1‖ = ‖θm‖ := hq2
  have hex := expPolyC_exists_ne hL hd (q := q) (by
    intro h; rw [h, norm_zero] at hq1'; exact hp (norm_eq_zero.1 hq1'.symm))
    (hq2'.trans (hm.trans hq1'.symm))
  obtain ⟨ε, hε, hst⟩ := expPolyC_zero_stable hd.le hex hz0 (half_pos hδ)
  have hcd : Tendsto (fun n => coefDist (phaseCoef θp θm θdp θdm L d (ρ (φ n)).re) q)
      atTop (𝓝 0) := by
    have hc : Continuous fun q' => coefDist q' q := by unfold coefDist; fun_prop
    have h0 : coefDist q q = 0 := by simp [coefDist]
    have := (hc.tendsto q).comp hq
    rw [h0] at this
    exact this
  have ev1 := hcd.eventually (gt_mem_nhds hε)
  have ev2 := (Metric.tendsto_nhds.1 hy) (δ / 2) (half_pos hδ)
  obtain ⟨n, hn1, hn2⟩ := (ev1.and ev2).exists
  obtain ⟨z', hz', hdz⟩ := hst _ hn1
  have hzero : expPoly θp θm θdp θdm L d ((ρ (φ n)).re + z') = 0 := by
    rw [← expPolyC_phase]; exact hz'
  have := hρ (φ n) _ hzero
  have hdist : dist (ρ (φ n)) ((ρ (φ n)).re + z') < δ := by
    have e : ρ (φ n) = ((ρ (φ n)).re : ℂ) + ((ρ (φ n)).im : ℂ) * I :=
      (Complex.re_add_im _).symm
    rw [show dist (ρ (φ n)) ((ρ (φ n)).re + z') =
      dist (((ρ (φ n)).re : ℂ) + ((ρ (φ n)).im : ℂ) * I) (((ρ (φ n)).re : ℂ) + z') by rw [← e]]
    rw [dist_add_left]
    calc _ ≤ dist (((ρ (φ n)).im : ℂ) * I) ((y : ℂ) * I) + dist ((y : ℂ) * I) z' :=
          dist_triangle _ _ _
      _ < δ / 2 + δ / 2 := by
          rw [dist_real_mul_I]; exact add_lt_add hn2 (by rwa [dist_comm])
      _ = δ := by ring
  linarith

/-- Лемма `lem:F` (b): оценка снизу вне `δ`-окрестности нулей. Условие
`∀ z, F z = 0 → δ ≤ dist ρ z` означает `dist(ρ, Z_F) ≥ δ` (и не пусто при `Z_F = ∅`). -/
theorem expPoly_lower_dist {θp θm θdp θdm : ℂ} {L d : ℝ} (hL : 0 < L) (hd : |d| < L)
    (hp : θp ≠ 0) (hm : ‖θm‖ = ‖θp‖) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c > 0, ∀ ρ : ℂ, (∀ z, expPoly θp θm θdp θdm L d z = 0 → δ ≤ dist ρ z) →
      c * Real.exp (L * |ρ.im|) ≤ ‖expPoly θp θm θdp θdm L d ρ‖ := by
  obtain ⟨h₀, h01, hA⟩ := expPoly_lower_outside (θdp := θdp) (θdm := θdm) hL hd hp hm
  have hpos : 0 < ‖θp‖ := norm_pos_iff.2 hp
  have hmpos : 0 < (1 / 2) * ‖θp‖ := by positivity
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ ρ : ℂ, (∀ z, expPoly θp θm θdp θdm L d z = 0 → δ ≤ dist ρ z) ∧
      |ρ.im| ≤ h₀ ∧ ‖expPoly θp θm θdp θdm L d ρ‖ <
        (1 / 2) * ‖θp‖ / ((n : ℝ) + 1) * Real.exp (L * h₀) := by
    intro n
    have hc : 0 < (1 / 2) * ‖θp‖ / ((n : ℝ) + 1) := by positivity
    obtain ⟨ρ, hρ, hlt⟩ := hcon _ hc
    have hle : |ρ.im| ≤ h₀ := by
      by_contra hgt
      have h1 := hA ρ (not_le.1 hgt).le
      have h2 : (1 / 2) * ‖θp‖ / ((n : ℝ) + 1) ≤ (1 / 2) * ‖θp‖ :=
        div_le_self hmpos.le (by linarith [n.cast_nonneg (α := ℝ)])
      have := Real.exp_pos (L * |ρ.im|)
      nlinarith
    refine ⟨ρ, hρ, hle, lt_of_lt_of_le hlt (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hle hL.le)) hc.le)⟩
  choose ρ hρ hρim hρF using hseq
  refine expPoly_no_seq hL hd hp hm hδ ρ (fun n => hρ n) hρim ?_
  have h1 : Tendsto (fun n : ℕ => (1 / 2) * ‖θp‖ * Real.exp (L * h₀) * (1 / ((n : ℝ) + 1)))
      atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul
      ((1 / 2) * ‖θp‖ * Real.exp (L * h₀))
  refine squeeze_zero_norm (fun n => ?_) h1
  have := (hρF n).le
  calc _ ≤ _ := this
    _ = _ := by ring

end Involution
