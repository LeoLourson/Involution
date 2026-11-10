module

public import Involution.Estimates.ExpPolyLower
public import Involution.Estimates.ExpPolyCount
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.SpecialFunctions.Integrability.Log
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Лемма `lem:F` (d): множество нулей `F` бесконечно. Вместо теоремы Адамара (её нет в
Mathlib) используется формула Йенсена: при конечном `Z_F` на больших окружностях по (b)
`log|F| ≥ log c₁ + L|Im ρ|`, среднее по окружности радиуса `R` не меньше `L R/2 - const`, а
правая часть формулы Йенсена равна `M log R + const`. -/

@[expose] public noncomputable section

open Complex Real Filter Topology Metric MeasureTheory

namespace Involution

/-- Среднее по окружности от `(Im (z - c))²` равно `R²/2`. -/
theorem circleAverage_im_sq (c : ℂ) (R : ℝ) :
    circleAverage (fun z : ℂ => (z - c).im ^ 2) c R = R ^ 2 / 2 := by
  rw [circleAverage_def]
  have : ∀ θ : ℝ, ((circleMap c R θ) - c).im ^ 2 = R ^ 2 * Real.sin θ ^ 2 := by
    intro θ; simp [circleMap, Complex.exp_ofReal_mul_I_im, mul_pow]
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul, integral_sin_sq]
  simp only [smul_eq_mul, Real.sin_zero, Real.cos_zero, Real.sin_two_pi, Real.cos_two_pi]
  field_simp
  ring

/-- Нижняя оценка среднего `log |F|` по окружности, лежащей на расстоянии `≥ 1` от нулей. -/
theorem circleAverage_log_expPoly_ge {θp θm θdp θdm : ℂ} {L d : ℝ} (hL : 0 < L) {cδ : ℝ}
    (hcδ : 0 < cδ)
    (hb : ∀ ρ : ℂ, (∀ z, expPoly θp θm θdp θdm L d z = 0 → 1 ≤ dist ρ z) →
      cδ * Real.exp (L * |ρ.im|) ≤ ‖expPoly θp θm θdp θdm L d ρ‖)
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hfar : ∀ z ∈ sphere c R, ∀ w, expPoly θp θm θdp θdm L d w = 0 → 1 ≤ dist z w) :
    Real.log cδ + (L * R / 2 - L * |c.im|) ≤
      circleAverage (fun z => Real.log ‖expPoly θp θm θdp θdm L d z‖) c R := by
  set g : ℂ → ℝ := fun z => (Real.log cδ - L * |c.im|) + (L / R) * (z - c).im ^ 2 with hg
  have hgc : Continuous g := by rw [hg]; fun_prop
  have hgi : CircleIntegrable g c R := hgc.continuousOn.circleIntegrable'
  have hFi : CircleIntegrable (fun z => Real.log ‖expPoly θp θm θdp θdm L d z‖) c R :=
    ((expPoly_analytic θp θm θdp θdm L d).meromorphicOn.mono_set
      (Set.subset_univ (sphere c |R|))).circleIntegrable_log_norm
  have hq : CircleIntegrable (fun z : ℂ => (L / R) * (z - c).im ^ 2) c R := by
    refine ContinuousOn.circleIntegrable' ?_
    exact (by fun_prop : Continuous fun z : ℂ => (L / R) * (z - c).im ^ 2).continuousOn
  have hgavg : circleAverage g c R = Real.log cδ + (L * R / 2 - L * |c.im|) := by
    have h1 := circleAverage_fun_smul (a := L / R) (f := fun z : ℂ => (z - c).im ^ 2) (c := c)
      (R := R)
    simp only [smul_eq_mul] at h1
    rw [hg, circleAverage_fun_add (circleIntegrable_const _ _ _) hq, circleAverage_const, h1,
      circleAverage_im_sq]
    field_simp
    ring
  rw [← hgavg]
  refine circleAverage_mono hgi hFi fun z hz => ?_
  rw [abs_of_pos hR] at hz
  have h1 := hb z (hfar z hz)
  have hFpos : 0 < ‖expPoly θp θm θdp θdm L d z‖ :=
    lt_of_lt_of_le (by positivity) h1
  have h2 : Real.log cδ + L * |z.im| ≤ Real.log ‖expPoly θp θm θdp θdm L d z‖ := by
    have := Real.log_le_log (by positivity) h1
    rwa [Real.log_mul hcδ.ne' (Real.exp_pos _).ne', Real.log_exp] at this
  have ht : |(z - c).im| ≤ R := by
    have h3 := Complex.abs_im_le_norm (z - c)
    rwa [← dist_eq_norm, mem_sphere.1 hz] at h3
  have h4 : (z - c).im ^ 2 / R ≤ |(z - c).im| := by
    rw [div_le_iff₀ hR, sq]
    calc (z - c).im * (z - c).im ≤ |(z - c).im| * |(z - c).im| := by
          exact (abs_mul_abs_self _).symm.le
      _ ≤ |(z - c).im| * R := mul_le_mul_of_nonneg_left ht (abs_nonneg _)
  have h5 : |(z - c).im| ≤ |z.im| + |c.im| := by
    simpa using abs_sub z.im c.im
  have : L / R * (z - c).im ^ 2 ≤ L * (|z.im| + |c.im|) := by
    rw [div_mul_eq_mul_div, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (h4.trans h5) hL.le
  simp only [hg]
  nlinarith

theorem divisor_expPoly_eq_zero {θp θm θdp θdm : ℂ} {L d : ℝ} (U : Set ℂ) {u : ℂ}
    (h : expPoly θp θm θdp θdm L d u ≠ 0) :
    MeromorphicOn.divisor (expPoly θp θm θdp θdm L d) U u = 0 := by
  by_cases hu : u ∈ U
  · rw [divisor_expPoly_eq U hu,
      ((expPoly_analytic θp θm θdp θdm L d) u trivial).analyticOrderAt_eq_zero.2 h]
    simp
  · exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu

/-- Формула Йенсена для `F` с конечным множеством нулей `T`, целиком лежащим в круге. -/
theorem circleAverage_log_expPoly_eq {θp θm θdp θdm : ℂ} {L d : ℝ} (T : Finset ℂ)
    (hT : ∀ u, expPoly θp θm θdp θdm L d u = 0 ↔ u ∈ T) {c : ℂ}
    (hc : expPoly θp θm θdp θdm L d c ≠ 0) {R : ℝ} (hR : 0 < R)
    (hin : ∀ u ∈ T, dist u c ≤ R) :
    circleAverage (fun z => Real.log ‖expPoly θp θm θdp θdm L d z‖) c R =
      (∑ u ∈ T, ((analyticOrderAt (expPoly θp θm θdp θdm L d) u).toNat : ℝ)) * Real.log R -
        (∑ u ∈ T, ((analyticOrderAt (expPoly θp θm θdp θdm L d) u).toNat : ℝ) *
          Real.log ‖c - u‖) + Real.log ‖expPoly θp θm θdp θdm L d c‖ := by
  rw [AnalyticOnNhd.circleAverage_log_norm hR.ne'
    ((expPoly_analytic θp θm θdp θdm L d).mono (Set.subset_univ _)) hc]
  rw [finsum_eq_sum_of_support_subset (s := T)]
  · rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun u hu => ?_
    have hF0 : expPoly θp θm θdp θdm L d u = 0 := (hT u).2 hu
    have hcu : ‖c - u‖ ≠ 0 := fun h => hc (by
      have : c = u := sub_eq_zero.1 (norm_eq_zero.1 h)
      rw [this]; exact hF0)
    have hmem : u ∈ closedBall c |R| := by
      rw [mem_closedBall, abs_of_pos hR]; exact hin u hu
    rw [divisor_expPoly_eq _ hmem, Int.cast_natCast, Real.log_mul hR.ne' (inv_ne_zero hcu),
      Real.log_inv]
    ring
  · intro u hu
    rw [Function.mem_support] at hu
    by_contra hnu
    exact hu (by
      rw [divisor_expPoly_eq_zero]
      · simp
      · exact fun h => hnu ((hT u).1 h))

/-- Лемма `lem:F` (d), первая часть: множество нулей `F` бесконечно. -/
theorem expPoly_zeros_infinite {θp θm θdp θdm : ℂ} {L d : ℝ} (hL : 0 < L) (hd : |d| < L)
    (hp : θp ≠ 0) (hm : ‖θm‖ = ‖θp‖) :
    {z : ℂ | expPoly θp θm θdp θdm L d z = 0}.Infinite := by
  intro hfin'
  set F := expPoly θp θm θdp θdm L d with hF
  have hfin : {z : ℂ | F z = 0}.Finite := hfin'
  set T := hfin.toFinset with hTdef
  have hT : ∀ u, F u = 0 ↔ u ∈ T := fun u => by simp [hTdef]
  obtain ⟨h₀, h01, hA⟩ := expPoly_lower_outside (θdp := θdp) (θdm := θdm) hL hd hp hm
  have hpos : 0 < ‖θp‖ := norm_pos_iff.2 hp
  set c : ℂ := (h₀ : ℂ) * I with hcdef
  have hcim : |c.im| = h₀ := by simp [hcdef, abs_of_nonneg (by linarith : 0 ≤ h₀)]
  have hc : F c ≠ 0 := by
    intro h
    have := hA c (by rw [hcim])
    rw [show expPoly θp θm θdp θdm L d c = 0 from h, norm_zero] at this
    have := Real.exp_pos (L * |c.im|)
    nlinarith
  obtain ⟨cδ, hcδ, hb⟩ := expPoly_lower_dist (θdp := θdp) (θdm := θdm) hL hd hp hm
    (zero_lt_one : (0 : ℝ) < 1)
  set A : ℝ := ∑ u ∈ T, ‖u‖ with hAdef
  set Mt : ℝ := ∑ u ∈ T, ((analyticOrderAt F u).toNat : ℝ) with hMt
  set K : ℝ := ∑ u ∈ T, ((analyticOrderAt F u).toNat : ℝ) * Real.log ‖c - u‖ with hK
  have hAnn : 0 ≤ A := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hMnn : 0 ≤ Mt := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hu_le : ∀ u ∈ T, ‖u‖ ≤ A := fun u hu =>
    Finset.single_le_sum (f := fun u => ‖u‖) (fun _ _ => norm_nonneg _) hu
  have key : ∀ R : ℝ, ‖c‖ + A + 1 < R →
      Real.log cδ + (L * R / 2 - L * |c.im|) ≤ Mt * Real.log R - K + Real.log ‖F c‖ := by
    intro R hR
    have hRpos : 0 < R := by linarith [norm_nonneg c]
    have hin : ∀ u ∈ T, dist u c ≤ R := by
      intro u hu
      have := dist_le_norm_add_norm u c
      linarith [hu_le u hu]
    have hfar : ∀ z ∈ sphere c R, ∀ w, F w = 0 → 1 ≤ dist z w := by
      intro z hz w hw
      have h2 := dist_triangle z w c
      rw [mem_sphere] at hz
      have h3 : dist w c ≤ ‖c‖ + A := by
        have := dist_le_norm_add_norm w c
        linarith [hu_le w ((hT w).1 hw)]
      linarith
    have h1 := circleAverage_log_expPoly_ge hL hcδ hb hRpos hfar
    rw [circleAverage_log_expPoly_eq T hT hc hRpos hin] at h1
    exact h1
  set C₀ : ℝ := Real.log ‖F c‖ - K - Real.log cδ + L * |c.im| with hC₀
  set ε : ℝ := L / (4 * (Mt + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have hlo := Real.isLittleO_log_id_atTop.def hεpos
  obtain ⟨R, ⟨hR1, hR2⟩, hR3, hR4⟩ := (((eventually_gt_atTop (‖c‖ + A + 1)).and
    (eventually_gt_atTop (4 * C₀ / L))).and (hlo.and (eventually_gt_atTop (0 : ℝ)))).exists
  have h1 := key R hR1
  have h2 : Real.log R ≤ ε * R := by
    have := hR3
    simp only [id, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans_eq (by rw [abs_of_pos hR4]))
  have h3 : Mt * Real.log R ≤ L * R / 4 := by
    calc Mt * Real.log R ≤ Mt * (ε * R) := mul_le_mul_of_nonneg_left h2 hMnn
      _ = L * R / 4 * (Mt / (Mt + 1)) := by rw [hε]; field_simp
      _ ≤ L * R / 4 * 1 := by
          gcongr
          rw [div_le_one (by linarith)]; linarith
      _ = _ := mul_one _
  have h4 : 4 * C₀ / L < R := hR2
  rw [div_lt_iff₀ hL] at h4
  nlinarith

/-- В любом шаре у функции `F`, не равной тождественно нулю, конечное число нулей. -/
theorem expPoly_zeros_finite_ball {θp θm θdp θdm : ℂ} {L d : ℝ} {w : ℂ}
    (hw : expPoly θp θm θdp θdm L d w ≠ 0) (c : ℂ) (r : ℝ) :
    {z : ℂ | expPoly θp θm θdp θdm L d z = 0 ∧ z ∈ closedBall c r}.Finite := by
  set F := expPoly θp θm θdp θdm L d with hF
  have hfs := (MeromorphicOn.divisor F (closedBall c |r|)).finiteSupport
    (isCompact_closedBall c |r|)
  refine hfs.subset fun z ⟨hz, hzb⟩ => ?_
  have hzb' : z ∈ closedBall c |r| := closedBall_subset_closedBall (le_abs_self r) hzb
  rw [Function.mem_support, divisor_expPoly_eq _ hzb']
  have han : AnalyticOnNhd ℂ F Set.univ := expPoly_analytic θp θm θdp θdm L d
  have hne : analyticOrderAt F z ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    exact hw (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ z) htop (Set.mem_univ w))
  have hne0 : analyticOrderAt F z ≠ 0 := fun h0 =>
    ((han z trivial).analyticOrderAt_eq_zero.1 h0) hz
  intro h
  have h' : (analyticOrderAt F z).toNat = 0 := by exact_mod_cast h
  rcases (ENat.toNat_eq_zero.1 h') with h1 | h1
  · exact hne0 h1
  · exact hne h1

/-- Лемма `lem:F` (d): бесконечно много нулей в полуплоскости `Re ρ > 0`, если множество
нулей симметрично относительно нуля (`F(-ρ) = ±F(ρ)`). -/
theorem expPoly_zeros_pos_re_infinite {θp θm θdp θdm : ℂ} {L d : ℝ} (hL : 0 < L)
    (hd : |d| < L) (hp : θp ≠ 0) (hm : ‖θm‖ = ‖θp‖)
    (hsym : ∀ z, expPoly θp θm θdp θdm L d z = 0 → expPoly θp θm θdp θdm L d (-z) = 0) :
    {z : ℂ | expPoly θp θm θdp θdm L d z = 0 ∧ 0 < z.re}.Infinite := by
  intro hfin
  obtain ⟨h₀, h01, hA⟩ := expPoly_lower_outside (θdp := θdp) (θdm := θdm) hL hd hp hm
  have hpos : 0 < ‖θp‖ := norm_pos_iff.2 hp
  have hw : expPoly θp θm θdp θdm L d ((h₀ : ℂ) * I) ≠ 0 := by
    intro h
    have h1 := hA ((h₀ : ℂ) * I) (by simp [abs_of_nonneg (by linarith : 0 ≤ h₀)])
    rw [h, norm_zero] at h1
    have h2 := Real.exp_pos (L * |((h₀ : ℂ) * I).im|)
    nlinarith
  have hball := expPoly_zeros_finite_ball hw 0 h₀
  refine expPoly_zeros_infinite (θdp := θdp) (θdm := θdm) hL hd hp hm ?_
  refine (hfin.union (hfin.image Neg.neg |>.union hball)).subset fun z hz => ?_
  rcases lt_trichotomy z.re 0 with h | h | h
  · right; left
    exact ⟨-z, ⟨hsym z hz, by simpa using h⟩, by simp⟩
  · right; right
    refine ⟨hz, ?_⟩
    have := expPoly_zero_im_lt hp hA hz
    rw [mem_closedBall, dist_zero_right]
    have h2 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    rw [h, abs_zero] at h2
    linarith
  · left; exact ⟨hz, h⟩

end Involution
