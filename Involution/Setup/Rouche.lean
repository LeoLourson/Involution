module

public import Involution.Setup.RoucheArgument
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Order.IntermediateValue

/-! Теорема Руше для круга: равенство чисел нулей `f` и `f + g` с учётом кратности. -/

@[expose] public noncomputable section

open Metric Set Filter Topology Complex
open scoped Real

namespace Involution

/-- Непрерывная функция на `[0,1]` со значениями в `ℕ` принимает на концах одно значение. -/
theorem nat_valued_endpoints {k : ℝ → ℝ} (hk : ContinuousOn k (Icc 0 1)) (n : ℝ → ℕ)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, k t = n t) : n 0 = n 1 := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have key : ∀ (a m : ℕ), (m : ℝ) = (a : ℝ) + 1 / 2 → False := by
    intro a m hm
    have h2 : ((2 * m : ℕ) : ℝ) = ((2 * a + 1 : ℕ) : ℝ) := by push_cast; linarith
    have := Nat.cast_injective h2
    omega
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hk01 : (n 0 : ℝ) < n 1 := by exact_mod_cast hlt
    have hmem : (n 0 : ℝ) + 1 / 2 ∈ Icc (k 0) (k 1) := by
      rw [h 0 h0, h 1 h1]
      constructor
      · linarith
      · have : (n 0 : ℝ) + 1 ≤ n 1 := by exact_mod_cast hlt
        linarith
    obtain ⟨t, ht, hkt⟩ := intermediate_value_Icc zero_le_one hk hmem
    rw [h t ht] at hkt
    exact key _ _ hkt
  · have hmem : (n 1 : ℝ) + 1 / 2 ∈ Icc (k 1) (k 0) := by
      rw [h 0 h0, h 1 h1]
      constructor
      · linarith
      · have : (n 1 : ℝ) + 1 ≤ n 0 := by exact_mod_cast hgt
        linarith
    obtain ⟨t, ht, hkt⟩ := intermediate_value_Icc' zero_le_one hk hmem
    rw [h t ht] at hkt
    exact key _ _ hkt

/-- Срезка параметра гомотопии на отрезок `[0,1]`. -/
def clamp01 (t : ℝ) : ℝ := max 0 (min 1 t)

theorem clamp01_mem (t : ℝ) : clamp01 t ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem continuous_clamp01 : Continuous clamp01 := by
  unfold clamp01; fun_prop

theorem clamp01_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : clamp01 t = t := by
  unfold clamp01
  rw [min_eq_right ht.2, max_eq_right ht.1]

section

variable {f g : ℂ → ℂ} {c : ℂ} {r R : ℝ}

theorem homotopy_ne_zero (hfg : ∀ z ∈ sphere c r, ‖g z‖ < ‖f z‖) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : z ∈ sphere c r) : f z + (s : ℂ) * g z ≠ 0 := by
  intro h
  have h1 : f z = -((s : ℂ) * g z) := eq_neg_of_add_eq_zero_left h
  have h2 : ‖f z‖ ≤ ‖g z‖ := by
    rw [h1, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hs.2
  exact absurd (hfg z hz) (not_lt.2 h2)

theorem continuous_homotopy_integral (hr : 0 < r) (hrR : r < R)
    (hdf : DifferentiableOn ℂ f (ball c R)) (hdg : DifferentiableOn ℂ g (ball c R))
    (hfg : ∀ z ∈ sphere c r, ‖g z‖ < ‖f z‖) :
    Continuous fun t : ℝ => ∮ z in C(c, r),
      (deriv f z + (clamp01 t : ℂ) * deriv g z) / (f z + (clamp01 t : ℂ) * g z) := by
  have hsph : ∀ θ : ℝ, circleMap c r θ ∈ sphere c r := fun θ => circleMap_mem_sphere c hr.le θ
  have hmem : ∀ θ : ℝ, circleMap c r θ ∈ ball c R := fun θ =>
    closedBall_subset_ball hrR (sphere_subset_closedBall (hsph θ))
  have cf : Continuous fun θ => f (circleMap c r θ) :=
    hdf.continuousOn.comp_continuous (continuous_circleMap c r) hmem
  have cg : Continuous fun θ => g (circleMap c r θ) :=
    hdg.continuousOn.comp_continuous (continuous_circleMap c r) hmem
  have cdf : Continuous fun θ => deriv f (circleMap c r θ) :=
    (hdf.deriv isOpen_ball).continuousOn.comp_continuous (continuous_circleMap c r) hmem
  have cdg : Continuous fun θ => deriv g (circleMap c r θ) :=
    (hdg.deriv isOpen_ball).continuousOn.comp_continuous (continuous_circleMap c r) hmem
  unfold circleIntegral
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
  simp only [deriv_circleMap, smul_eq_mul]
  have hcl : Continuous fun p : ℝ × ℝ => ((clamp01 p.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_clamp01.comp continuous_fst)
  have c2 : Continuous fun p : ℝ × ℝ => circleMap 0 r p.2 * I :=
    ((continuous_circleMap 0 r).comp continuous_snd).mul continuous_const
  refine c2.mul (Continuous.div ?_ ?_ ?_)
  · exact (cdf.comp continuous_snd).add (hcl.mul (cdg.comp continuous_snd))
  · exact (cf.comp continuous_snd).add (hcl.mul (cg.comp continuous_snd))
  · intro p
    exact homotopy_ne_zero hfg (clamp01_mem p.1) (hsph p.2)

theorem homotopy_integral_eq (hr : 0 < r) (hrR : r < R)
    (hdf : DifferentiableOn ℂ f (ball c R)) (hdg : DifferentiableOn ℂ g (ball c R))
    (hfg : ∀ z ∈ sphere c r, ‖g z‖ < ‖f z‖) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (∮ z in C(c, r), (deriv f z + (s : ℂ) * deriv g z) / (f z + (s : ℂ) * g z)) =
      2 * π * I * (zeroCount (fun z => f z + (s : ℂ) * g z) c r : ℂ) := by
  have hd : DifferentiableOn ℂ (fun z => f z + (s : ℂ) * g z) (ball c R) :=
    hdf.add (hdg.const_mul _)
  rw [← argument_principle hr hrR hd (fun z hz => homotopy_ne_zero hfg hs hz)]
  refine circleIntegral.integral_congr hr.le fun z hz => ?_
  have hzR : z ∈ ball c R := closedBall_subset_ball hrR (sphere_subset_closedBall hz)
  have h1 : DifferentiableAt ℂ f z := hdf.differentiableAt (isOpen_ball.mem_nhds hzR)
  have h2 : DifferentiableAt ℂ g z := hdg.differentiableAt (isOpen_ball.mem_nhds hzR)
  have : HasDerivAt (fun z => f z + (s : ℂ) * g z) (deriv f z + (s : ℂ) * deriv g z) z :=
    h1.hasDerivAt.add (h2.hasDerivAt.const_mul _)
  rw [this.deriv]

/-- **Теорема Руше** для открытого круга: если `‖g‖ < ‖f‖` на окружности, то `f` и `f + g`
имеют в круге одинаковое число нулей с учётом кратности. -/
theorem rouche_ball (hr : 0 < r) (hrR : r < R)
    (hdf : DifferentiableOn ℂ f (ball c R)) (hdg : DifferentiableOn ℂ g (ball c R))
    (hfg : ∀ z ∈ sphere c r, ‖g z‖ < ‖f z‖) :
    zeroCount f c r = zeroCount (f + g) c r := by
  set n : ℝ → ℕ := fun t => zeroCount (fun z => f z + (clamp01 t : ℂ) * g z) c r with hn
  have hJ := continuous_homotopy_integral hr hrR hdf hdg hfg
  have hk : Continuous fun t : ℝ => ((∮ z in C(c, r),
      (deriv f z + (clamp01 t : ℂ) * deriv g z) / (f z + (clamp01 t : ℂ) * g z)) /
        (2 * π * I)).re := Complex.continuous_re.comp (hJ.div_const _)
  have hpi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have := nat_valued_endpoints hk.continuousOn n (fun t _ => by
    rw [homotopy_integral_eq hr hrR hdf hdg hfg (clamp01_mem t), hn]
    simp only
    rw [mul_div_cancel_left₀ _ hpi]
    simp)
  have e0 : n 0 = zeroCount f c r := by
    simp only [hn, clamp01]; simp
  have e1 : n 1 = zeroCount (f + g) c r := by
    simp only [hn, clamp01]
    simp
    rfl
  rw [← e0, ← e1]
  exact this

/-- **Теорема Руше**: `f`, `g` голоморфны в открытом множестве `U`, содержащем замкнутый круг. -/
theorem rouche {U : Set ℂ} (hU : IsOpen U) (hB : closedBall c r ⊆ U) (hr : 0 < r)
    (hdf : DifferentiableOn ℂ f U) (hdg : DifferentiableOn ℂ g U)
    (hfg : ∀ z ∈ sphere c r, ‖g z‖ < ‖f z‖) :
    zeroCount f c r = zeroCount (f + g) c r := by
  obtain ⟨δ, hδ, hth⟩ := (isCompact_closedBall c r).exists_thickening_subset_open hU hB
  rw [thickening_closedBall hδ hr.le] at hth
  have hsub : ball c (δ + r) ⊆ U := hth
  exact rouche_ball hr (show r < δ + r by linarith) (hdf.mono hsub) (hdg.mono hsub) hfg

theorem zeroCount_eq_sum (hfin : (ball c r ∩ Function.support (zeroMult f)).Finite) :
    zeroCount f c r = ∑ z ∈ hfin.toFinset, zeroMult f z := by
  unfold zeroCount
  rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ hfin]

/-- Следствие (i): если `f` не имеет нулей в круге, то и `f + g` их не имеет. -/
theorem rouche_no_zeros {U : Set ℂ} (hU : IsOpen U) (hB : closedBall c r ⊆ U) (hr : 0 < r)
    (hdf : DifferentiableOn ℂ f U) (hdg : DifferentiableOn ℂ g U)
    (hfg : ∀ z ∈ sphere c r, ‖g z‖ < ‖f z‖) (h0 : ∀ z ∈ ball c r, f z ≠ 0) :
    ∀ z ∈ ball c r, (f + g) z ≠ 0 := by
  have hcount := rouche hU hB hr hdf hdg hfg
  have hf0 : zeroCount f c r = 0 := by
    refine finsum_mem_eq_zero_of_forall_eq_zero fun z hz => ?_
    unfold zeroMult analyticOrderNatAt
    rw [analyticOrderAt_eq_zero.2 (Or.inr (h0 z hz))]
    rfl
  obtain ⟨δ, hδ, hth⟩ := (isCompact_closedBall c r).exists_thickening_subset_open hU hB
  rw [thickening_closedBall hδ hr.le] at hth
  have hsub : ball c (δ + r) ⊆ U := hth
  have hd : DifferentiableOn ℂ (f + g) (ball c (δ + r)) := (hdf.add hdg).mono hsub
  have hs : ∀ z ∈ sphere c r, (f + g) z ≠ 0 := fun z hz h => by
    have h1 : f z = -g z := eq_neg_of_add_eq_zero_left h
    have := hfg z hz
    rw [h1, norm_neg] at this
    exact lt_irrefl _ this
  obtain ⟨p, hpR, hp⟩ := ne_zero_point hr hs (show r < δ + r by linarith)
  have hfin := zeroMult_support_finite (show r < δ + r by linarith) hd hpR hp
  intro z hz h
  have := zeroMult_pos (show r < δ + r by linarith) hd hpR hp hz h
  have h2 := le_zeroCount hfin hz
  omega

/-- Следствие (ii): если у `f` в круге ровно один нуль и он простой, то то же верно для `f + g`. -/
theorem rouche_simple {U : Set ℂ} (hU : IsOpen U) (hB : closedBall c r ⊆ U) (hr : 0 < r)
    (hdf : DifferentiableOn ℂ f U) (hdg : DifferentiableOn ℂ g U)
    (hfg : ∀ z ∈ sphere c r, ‖g z‖ < ‖f z‖) {z₀ : ℂ} (hz₀ : z₀ ∈ ball c r)
    (h0 : f z₀ = 0) (h1 : analyticOrderAt f z₀ = 1)
    (hu : ∀ z ∈ ball c r, f z = 0 → z = z₀) :
    ∃ w ∈ ball c r, (f + g) w = 0 ∧ analyticOrderAt (f + g) w = 1 ∧
      ∀ z ∈ ball c r, (f + g) z = 0 → z = w := by
  have hcount := rouche hU hB hr hdf hdg hfg
  obtain ⟨δ, hδ, hth⟩ := (isCompact_closedBall c r).exists_thickening_subset_open hU hB
  rw [thickening_closedBall hδ hr.le] at hth
  have hsub : ball c (δ + r) ⊆ U := hth
  have hrR : r < δ + r := by linarith
  have hd : DifferentiableOn ℂ (f + g) (ball c (δ + r)) := (hdf.add hdg).mono hsub
  have hs : ∀ z ∈ sphere c r, (f + g) z ≠ 0 := fun z hz h => by
    have h1 : f z = -g z := eq_neg_of_add_eq_zero_left h
    have := hfg z hz
    rw [h1, norm_neg] at this
    exact lt_irrefl _ this
  obtain ⟨p, hpR, hp⟩ := ne_zero_point hr hs hrR
  have hfin := zeroMult_support_finite hrR hd hpR hp
  -- число нулей `f` равно единице
  have hfs : ∀ z ∈ sphere c r, f z ≠ 0 := fun z hz h => by
    have := hfg z hz
    rw [h, norm_zero] at this
    exact absurd this (not_lt.2 (norm_nonneg _))
  obtain ⟨q, hqR, hq⟩ := ne_zero_point hr hfs hrR
  have hdf' : DifferentiableOn ℂ f (ball c (δ + r)) := hdf.mono hsub
  have hfin0 := zeroMult_support_finite hrR hdf' hqR hq
  have hm1 : zeroMult f z₀ = 1 := by
    unfold zeroMult analyticOrderNatAt
    rw [h1]; rfl
  have hc1 : zeroCount f c r = 1 := by
    rw [zeroCount_eq_sum hfin0]
    have : hfin0.toFinset = {z₀} := by
      ext z
      simp only [Set.Finite.mem_toFinset, Set.mem_inter_iff, Function.mem_support,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hz, hne⟩
        exact hu z hz (apply_eq_zero_of_analyticOrderNatAt_ne_zero hne)
      · rintro rfl
        exact ⟨hz₀, by rw [hm1]; exact one_ne_zero⟩
    rw [this, Finset.sum_singleton, hm1]
  rw [hcount, zeroCount_eq_sum hfin] at hc1
  -- единственный нуль `f + g`
  have hpos : ∀ z ∈ hfin.toFinset, 1 ≤ zeroMult (f + g) z := fun z hz => by
    simp only [Set.Finite.mem_toFinset, Set.mem_inter_iff, Function.mem_support] at hz
    exact Nat.one_le_iff_ne_zero.2 hz.2
  have hcard : hfin.toFinset.card ≤ 1 := by
    calc hfin.toFinset.card = ∑ z ∈ hfin.toFinset, 1 := by simp
      _ ≤ ∑ z ∈ hfin.toFinset, zeroMult (f + g) z := Finset.sum_le_sum hpos
      _ = 1 := hc1
  have hne : hfin.toFinset.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.sum_empty] at hc1
    omega
  obtain ⟨w, hw⟩ := Finset.card_eq_one.1 (le_antisymm hcard (Finset.card_pos.2 hne))
  rw [hw, Finset.sum_singleton] at hc1
  have hwm : w ∈ hfin.toFinset := by rw [hw]; exact Finset.mem_singleton_self w
  simp only [Set.Finite.mem_toFinset, Set.mem_inter_iff, Function.mem_support] at hwm
  have hfw := apply_eq_zero_of_analyticOrderNatAt_ne_zero hwm.2
  refine ⟨w, hwm.1, hfw, ?_, fun z hz hzz => ?_⟩
  · have hfinord := analyticOrderAt_ne_top_of_ball hd hpR hp (ball_subset_ball hrR.le hwm.1)
    have : (analyticOrderNatAt (f + g) w : ℕ∞) = analyticOrderAt (f + g) w :=
      Nat.cast_analyticOrderNatAt hfinord
    rw [← this]
    change ((zeroMult (f + g) w : ℕ) : ℕ∞) = 1
    rw [hc1]; rfl
  · have hzm : z ∈ hfin.toFinset := by
      simp only [Set.Finite.mem_toFinset, Set.mem_inter_iff, Function.mem_support]
      exact ⟨hz, zeroMult_pos hrR hd hpR hp hz hzz⟩
    rw [hw] at hzm
    exact Finset.mem_singleton.1 hzm

end

end Involution
