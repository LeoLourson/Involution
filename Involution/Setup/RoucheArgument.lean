module

public import Involution.Setup.RoucheZeros
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Algebra.BigOperators.Finprod

/-! Принцип аргумента для круга: `(2πi)⁻¹ ∮ f'/f = число нулей с кратностью`. -/

@[expose] public noncomputable section

open Metric Set Filter Topology Complex
open scoped Real

namespace Involution

/-- Число нулей `f` в открытом круге `ball c r` с учётом кратности. -/
def zeroCount (f : ℂ → ℂ) (c : ℂ) (r : ℝ) : ℕ := ∑ᶠ z ∈ ball c r, zeroMult f z

section

variable {f : ℂ → ℂ} {c : ℂ} {r R : ℝ}

theorem ne_zero_point (hr : 0 < r) (hs : ∀ z ∈ sphere c r, f z ≠ 0) (hrR : r < R) :
    ∃ z₀ ∈ ball c R, f z₀ ≠ 0 := by
  refine ⟨c + r, ?_, hs _ ?_⟩
  · simp [abs_of_pos hr, hrR]
  · simp [abs_of_pos hr]

theorem zeroMult_support_finite (hrR : r < R) (hd : DifferentiableOn ℂ f (ball c R))
    {z₀ : ℂ} (hz₀ : z₀ ∈ ball c R) (hf : f z₀ ≠ 0) :
    (ball c r ∩ Function.support (zeroMult f)).Finite := by
  refine (zeros_finite hrR hd hz₀ hf).subset fun z hz => ?_
  refine ⟨ball_subset_closedBall hz.1, ?_⟩
  exact apply_eq_zero_of_analyticOrderNatAt_ne_zero hz.2

theorem le_zeroCount (hfin : (ball c r ∩ Function.support (zeroMult f)).Finite)
    {z : ℂ} (hz : z ∈ ball c r) : zeroMult f z ≤ zeroCount f c r := by
  unfold zeroCount
  rw [finsum_mem_def]
  have hsup : Function.support ((ball c r).indicator (zeroMult f)) =
      ball c r ∩ Function.support (zeroMult f) := by
    rw [Set.support_indicator, Set.inter_comm]
  have := single_le_finsum z (f := (ball c r).indicator (zeroMult f))
    (by unfold Function.HasFiniteSupport; rw [hsup]; exact hfin) (fun _ => Nat.zero_le _)
  simpa [Set.indicator_of_mem hz] using this

theorem zeroMult_pos (hrR : r < R) (hd : DifferentiableOn ℂ f (ball c R))
    {z₀ : ℂ} (hz₀ : z₀ ∈ ball c R) (hf : f z₀ ≠ 0) {z : ℂ} (hz : z ∈ ball c r)
    (h0 : f z = 0) : zeroMult f z ≠ 0 := by
  have hzR : z ∈ ball c R := ball_subset_ball hrR.le hz
  have hfin := analyticOrderAt_ne_top_of_ball hd hz₀ hf hzR
  have han := (hd.analyticOnNhd isOpen_ball) z hzR
  have hne : analyticOrderAt f z ≠ 0 := analyticOrderAt_ne_zero.2 ⟨han, h0⟩
  intro h
  unfold zeroMult analyticOrderNatAt at h
  rcases ENat.toNat_eq_zero.1 h with h | h
  · exact hne h
  · exact hfin h

theorem circleIntegral_logDeriv_eq_zero (hr : 0 < r) (hrR : r < R)
    (hd : DifferentiableOn ℂ f (ball c R)) (hnz : ∀ z ∈ closedBall c r, f z ≠ 0) :
    (∮ z in C(c, r), deriv f z / f z) = 0 := by
  have hsub : closedBall c r ⊆ ball c R := closedBall_subset_ball hrR
  have hd' : DifferentiableOn ℂ (deriv f) (ball c R) := hd.deriv isOpen_ball
  refine circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le
    (Set.countable_empty) ?_ ?_
  · exact (hd'.continuousOn.mono hsub).div (hd.continuousOn.mono hsub) hnz
  · intro z hz
    have hzR : z ∈ ball c R := hsub (ball_subset_closedBall hz.1)
    have h1 : DifferentiableAt ℂ (deriv f) z := hd'.differentiableAt (isOpen_ball.mem_nhds hzR)
    have h2 : DifferentiableAt ℂ f z := hd.differentiableAt (isOpen_ball.mem_nhds hzR)
    exact h1.div h2 (hnz z (ball_subset_closedBall hz.1))

theorem dslope_factor {z₀ : ℂ} (h0 : f z₀ = 0) (z : ℂ) : f z = (z - z₀) * dslope f z₀ z := by
  have := sub_smul_dslope f z₀ z
  rw [h0, sub_zero, smul_eq_mul] at this
  exact this.symm

theorem zeroMult_factor (hd : DifferentiableOn ℂ f (ball c R)) {z₀ : ℂ} (h0 : f z₀ = 0)
    (hz₀ : z₀ ∈ ball c R) {w : ℂ} (hw : w ∈ ball c R)
    {p : ℂ} (hp : p ∈ ball c R) (hgp : dslope f z₀ p ≠ 0) :
    zeroMult f w = (if w = z₀ then 1 else 0) + zeroMult (dslope f z₀) w := by
  have hg : DifferentiableOn ℂ (dslope f z₀) (ball c R) :=
    (differentiableOn_dslope (isOpen_ball.mem_nhds hz₀)).2 hd
  have hfe : f = (fun z => z - z₀) * dslope f z₀ := funext (dslope_factor h0)
  have han : AnalyticAt ℂ (fun z => z - z₀) w := by fun_prop
  have hgan : AnalyticAt ℂ (dslope f z₀) w := (hg.analyticOnNhd isOpen_ball) w hw
  have hfin := analyticOrderAt_ne_top_of_ball hg hp hgp hw
  have h1 : analyticOrderAt (fun z => z - z₀) w ≠ ⊤ := by
    by_cases h : w = z₀
    · subst h; simp
    · rw [analyticOrderAt_id_sub_const_of_ne h]; simp
  have e : zeroMult f w = analyticOrderNatAt ((fun z => z - z₀) * dslope f z₀) w := by
    rw [← hfe]
  rw [e, analyticOrderNatAt_mul han hgan h1 hfin]
  congr 1
  by_cases h : w = z₀
  · subst h; simp [analyticOrderNatAt]
  · simp [h, analyticOrderNatAt, analyticOrderAt_id_sub_const_of_ne h]

theorem zeroCount_factor (hr : 0 < r) (hrR : r < R) (hd : DifferentiableOn ℂ f (ball c R))
    (hs : ∀ z ∈ sphere c r, f z ≠ 0) {z₀ : ℂ} (h0 : f z₀ = 0) (hz₀ : z₀ ∈ ball c r) :
    zeroCount f c r = zeroCount (dslope f z₀) c r + 1 := by
  have hz₀R : z₀ ∈ ball c R := ball_subset_ball hrR.le hz₀
  have hg : DifferentiableOn ℂ (dslope f z₀) (ball c R) :=
    (differentiableOn_dslope (isOpen_ball.mem_nhds hz₀R)).2 hd
  have hgs : ∀ z ∈ sphere c r, dslope f z₀ z ≠ 0 := fun z hz h => by
    have := dslope_factor h0 z
    rw [h, mul_zero] at this
    exact hs z hz this
  obtain ⟨p, hpR, hp⟩ := ne_zero_point hr hgs hrR
  have hgfin := zeroMult_support_finite hrR hg hpR hp
  have hmem : ∀ z ∈ ball c r, zeroMult f z =
      (if z = z₀ then 1 else 0) + zeroMult (dslope f z₀) z := fun z hz =>
    zeroMult_factor hd h0 hz₀R (ball_subset_ball hrR.le hz) hpR hp
  have hite : (ball c r ∩ Function.support fun z => if z = z₀ then 1 else 0).Finite := by
    refine (Set.finite_singleton z₀).subset fun z hz => ?_
    by_contra h
    exact hz.2 (by simp [Set.mem_singleton_iff.not.1 h |> fun h' => h'])
  unfold zeroCount
  rw [finsum_mem_congr rfl hmem, finsum_mem_add_distrib' hite hgfin]
  rw [add_comm]
  congr 1
  rw [← finsum_mem_inter_support]
  have : ball c r ∩ (Function.support fun z => if z = z₀ then (1 : ℕ) else 0) = {z₀} := by
    ext z
    by_cases h : z = z₀
    · subst h; simp [hz₀]
    · simp [h]
  rw [this, finsum_mem_singleton]
  simp

theorem circleIntegral_logDeriv_aux (hr : 0 < r) (hrR : r < R) :
    ∀ (N : ℕ) (f : ℂ → ℂ), DifferentiableOn ℂ f (ball c R) → (∀ z ∈ sphere c r, f z ≠ 0) →
      zeroCount f c r = N → (∮ z in C(c, r), deriv f z / f z) = 2 * π * I * N := by
  intro N
  induction N with
  | zero =>
    intro f hd hs hN
    obtain ⟨p, hpR, hp⟩ := ne_zero_point hr hs hrR
    have hfin := zeroMult_support_finite hrR hd hpR hp
    rw [circleIntegral_logDeriv_eq_zero hr hrR hd, Nat.cast_zero, mul_zero]
    intro z hz
    rcases (mem_closedBall.1 hz).lt_or_eq with h | h
    · intro h0
      exact zeroMult_pos hrR hd hpR hp (mem_ball.2 h) h0
        (Nat.le_zero.1 (hN ▸ le_zeroCount hfin (mem_ball.2 h)))
    · exact hs z (mem_sphere.2 h)
  | succ N ih =>
    intro f hd hs hN
    obtain ⟨p, hpR, hp⟩ := ne_zero_point hr hs hrR
    have hfin := zeroMult_support_finite hrR hd hpR hp
    obtain ⟨z₀, hz₀, hm⟩ : ∃ z₀ ∈ ball c r, zeroMult f z₀ ≠ 0 := by
      by_contra h
      push Not at h
      have : zeroCount f c r = 0 := finsum_mem_eq_zero_of_forall_eq_zero h
      omega
    have h0 : f z₀ = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hm
    have hz₀R : z₀ ∈ ball c R := ball_subset_ball hrR.le hz₀
    have hg : DifferentiableOn ℂ (dslope f z₀) (ball c R) :=
      (differentiableOn_dslope (isOpen_ball.mem_nhds hz₀R)).2 hd
    have hgs : ∀ z ∈ sphere c r, dslope f z₀ z ≠ 0 := fun z hz h => by
      have := dslope_factor h0 z
      rw [h, mul_zero] at this
      exact hs z hz this
    have hcount := zeroCount_factor hr hrR hd hs h0 hz₀
    have hIH := ih _ hg hgs (by omega)
    have hsph : ∀ z ∈ sphere c r, deriv f z / f z =
        (z - z₀)⁻¹ + deriv (dslope f z₀) z / dslope f z₀ z := by
      intro z hz
      have hzR : z ∈ ball c R := closedBall_subset_ball hrR (sphere_subset_closedBall hz)
      have hne : z - z₀ ≠ 0 := by
        intro h
        have : z = z₀ := sub_eq_zero.1 h
        subst this
        exact (mem_ball.1 hz₀).ne (mem_sphere.1 hz)
      have hgz := hgs z hz
      have hdg : DifferentiableAt ℂ (dslope f z₀) z :=
        hg.differentiableAt (isOpen_ball.mem_nhds hzR)
      have hfe : f = (fun z => z - z₀) * dslope f z₀ := funext (dslope_factor h0)
      have hder : deriv f z = dslope f z₀ z + (z - z₀) * deriv (dslope f z₀) z := by
        conv_lhs => rw [hfe]
        rw [deriv_mul (by fun_prop) hdg]
        simp [mul_comm]
      rw [hder, dslope_factor h0 z]
      field_simp
    have hc1 : CircleIntegrable (fun z => (z - z₀)⁻¹) c r :=
      circleIntegrable_sub_inv_iff.2 (Or.inr (by
        rw [abs_of_pos hr]; intro h; exact (mem_ball.1 hz₀).ne (mem_sphere.1 h)))
    have hc2 : CircleIntegrable (fun z => deriv (dslope f z₀) z / dslope f z₀ z) c r := by
      refine ContinuousOn.circleIntegrable hr.le ?_
      have hsub : sphere c r ⊆ ball c R :=
        sphere_subset_closedBall.trans (closedBall_subset_ball hrR)
      have hd' : DifferentiableOn ℂ (deriv (dslope f z₀)) (ball c R) := hg.deriv isOpen_ball
      exact (hd'.continuousOn.mono hsub).div (hg.continuousOn.mono hsub) hgs
    rw [circleIntegral.integral_congr hr.le hsph, circleIntegral.integral_add hc1 hc2,
      circleIntegral.integral_sub_inv_of_mem_ball hz₀, hIH]
    push_cast
    ring

/-- **Принцип аргумента для круга**: `(2πi)⁻¹ ∮ f'/f` равно числу нулей с кратностью. -/
theorem argument_principle (hr : 0 < r) (hrR : r < R) (hd : DifferentiableOn ℂ f (ball c R))
    (hs : ∀ z ∈ sphere c r, f z ≠ 0) :
    (∮ z in C(c, r), deriv f z / f z) = 2 * π * I * (zeroCount f c r : ℂ) :=
  circleIntegral_logDeriv_aux hr hrR _ f hd hs rfl

end

end Involution
