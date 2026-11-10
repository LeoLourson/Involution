module

public import Involution.Folding.GeneralBCSystem
public import Involution.Setup.ComplexAC
public import Involution.Setup.WeakPrimitive

/-! # Свойства коэффициента `a` при (H): знак, оценки, абсолютная непрерывность (G2a, часть (а))

При `HypH a m κ`: `a` непрерывна и знакопостоянна на `[-1,1]`, `eps a * a x > 0`;
`m² ≤ a(x)a(-x) ≤ κ < 1`; `σ_±`, `τ_±`, `k` абсолютно непрерывны на `[0,1]`, отделены от нуля;
`τ_+ < τ_-`. Выкладки (C24 шаг 5) опираются на соотношения `k a = √p`, `k² a = a(-·)`. -/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Involution.GeneralBC
section Sign
variable {a : ℝ → ℝ} {m κ : ℝ}

theorem HypH.continuousOn (h : HypH a m κ) : ContinuousOn a (Icc (-1) 1) := by
  simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using h.ac.continuousOn

theorem HypH.ne_zero (h : HypH a m κ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : a x ≠ 0 := by
  intro h0
  have := h.lower x hx
  rw [h0] at this
  simp at this
  linarith [h.m_pos]

theorem HypH.mul_pos' (h : HypH a m κ) {x y : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1)
    (hy : y ∈ Icc (-1 : ℝ) 1) : 0 < a x * a y := by
  by_contra hcon
  have hcon := not_lt.1 hcon
  have hsub : uIcc x y ⊆ Icc (-1) 1 := uIcc_subset_Icc hx hy
  have hmem : (0 : ℝ) ∈ uIcc (a x) (a y) := by
    rw [mem_uIcc]
    rcases lt_or_gt_of_ne (h.ne_zero hx) with h1 | h1 <;>
      rcases lt_or_gt_of_ne (h.ne_zero hy) with h2 | h2
    · exact absurd (mul_pos_of_neg_of_neg h1 h2) (not_lt.2 hcon)
    · exact Or.inl ⟨h1.le, h2.le⟩
    · exact Or.inr ⟨h2.le, h1.le⟩
    · exact absurd (mul_pos h1 h2) (not_lt.2 hcon)
  obtain ⟨z, hz, hz0⟩ := intermediate_value_uIcc ((h.continuousOn).mono hsub) hmem
  exact h.ne_zero (hsub hz) hz0

theorem HypH.eps_mul_pos (h : HypH a m κ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 < eps a * a x := by
  have h0 := h.mul_pos' (x := 0) (y := x) (by simp) hx
  unfold eps
  split_ifs with hp
  · simpa using (pos_iff_pos_of_mul_pos h0).1 hp
  · have : a 0 < 0 := lt_of_le_of_ne (not_lt.1 hp) (h.ne_zero (by simp))
    have := neg_of_mul_pos_right h0 this.le
    linarith

theorem eps_mul_eps (a : ℝ → ℝ) : eps a * eps a = 1 := by
  unfold eps; split_ifs <;> norm_num

theorem abs_eps (a : ℝ → ℝ) : |eps a| = 1 := by
  unfold eps; split_ifs <;> norm_num

theorem eps_ne_zero (a : ℝ → ℝ) : eps a ≠ 0 := by
  unfold eps; split_ifs <;> norm_num

theorem HypH.abs_eq (h : HypH a m κ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |a x| = eps a * a x := by
  have h1 := abs_of_pos (h.eps_mul_pos hx)
  rw [abs_mul, abs_eps, one_mul] at h1
  exact h1

theorem neg_mem_Icc_one {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : -x ∈ Icc (-1 : ℝ) 1 :=
  ⟨by linarith [hx.2], by linarith [hx.1]⟩

theorem HypH.sq_le (h : HypH a m κ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    m ^ 2 ≤ a x * a (-x) := by
  have hp := h.mul_pos' hx (neg_mem_Icc_one hx)
  rw [← abs_of_pos hp, abs_mul, sq]
  exact mul_le_mul (h.lower x hx) (h.lower _ (neg_mem_Icc_one hx)) h.m_pos.le (abs_nonneg _)

theorem HypH.sq_le_kappa (h : HypH a m κ) : m ^ 2 ≤ κ :=
  (h.sq_le (x := 0) (by simp)).trans (h.upper 0 (by simp))

theorem HypH.pos_p (h : HypH a m κ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : 0 < a x * a (-x) :=
  h.mul_pos' hx (neg_mem_Icc_one hx)

theorem HypH.kappa_pos (h : HypH a m κ) : 0 < κ :=
  lt_of_lt_of_le (pow_pos h.m_pos 2) h.sq_le_kappa

theorem HypH.sqrtK_lt_one (h : HypH a m κ) : Real.sqrt κ < 1 := by
  rw [Real.sqrt_lt' one_pos]; simpa using h.kappa_lt

theorem HypH.sqrtK_pos (h : HypH a m κ) : 0 < Real.sqrt κ := Real.sqrt_pos.2 h.kappa_pos

theorem HypH.m_le_sqrt (h : HypH a m κ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    m ≤ Real.sqrt (a x * a (-x)) :=
  Real.le_sqrt_of_sq_le (h.sq_le hx)

theorem HypH.sqrt_le (h : HypH a m κ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    Real.sqrt (a x * a (-x)) ≤ Real.sqrt κ :=
  Real.sqrt_le_sqrt (h.upper x hx)

theorem HypH.sqrt_pos' (h : HypH a m κ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 < Real.sqrt (a x * a (-x)) := lt_of_lt_of_le h.m_pos (h.m_le_sqrt hx)

theorem HypH.sqrt_lt_one (h : HypH a m κ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    Real.sqrt (a x * a (-x)) < 1 := (h.sqrt_le hx).trans_lt h.sqrtK_lt_one

theorem HypH.sigma_ge (h : HypH a m κ) {s : ℝ} (hs : s = 1 ∨ s = -1) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) : 1 - Real.sqrt κ ≤ sigma a s x := by
  have := h.sqrt_le hx
  have := h.sqrt_pos' hx
  unfold sigma
  rcases hs with rfl | rfl <;> nlinarith [h.sqrtK_pos]

theorem HypH.sigma_le (h : HypH a m κ) {s : ℝ} (hs : s = 1 ∨ s = -1) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) : sigma a s x ≤ 1 + Real.sqrt κ := by
  have := h.sqrt_le hx
  have := h.sqrt_pos' hx
  unfold sigma
  rcases hs with rfl | rfl <;> nlinarith [h.sqrtK_pos]

theorem HypH.sigma_pos (h : HypH a m κ) {s : ℝ} (hs : s = 1 ∨ s = -1) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) : 0 < sigma a s x := by
  have := h.sigma_ge hs hx
  linarith [h.sqrtK_lt_one]

theorem HypH.tau_pos (h : HypH a m κ) {s : ℝ} (hs : s = 1 ∨ s = -1) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) : 0 < tau a s x := by
  unfold tau
  exact inv_pos.2 (Real.sqrt_pos.2 (h.sigma_pos hs hx))

theorem HypH.tau_sq_mul (h : HypH a m κ) {s : ℝ} (hs : s = 1 ∨ s = -1) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) : tau a s x ^ 2 * sigma a s x = 1 := by
  unfold tau
  have hp := h.sigma_pos hs hx
  rw [inv_pow, Real.sq_sqrt hp.le]
  exact inv_mul_cancel₀ hp.ne'

theorem HypH.tau_lt (h : HypH a m κ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    tau a 1 x < tau a (-1) x := by
  unfold tau
  have hp1 := h.sigma_pos (Or.inl rfl) hx
  have hp2 := h.sigma_pos (Or.inr rfl) hx
  have hlt : sigma a (-1) x < sigma a 1 x := by
    unfold sigma; have := h.sqrt_pos' hx; linarith
  exact (inv_lt_inv₀ (Real.sqrt_pos.2 hp1) (Real.sqrt_pos.2 hp2)).2
    (Real.sqrt_lt_sqrt hp2.le hlt)

theorem HypH.tau_ge (h : HypH a m κ) {s : ℝ} (hs : s = 1 ∨ s = -1) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) : (Real.sqrt (1 + Real.sqrt κ))⁻¹ ≤ tau a s x := by
  unfold tau
  exact (inv_le_inv₀ (Real.sqrt_pos.2 (by linarith [h.sqrtK_pos]))
    (Real.sqrt_pos.2 (h.sigma_pos hs hx))).2 (Real.sqrt_le_sqrt (h.sigma_le hs hx))

theorem HypH.tau_le (h : HypH a m κ) {s : ℝ} (hs : s = 1 ∨ s = -1) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) : tau a s x ≤ (Real.sqrt (1 - Real.sqrt κ))⁻¹ := by
  unfold tau
  exact (inv_le_inv₀ (Real.sqrt_pos.2 (h.sigma_pos hs hx))
    (Real.sqrt_pos.2 (by linarith [h.sqrtK_lt_one]))).2 (Real.sqrt_le_sqrt (h.sigma_ge hs hx))

end Sign

section AC
variable {a : ℝ → ℝ} {m κ : ℝ}

theorem ac_neg_comp {f : ℝ → ℝ} (hf : AbsolutelyContinuousOnInterval f (-1) 1) :
    AbsolutelyContinuousOnInterval (fun x => f (-x)) 0 1 := by
  have hint : IntervalIntegrable (deriv f) volume (-1) 1 := hf.intervalIntegrable_deriv
  have hg1 : IntervalIntegrable (fun t => deriv f (-t)) volume 1 (-1) := by
    have := (IntervalIntegrable.iff_comp_neg (a := -1) (b := 1) (f := deriv f)).mp hint
    simpa using this
  have hg : IntervalIntegrable (fun t => deriv f (-t)) volume 0 1 :=
    (hg1.symm).mono_set (by
      rw [uIcc_of_le (by norm_num), uIcc_of_le (by norm_num)]
      intro t ht; exact ⟨by linarith [ht.1], ht.2⟩)
  have hac := hg.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
  have hac2 : AbsolutelyContinuousOnInterval
      (fun x => (f (-1) + ∫ v in (0 : ℝ)..1, deriv f (-v)) -
        ∫ v in (0 : ℝ)..x, deriv f (-v)) 0 1 := by
    have hc : AbsolutelyContinuousOnInterval
        (fun _ : ℝ => f (-1) + ∫ v in (0 : ℝ)..1, deriv f (-v)) 0 1 :=
      (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
    exact hc.fun_sub hac
  refine hac2.congr ?_
  intro x hx
  rw [uIcc_of_le (by norm_num)] at hx
  have hxint : IntervalIntegrable (fun t => deriv f (-t)) volume x 1 :=
    hg.mono_set (by
      rw [uIcc_of_le hx.2, uIcc_of_le (by norm_num)]
      intro t ht; exact ⟨by linarith [ht.1, hx.1], ht.2⟩)
  have h0x : IntervalIntegrable (fun t => deriv f (-t)) volume 0 x :=
    hg.mono_set (by
      rw [uIcc_of_le hx.1, uIcc_of_le (by norm_num)]
      intro t ht; exact ⟨ht.1, by linarith [ht.2, hx.2]⟩)
  have h1 := (hf.mono (c := -1) (d := -x) (by
      rw [uIcc_of_le (show (-1 : ℝ) ≤ -x by linarith [hx.2]),
        uIcc_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]
      intro t ht; exact ⟨ht.1, by linarith [ht.2, hx.1]⟩)).integral_deriv_eq_sub
  have h2 := intervalIntegral.integral_comp_neg (a := x) (b := 1) (deriv f)
  have h3 := intervalIntegral.integral_interval_sub_left hg h0x
  try simp only [neg_neg] at h2
  linarith

theorem ac_comp_cd {f g : ℝ → ℝ} {c d : ℝ} (hf : ContDiffOn ℝ 1 f (Icc c d))
    (hg : AbsolutelyContinuousOnInterval g 0 1) (hmem : ∀ x ∈ Icc (0 : ℝ) 1, g x ∈ Icc c d) :
    AbsolutelyContinuousOnInterval (fun x => f (g x)) 0 1 := by
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith (by decide) (convex_Icc _ _) isCompact_Icc
  exact hK.comp_absolutelyContinuousOnInterval (g := g)
    (fun x hx => hmem x (by simpa [uIcc_of_le (zero_le_one' ℝ)] using hx)) hg

theorem contDiffOn_sqrt_Icc {c d : ℝ} (hc : 0 < c) :
    ContDiffOn ℝ 1 (fun x : ℝ => Real.sqrt x) (Icc c d) :=
  fun _ hx => (Real.contDiffAt_sqrt (ne_of_gt (lt_of_lt_of_le hc hx.1))).contDiffWithinAt

theorem contDiffOn_inv_Icc {c d : ℝ} (hc : 0 < c) :
    ContDiffOn ℝ 1 (fun x : ℝ => x⁻¹) (Icc c d) :=
  fun _ hx => (contDiffAt_inv ℝ (ne_of_gt (lt_of_lt_of_le hc hx.1))).contDiffWithinAt

theorem HypH.ac_half (h : HypH a m κ) : AbsolutelyContinuousOnInterval a 0 1 :=
  h.ac.mono (by
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1), uIcc_of_le (zero_le_one' ℝ)]
    exact Icc_subset_Icc (by norm_num) le_rfl)

theorem HypH.ac_neg (h : HypH a m κ) :
    AbsolutelyContinuousOnInterval (fun x => a (-x)) 0 1 := ac_neg_comp h.ac

theorem HypH.ac_p (h : HypH a m κ) :
    AbsolutelyContinuousOnInterval (fun x => a x * a (-x)) 0 1 := by
  have := h.ac_half.smul h.ac_neg
  exact this

theorem mem_Icc_neg_one_of_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : x ∈ Icc (-1 : ℝ) 1 :=
  ⟨by linarith [hx.1], hx.2⟩

theorem HypH.ac_rp (h : HypH a m κ) :
    AbsolutelyContinuousOnInterval (fun x => Real.sqrt (a x * a (-x))) 0 1 :=
  ac_comp_cd (contDiffOn_sqrt_Icc (c := m ^ 2) (d := κ) (pow_pos h.m_pos 2)) h.ac_p
    (fun x hx => ⟨h.sq_le (mem_Icc_neg_one_of_mem hx), h.upper x (mem_Icc_neg_one_of_mem hx)⟩)

theorem HypH.ac_sigma (h : HypH a m κ) (s : ℝ) :
    AbsolutelyContinuousOnInterval (sigma a s) 0 1 := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) 0 1 :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  exact hc.fun_add (h.ac_rp.const_mul s)

theorem HypH.ac_tau (h : HypH a m κ) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    AbsolutelyContinuousOnInterval (tau a s) 0 1 := by
  have hlo : 0 < 1 - Real.sqrt κ := by linarith [h.sqrtK_lt_one]
  have h1 : AbsolutelyContinuousOnInterval (fun x => Real.sqrt (sigma a s x)) 0 1 :=
    ac_comp_cd (contDiffOn_sqrt_Icc (c := 1 - Real.sqrt κ) (d := 1 + Real.sqrt κ) hlo)
      (h.ac_sigma s) (fun x hx => ⟨h.sigma_ge hs (mem_Icc_neg_one_of_mem hx),
        h.sigma_le hs (mem_Icc_neg_one_of_mem hx)⟩)
  change AbsolutelyContinuousOnInterval (fun x => (Real.sqrt (sigma a s x))⁻¹) 0 1
  exact ac_comp_cd (f := fun y : ℝ => y⁻¹) (contDiffOn_inv_Icc (c := Real.sqrt (1 - Real.sqrt κ))
      (d := Real.sqrt (1 + Real.sqrt κ)) (Real.sqrt_pos.2 hlo)) h1
    (fun x hx => ⟨Real.sqrt_le_sqrt (h.sigma_ge hs (mem_Icc_neg_one_of_mem hx)),
      Real.sqrt_le_sqrt (h.sigma_le hs (mem_Icc_neg_one_of_mem hx))⟩)

end AC

section Kfun
variable {a : ℝ → ℝ} {m κ : ℝ}

theorem HypH.exists_bound (h : HypH a m κ) : ∃ B : ℝ, m ≤ B ∧ ∀ x ∈ Icc (-1 : ℝ) 1, |a x| ≤ B := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn h.continuousOn
  refine ⟨max C m, le_max_right _ _, fun x hx => ?_⟩
  exact (by simpa using hC x hx : |a x| ≤ C).trans (le_max_left _ _)

theorem HypH.ratio_pos (h : HypH a m κ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 < a (-x) / a x := by
  have hx0 := h.ne_zero hx
  have hp := h.pos_p hx
  have : a (-x) / a x = (a x * a (-x)) / (a x) ^ 2 := by field_simp
  rw [this]
  exact div_pos hp (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hx0)))

theorem HypH.kfun_sq (h : HypH a m κ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    kfun a x ^ 2 * a x = a (-x) := by
  have hx0 := h.ne_zero hx
  unfold kfun
  rw [mul_pow, Real.sq_sqrt (h.ratio_pos hx).le, sq, eps_mul_eps, one_mul]
  field_simp

theorem HypH.kfun_mul_a (h : HypH a m κ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    kfun a x * a x = Real.sqrt (a x * a (-x)) := by
  have hx0 := h.ne_zero hx
  have he := h.eps_mul_pos hx
  have : a x * a (-x) = (eps a * a x) ^ 2 * (a (-x) / a x) := by
    have e2 : eps a ^ 2 = 1 := by rw [sq]; exact eps_mul_eps a
    rw [mul_pow, e2]
    field_simp
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq he.le]
  unfold kfun
  ring

theorem ratio_eq (a : ℝ → ℝ) (x : ℝ) :
    a (-x) / a x = (eps a * a (-x)) * (eps a * a x)⁻¹ := by
  by_cases hx : a x = 0
  · simp [hx]
  · have := eps_ne_zero a
    field_simp

theorem HypH.ratio_bounds (h : HypH a m κ) {B : ℝ} (hB : ∀ x ∈ Icc (-1 : ℝ) 1, |a x| ≤ B)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : m / B ≤ a (-x) / a x ∧ a (-x) / a x ≤ B / m := by
  have hx' := neg_mem_Icc_one hx
  have e1 := h.abs_eq hx
  have e2 := h.abs_eq hx'
  have hr : a (-x) / a x = |a (-x)| / |a x| := by
    rw [e1, e2, mul_div_mul_left _ _ (eps_ne_zero a)]
  rw [hr]
  have h1 := h.lower x hx
  have h2 := h.lower _ hx'
  have h3 := hB x hx
  have h4 := hB _ hx'
  have hm := h.m_pos
  have hBpos : 0 < B := lt_of_lt_of_le hm (h1.trans h3)
  constructor
  · rw [div_le_div_iff₀ hBpos (lt_of_lt_of_le hm h1)]
    nlinarith
  · rw [div_le_div_iff₀ (lt_of_lt_of_le hm h1) hm]
    nlinarith

theorem HypH.ac_kfun (h : HypH a m κ) : AbsolutelyContinuousOnInterval (kfun a) 0 1 := by
  obtain ⟨B, hmB, hB⟩ := h.exists_bound
  have hm := h.m_pos
  have hBpos : 0 < B := lt_of_lt_of_le hm hmB
  have hH : AbsolutelyContinuousOnInterval (fun x => eps a * a x) 0 1 :=
    h.ac_half.const_mul _
  have hG : AbsolutelyContinuousOnInterval (fun x => eps a * a (-x)) 0 1 :=
    h.ac_neg.const_mul _
  have hHm : ∀ x ∈ Icc (0 : ℝ) 1, eps a * a x ∈ Icc m B := fun x hx => by
    have hx' := mem_Icc_neg_one_of_mem hx
    rw [← h.abs_eq hx']
    exact ⟨h.lower x hx', hB x hx'⟩
  have hinv : AbsolutelyContinuousOnInterval (fun x => (eps a * a x)⁻¹) 0 1 :=
    ac_comp_cd (f := fun y : ℝ => y⁻¹) (contDiffOn_inv_Icc (c := m) (d := B) hm) hH hHm
  have hr : AbsolutelyContinuousOnInterval (fun x => a (-x) / a x) 0 1 := by
    have := hG.fun_mul hinv
    simpa [ratio_eq] using this
  have hs : AbsolutelyContinuousOnInterval (fun x => Real.sqrt (a (-x) / a x)) 0 1 :=
    ac_comp_cd (contDiffOn_sqrt_Icc (c := m / B) (d := B / m) (div_pos hm hBpos)) hr
      (fun x hx => h.ratio_bounds hB (mem_Icc_neg_one_of_mem hx))
  exact hs.const_mul (eps a)

theorem HypH.kfun_abs_bounds (h : HypH a m κ) :
    ∃ c C : ℝ, 0 < c ∧ ∀ x ∈ Icc (-1 : ℝ) 1, c ≤ |kfun a x| ∧ |kfun a x| ≤ C := by
  obtain ⟨B, hmB, hB⟩ := h.exists_bound
  have hm := h.m_pos
  have hBpos : 0 < B := lt_of_lt_of_le hm hmB
  refine ⟨Real.sqrt (m / B), Real.sqrt (B / m), Real.sqrt_pos.2 (div_pos hm hBpos), fun x hx => ?_⟩
  have hb := h.ratio_bounds hB hx
  have habs : |kfun a x| = Real.sqrt (a (-x) / a x) := by
    unfold kfun
    rw [abs_mul, abs_eps, one_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [habs]
  exact ⟨Real.sqrt_le_sqrt hb.1, Real.sqrt_le_sqrt hb.2⟩

theorem HypH.kfun_ne_zero (h : HypH a m κ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : kfun a x ≠ 0 := by
  obtain ⟨c, C, hc, hb⟩ := h.kfun_abs_bounds
  intro h0
  have := (hb x hx).1
  rw [h0] at this
  simp at this
  linarith


end Kfun

end Involution.GeneralBC
