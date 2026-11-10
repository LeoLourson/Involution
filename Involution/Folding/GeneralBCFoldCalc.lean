module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-! # Формула Ньютона–Лейбница для комплекснозначных абсолютно непрерывных функций

Для `AbsolutelyContinuousOnInterval` в Mathlib формула есть только для `ℝ`-значных функций;
здесь она переносится на `ℂ` (по вещественной и мнимой частям), плюс кусочная формула и
абсолютная непрерывность интеграла с переменным верхним пределом. -/

@[expose] public section

open MeasureTheory Set
open scoped Interval

namespace Involution
namespace GeneralBC


theorem ftc_real {f f' : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (f' x) x) :
    IntervalIntegrable f' volume a b ∧ ∫ x in a..b, f' x = f b - f a := by
  have hcongr : (fun x => deriv f x) =ᵐ[volume.restrict (Ι a b)] f' := by
    refine (ae_restrict_iff' measurableSet_uIoc).2 ?_
    filter_upwards [hd] with x hx hxI
    exact (hx (uIoc_subset_uIcc hxI)).deriv
  refine ⟨?_, ?_⟩
  · exact (AbsolutelyContinuousOnInterval.intervalIntegrable_deriv hf).congr_ae hcongr
  · rw [← AbsolutelyContinuousOnInterval.integral_deriv_eq_sub hf]
    exact intervalIntegral.integral_congr_ae (by
      filter_upwards [hd] with x hx hxI
      exact (hx (uIoc_subset_uIcc hxI)).deriv.symm)

theorem intInt_ofReal {g : ℝ → ℝ} {a b : ℝ} (h : IntervalIntegrable g volume a b) :
    IntervalIntegrable (fun x => ((g x : ℝ) : ℂ)) volume a b :=
  ⟨h.1.ofReal, h.2.ofReal⟩

theorem ftc_complex {f f' : ℝ → ℂ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (f' x) x) :
    IntervalIntegrable f' volume a b ∧ ∫ x in a..b, f' x = f b - f a := by
  have hre : AbsolutelyContinuousOnInterval (fun x => (f x).re) a b :=
    Complex.reCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hf
  have him : AbsolutelyContinuousOnInterval (fun x => (f x).im) a b :=
    Complex.imCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hf
  have h1 := ftc_real hre (by
    filter_upwards [hd] with x hx hxI
    exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hx hxI)))
  have h2 := ftc_real him (by
    filter_upwards [hd] with x hx hxI
    exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hx hxI)))
  have hint : IntervalIntegrable f' volume a b := by
    have e : f' = fun x => (((f' x).re : ℝ) : ℂ) + (((f' x).im : ℝ) : ℂ) * Complex.I := by
      funext x; simp [Complex.re_add_im]
    rw [e]
    exact (intInt_ofReal h1.1).add ((intInt_ofReal h2.1).mul_const _)
  refine ⟨hint, ?_⟩
  apply Complex.ext
  · have := Complex.reCLM.intervalIntegral_comp_comm hint
    simp at this
    simpa using this.symm.trans h1.2
  · have := Complex.imCLM.intervalIntegral_comp_comm hint
    simp at this
    simpa using this.symm.trans h2.2


theorem ftc_piecewise {g g' : ℝ → ℂ} (hg : ContinuousOn g (Icc (-1) 1))
    (hd : ∀ x ∈ Ioo (-1 : ℝ) 1, x ≠ 0 → HasDerivAt g (g' x) x)
    (hi : IntervalIntegrable g' volume (-1) 1) :
    ∀ x ∈ Icc (-1 : ℝ) 1, g x = g 0 + ∫ t in (0 : ℝ)..x, g' t := by
  intro x hx
  have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  rcases le_total 0 x with hx0 | hx0
  · have hsub : Icc 0 x ⊆ Icc (-1 : ℝ) 1 := Icc_subset_Icc (by norm_num) hx.2
    have := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hx0 (hg.mono hsub)
      (fun t ht => (hd t ⟨by linarith [ht.1], by linarith [ht.2, hx.2]⟩ ht.1.ne').hasDerivWithinAt)
      (hi.mono_set (by rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1), uIcc_of_le hx0]; exact hsub))
    rw [this]; ring
  · have hsub : Icc x 0 ⊆ Icc (-1 : ℝ) 1 := Icc_subset_Icc hx.1 (by norm_num)
    have := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hx0 (hg.mono hsub)
      (fun t ht => (hd t ⟨by linarith [ht.1, hx.1], by linarith [ht.2]⟩ ht.2.ne).hasDerivWithinAt)
      (hi.mono_set (by rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1), uIcc_of_le hx0]; exact hsub))
    rw [intervalIntegral.integral_symm, this]; ring

theorem ac_integral_complex {g : ℝ → ℂ} {a b c : ℝ} (h : IntervalIntegrable g volume a b)
    (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ v in c..x, g v) a b := by
  have hre : IntervalIntegrable (fun v => (g v).re) volume a b := by
    have := (Complex.reCLM.lipschitzWith)
    exact ⟨h.1.re, h.2.re⟩
  have him : IntervalIntegrable (fun v => (g v).im) volume a b := ⟨h.1.im, h.2.im⟩
  have h1 := hre.absolutelyContinuousOnInterval_intervalIntegral hc
  have h2 := him.absolutelyContinuousOnInterval_intervalIntegral hc
  have h1' := Complex.ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval h1
  have h2' := Complex.ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval h2
  have h3 := h1'.add (h2'.const_smul Complex.I)
  refine h3.congr (fun x hx => ?_)
  have hx' : IntervalIntegrable g volume c x := h.mono_set (uIcc_subset_uIcc hc hx)
  have e1 := Complex.reCLM.intervalIntegral_comp_comm hx'
  have e2 := Complex.imCLM.intervalIntegral_comp_comm hx'
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at e1 e2
  apply Complex.ext <;> simp [e1, e2]

theorem ae_mem_Icc {P : ℝ → Prop} (h : ∀ᵐ x : ℝ, x ∈ Ioo (-1 : ℝ) 1 → P x) :
    ∀ᵐ x : ℝ, x ∈ Icc (-1 : ℝ) 1 → P x := by
  have h1 : ∀ᵐ x : ℝ, x ≠ -1 := (Set.countable_singleton (-1 : ℝ)).ae_notMem _
  have h2 : ∀ᵐ x : ℝ, x ≠ 1 := (Set.countable_singleton (1 : ℝ)).ae_notMem _
  filter_upwards [h, h1, h2] with x hx hx1 hx2 hxI
  exact hx ⟨lt_of_le_of_ne hxI.1 (Ne.symm hx1), lt_of_le_of_ne hxI.2 hx2⟩

theorem ftc_Icc {f f' : ℝ → ℂ} (hf : AbsolutelyContinuousOnInterval f (-1) 1)
    (hd : ∀ᵐ x : ℝ, x ∈ Ioo (-1 : ℝ) 1 → HasDerivAt f (f' x) x)
    {s t : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1) :
    IntervalIntegrable f' volume s t ∧ ∫ x in s..t, f' x = f t - f s := by
  have hsub : uIcc s t ⊆ uIcc (-1 : ℝ) 1 := by
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact uIcc_subset_Icc hs ht
  refine ftc_complex (hf.mono hsub) ?_
  filter_upwards [ae_mem_Icc hd] with x hx hxI
  exact hx (by
    have := hsub hxI
    rwa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at this)

theorem hasDerivAt_of_ftc {g g' : ℝ → ℂ} (hc : ContinuousOn g' (Icc (-1) 1))
    (hg : ∀ x ∈ Icc (-1 : ℝ) 1, g x = g 0 + ∫ t in (0 : ℝ)..x, g' t)
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : HasDerivAt g (g' x) x := by
  have hnhds : Ioo (-1 : ℝ) 1 ∈ nhds x := Ioo_mem_nhds hx.1 hx.2
  have hcx : ContinuousAt g' x := hc.continuousAt (Icc_mem_nhds hx.1 hx.2)
  have hint : IntervalIntegrable g' volume 0 x :=
    (hc.mono (uIcc_subset_Icc (⟨by norm_num, by norm_num⟩ : (0 : ℝ) ∈ Icc (-1 : ℝ) 1)
      (Ioo_subset_Icc_self hx))).intervalIntegrable
  have hsm : StronglyMeasurableAtFilter g' (nhds x) :=
    (hc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx
  have := (intervalIntegral.integral_hasDerivAt_right hint hsm hcx).const_add (g 0)
  refine this.congr_of_eventuallyEq ?_
  filter_upwards [hnhds] with t ht
  exact hg t (Ioo_subset_Icc_self ht)

end GeneralBC
end Involution
