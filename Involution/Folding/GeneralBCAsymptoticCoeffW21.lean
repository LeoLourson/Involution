module

public import Involution.Folding.GeneralBCAsymptoticCoeffTransfer

/-! # `Ã` при `a ∈ W²₁`: абсолютная непрерывность (G2a, часть (б))

Явные формулы производных `k'`, `τ_±'` через `a'` (`kD`, `tauD`), совпадающие с `deriv` п.в.;
`HypH.Atilde_offdiag_ac`: при `IsW21 a` существует матрица `B` с абсолютно непрерывными
элементами, равная `Atilde a x` почти всюду на `[0,1]` (диагональ нулевая). Равенство только п.в.:
`deriv` в точках недифференцируемости произвольно. -/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Involution.GeneralBC
section W21
variable {a : ℝ → ℝ} {m κ : ℝ}

/-- `rD`: производная `√(a(x)a(-x))` через `a'`. -/
def rD (a a' : ℝ → ℝ) (x : ℝ) : ℝ :=
  (a' x * a (-x) + a x * (a' (-x) * -1)) / (2 * Real.sqrt (a x * a (-x)))

/-- `kD`: производная `k` через `a'`. -/
def kD (a a' : ℝ → ℝ) (x : ℝ) : ℝ :=
  eps a * ((((a' (-x) * -1) * a x - a (-x) * a' x) / a x ^ 2) /
    (2 * Real.sqrt (a (-x) / a x)))

/-- `τD`: производная `τ_s` через `a'`. -/
def tauD (a a' : ℝ → ℝ) (s : ℝ) (x : ℝ) : ℝ :=
  -((s * rD a a' x) / (2 * Real.sqrt (sigma a s x))) / Real.sqrt (sigma a s x) ^ 2

theorem W21_ae {a' : ℝ → ℝ} (hd : ∀ᵐ x : ℝ, x ∈ Ioo (-1 : ℝ) 1 → HasDerivAt a (a' x) x) :
    ∀ᵐ x : ℝ, x ∈ Ioo (0 : ℝ) 1 → HasDerivAt a (a' x) x ∧ HasDerivAt a (a' (-x)) (-x) := by
  have h2 : ∀ᵐ x : ℝ, -x ∈ Ioo (-1 : ℝ) 1 → HasDerivAt a (a' (-x)) (-x) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hd
  filter_upwards [hd, h2] with x h1 h2 hx
  exact ⟨h1 ⟨by linarith [hx.1], hx.2⟩, h2 ⟨by linarith [hx.2], by linarith [hx.1]⟩⟩

theorem HypH.hasDerivAt_kfun_explicit (h : HypH a m κ) {a' : ℝ → ℝ} {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (h1 : HasDerivAt a (a' x) x) (h2 : HasDerivAt a (a' (-x)) (-x)) :
    HasDerivAt (kfun a) (kD a a' x) x := by
  have hxI : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2.le⟩
  have hb : HasDerivAt (fun y => a (-y)) (a' (-x) * -1) x := h2.comp x (hasDerivAt_neg x)
  have hdiv := HasDerivAt.div hb h1 (h.ne_zero hxI)
  have hsq := hdiv.sqrt (h.ratio_pos hxI).ne'
  exact (hsq.const_mul (eps a))

theorem HypH.hasDerivAt_tau_explicit (h : HypH a m κ) {s : ℝ} (hs : s = 1 ∨ s = -1)
    {a' : ℝ → ℝ} {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (h1 : HasDerivAt a (a' x) x) (h2 : HasDerivAt a (a' (-x)) (-x)) :
    HasDerivAt (tau a s) (tauD a a' s x) x := by
  have hxI : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2.le⟩
  have hb : HasDerivAt (fun y => a (-y)) (a' (-x) * -1) x := h2.comp x (hasDerivAt_neg x)
  have hp := (h1.mul hb).sqrt (h.pos_p hxI).ne'
  have hσ := (hp.const_mul s).const_add 1
  have hσ' := hσ.sqrt (h.sigma_pos hs hxI).ne'
  exact hσ'.inv (Real.sqrt_pos.2 (h.sigma_pos hs hxI)).ne'

theorem ac_const (c : ℝ) : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) 0 1 :=
  (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval

theorem ac_div_of_pos {f g : ℝ → ℝ} (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hg : AbsolutelyContinuousOnInterval g 0 1) (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < g x) :
    AbsolutelyContinuousOnInterval (fun x => f x / g x) 0 1 := by
  simpa only [div_eq_mul_inv] using hf.fun_mul (ac_inv_of_pos hg hpos)

theorem sqrt_ratio_eq (a : ℝ → ℝ) (x : ℝ) : Real.sqrt (a (-x) / a x) = |kfun a x| := by
  unfold kfun
  rw [abs_mul, abs_eps, one_mul, abs_of_nonneg (Real.sqrt_nonneg _)]

theorem HypH.ac_sqrt_ratio (h : HypH a m κ) :
    AbsolutelyContinuousOnInterval (fun x => Real.sqrt (a (-x) / a x)) 0 1 := by
  simp only [sqrt_ratio_eq]
  exact ac_abs h.ac_kfun

theorem HypH.ac_rD (h : HypH a m κ) {a' : ℝ → ℝ}
    (hw : AbsolutelyContinuousOnInterval a' (-1) 1) :
    AbsolutelyContinuousOnInterval (rD a a') 0 1 := by
  have ha' : AbsolutelyContinuousOnInterval a' 0 1 := hw.mono (by
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1), uIcc_of_le (zero_le_one' ℝ)]
    exact Icc_subset_Icc (by norm_num) le_rfl)
  have ha'n := ac_neg_comp hw
  have hu1 : AbsolutelyContinuousOnInterval (fun x => a' (-x) * -1) 0 1 := by
    simpa [mul_comm] using ha'n.const_mul (-1)
  have hnum := (ha'.fun_mul h.ac_neg).fun_add (h.ac_half.fun_mul hu1)
  have hden : AbsolutelyContinuousOnInterval (fun x => 2 * Real.sqrt (a x * a (-x))) 0 1 :=
    h.ac_rp.const_mul 2
  exact ac_div_of_pos hnum hden (fun x hx => by
    have := h.sqrt_pos' (mem_Icc_neg_one_of_mem hx); positivity)

theorem HypH.ac_kD (h : HypH a m κ) {a' : ℝ → ℝ}
    (hw : AbsolutelyContinuousOnInterval a' (-1) 1) :
    AbsolutelyContinuousOnInterval (kD a a') 0 1 := by
  have ha' : AbsolutelyContinuousOnInterval a' 0 1 := hw.mono (by
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1), uIcc_of_le (zero_le_one' ℝ)]
    exact Icc_subset_Icc (by norm_num) le_rfl)
  have ha'n := ac_neg_comp hw
  have hu1 : AbsolutelyContinuousOnInterval (fun x => a' (-x) * -1) 0 1 := by
    simpa [mul_comm] using ha'n.const_mul (-1)
  have hnum := (hu1.fun_mul h.ac_half).fun_sub (h.ac_neg.fun_mul ha')
  have hsq : AbsolutelyContinuousOnInterval (fun x => a x ^ 2) 0 1 := by
    simpa [sq] using h.ac_half.fun_mul h.ac_half
  have hsqpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < a x ^ 2 := fun x hx =>
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (h.ne_zero (mem_Icc_neg_one_of_mem hx))))
  have h1 := ac_div_of_pos hnum hsq hsqpos
  have hden : AbsolutelyContinuousOnInterval (fun x => 2 * Real.sqrt (a (-x) / a x)) 0 1 :=
    h.ac_sqrt_ratio.const_mul 2
  have h2 := ac_div_of_pos h1 hden (fun x hx => by
    have := Real.sqrt_pos.2 (h.ratio_pos (mem_Icc_neg_one_of_mem hx)); positivity)
  exact h2.const_mul (eps a)

theorem HypH.ac_tauD (h : HypH a m κ) {a' : ℝ → ℝ}
    (hw : AbsolutelyContinuousOnInterval a' (-1) 1) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    AbsolutelyContinuousOnInterval (tauD a a' s) 0 1 := by
  have hσ := ac_sqrt_of_pos (h.ac_sigma s) (fun x hx =>
    h.sigma_pos hs (mem_Icc_neg_one_of_mem hx))
  have hσpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < Real.sqrt (sigma a s x) := fun x hx =>
    Real.sqrt_pos.2 (h.sigma_pos hs (mem_Icc_neg_one_of_mem hx))
  have hn : AbsolutelyContinuousOnInterval (fun x => s * rD a a' x) 0 1 :=
    (h.ac_rD hw).const_mul s
  have hd : AbsolutelyContinuousOnInterval (fun x => 2 * Real.sqrt (sigma a s x)) 0 1 :=
    hσ.const_mul 2
  have h1 := ac_div_of_pos hn hd (fun x hx => by have := hσpos x hx; positivity)
  have hsq : AbsolutelyContinuousOnInterval (fun x => Real.sqrt (sigma a s x) ^ 2) 0 1 := by
    simpa [sq] using hσ.fun_mul hσ
  have h2 := ac_div_of_pos h1.fun_neg hsq (fun x hx => by have := hσpos x hx; positivity)
  exact h2

/-- `Ã` с `deriv` заменённой на явные формулы через `a'`: непрерывный представитель. -/
def AtildeW (a a' : ℝ → ℝ) (x : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun c c' =>
    if c = c' then 0
    else if chan c = chan c' then ((tauD a a' (chan c) x / (2 * tau a (chan c) x) : ℝ) : ℂ)
    else ((kD a a' x / (4 * kfun a x) : ℝ) : ℂ) *
      (1 + ((sgn c' * tau a (chan c') x / (sgn c * tau a (chan c) x) : ℝ) : ℂ)) *
      ((Damp a (chan c') x / Damp a (chan c) x : ℝ) : ℂ)

theorem HypH.ae_Atilde_eq (h : HypH a m κ) {a' : ℝ → ℝ}
    (hd : ∀ᵐ x : ℝ, x ∈ Ioo (-1 : ℝ) 1 → HasDerivAt a (a' x) x) :
    ∀ᵐ x : ℝ, x ∈ Icc (0 : ℝ) 1 → Atilde a x = AtildeW a a' x := by
  apply ae_Icc_of_Ioo
  filter_upwards [W21_ae hd] with x hx hxI
  obtain ⟨h1, h2⟩ := hx hxI
  have hk : dk a x = kD a a' x := (h.hasDerivAt_kfun_explicit hxI h1 h2).deriv
  have ht : ∀ s, (s = 1 ∨ s = -1) → dtau a s x = tauD a a' s x := fun s hs =>
    (h.hasDerivAt_tau_explicit hs hxI h1 h2).deriv
  ext c c'
  simp only [Atilde, AtildeW, Matrix.of_apply]
  rw [hk, ht _ (chan_eq c)]
  by_cases hcc : c = c' <;> by_cases hch : chan c = chan c' <;> simp [hcc, hch]

theorem HypH.ac_AtildeW (h : HypH a m κ) {a' : ℝ → ℝ}
    (hw : AbsolutelyContinuousOnInterval a' (-1) 1) (c c' : Fin 4) :
    AbsolutelyContinuousOnInterval (fun x => AtildeW a a' x c c') 0 1 := by
  by_cases hcc : c = c'
  · have : (fun x => AtildeW a a' x c c') = fun _ => (0 : ℂ) := by
      funext x; simp [AtildeW, hcc]
    rw [this]
    exact (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  by_cases hch : chan c = chan c'
  · have hs := chan_eq c
    have h1 := ac_div_of_pos (h.ac_tauD hw hs) ((h.ac_tau hs).const_mul 2) (fun x hx => by
      have := h.tau_pos hs (mem_Icc_neg_one_of_mem hx); positivity)
    have : (fun x => AtildeW a a' x c c') =
        fun x => ((tauD a a' (chan c) x / (2 * tau a (chan c) x) : ℝ) : ℂ) := by
      funext x; simp [AtildeW, hcc, hch]
    rw [this]
    exact ac_ofReal h1
  · have hs := chan_eq c
    have hs' := chan_eq c'
    have hkpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < 4 * (eps a * kfun a x) := fun x hx => by
      have := abs_pos.2 (h.kfun_ne_zero (mem_Icc_neg_one_of_mem hx))
      rw [kfun_eps_abs] at this; positivity
    have A1 : AbsolutelyContinuousOnInterval (fun x => kD a a' x / (4 * kfun a x)) 0 1 := by
      have := ac_div_of_pos ((h.ac_kD hw).const_mul (eps a))
        ((h.ac_kfun.const_mul (eps a)).const_mul 4) hkpos
      refine this.congr (fun x hx => ?_)
      have hk := h.kfun_ne_zero (mem_Icc_neg_one_of_mem (by
        rw [uIcc_of_le (zero_le_one' ℝ)] at hx; exact hx))
      have := eps_ne_zero a
      simp only
      field_simp
    have A2 : AbsolutelyContinuousOnInterval
        (fun x => sgn c' * tau a (chan c') x / (sgn c * tau a (chan c) x)) 0 1 := by
      have := ac_div_of_pos (((h.ac_tau hs').const_mul (sgn c' * sgn c)))
        (h.ac_tau hs) (fun x hx => h.tau_pos hs (mem_Icc_neg_one_of_mem hx))
      refine this.congr (fun x hx => ?_)
      have ht := (h.tau_pos hs (mem_Icc_neg_one_of_mem (by
        rw [uIcc_of_le (zero_le_one' ℝ)] at hx; exact hx))).ne'
      have hsg : sgn c ≠ 0 := by rcases sgn_eq c with h1 | h1 <;> rw [h1] <;> norm_num
      have hs2 : sgn c * sgn c = 1 := by rcases sgn_eq c with h1 | h1 <;> rw [h1] <;> norm_num
      simp only
      field_simp
      linear_combination (sgn c' * tau a (chan c') x) * hs2
    have A3 := ac_div_of_pos (h.ac_Damp hs') (h.ac_Damp hs) (fun x hx =>
      h.Damp_pos hs (mem_Icc_neg_one_of_mem hx))
    have hc1 : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℂ)) 0 1 :=
      (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
    have hprod := (((ac_ofReal A1).fun_smul (hc1.fun_add (ac_ofReal A2))).fun_smul (ac_ofReal A3))
    have hprod' : AbsolutelyContinuousOnInterval (fun x =>
        ((kD a a' x / (4 * kfun a x) : ℝ) : ℂ) *
        (1 + ((sgn c' * tau a (chan c') x / (sgn c * tau a (chan c) x) : ℝ) : ℂ)) *
        ((Damp a (chan c') x / Damp a (chan c) x : ℝ) : ℂ)) 0 1 := by
      simpa only [smul_eq_mul] using hprod
    have e : (fun x => AtildeW a a' x c c') = fun x =>
        ((kD a a' x / (4 * kfun a x) : ℝ) : ℂ) *
        (1 + ((sgn c' * tau a (chan c') x / (sgn c * tau a (chan c) x) : ℝ) : ℂ)) *
        ((Damp a (chan c') x / Damp a (chan c) x : ℝ) : ℂ) := by
      funext x; simp only [AtildeW, Matrix.of_apply, hcc, hch, ite_false]
    rw [e]
    exact hprod'

theorem HypH.Atilde_offdiag_ac (h : HypH a m κ) (hw : IsW21 a) :
    ∃ B : ℝ → Matrix (Fin 4) (Fin 4) ℂ,
      (∀ i j, AbsolutelyContinuousOnInterval (fun x => B x i j) 0 1) ∧
      ∀ᵐ x : ℝ, x ∈ Icc (0 : ℝ) 1 → Atilde a x = B x := by
  obtain ⟨a', -, hac', hd⟩ := hw
  exact ⟨AtildeW a a', fun i j => h.ac_AtildeW hac' i j, h.ae_Atilde_eq hd⟩

end W21
end Involution.GeneralBC


