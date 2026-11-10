module

public import Involution.Folding.GeneralBCAsymptoticCoeffAlg
public import Involution.Folding.GeneralBCExternal
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Перенос решений: `W D Z̃` решает `Y' = ρ K Y` (G2a, часть (в))

Абсолютная непрерывность `Damp`, `W`, `W D`; производные в точках дифференцируемости `a`
(`ae_good`); интегрируемость `Ã` (`HypH.integrable_Atilde`); непрерывность `Kmat`;
главная теорема `HypH.transfer`: если `Z̃` удовлетворяет `IsMatSol (Ã + ρ Λ)` и подынтегральные
функции суммируемы (гипотеза `hint`), то `W D Z̃` удовлетворяет `IsSol a ρ`.
Формула Ньютона–Лейбница — `Involution.complex_ac_integral_eq_sub`. -/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Involution.GeneralBC
section Anal
variable {a : ℝ → ℝ} {m κ : ℝ}

theorem ac_sqrt_of_pos {g : ℝ → ℝ} (hg : AbsolutelyContinuousOnInterval g 0 1)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < g x) :
    AbsolutelyContinuousOnInterval (fun x => Real.sqrt (g x)) 0 1 := by
  have hc : ContinuousOn g (Icc 0 1) := by
    simpa [uIcc_of_le (zero_le_one' ℝ)] using hg.continuousOn
  obtain ⟨xm, hxm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (zero_le_one' ℝ)) hc
  obtain ⟨xM, hxM, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 (zero_le_one' ℝ)) hc
  exact ac_comp_cd (contDiffOn_sqrt_Icc (c := g xm) (d := g xM) (hpos xm hxm)) hg
    (fun x hx => ⟨hmin hx, hmax hx⟩)

theorem ac_inv_of_pos {g : ℝ → ℝ} (hg : AbsolutelyContinuousOnInterval g 0 1)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < g x) :
    AbsolutelyContinuousOnInterval (fun x => (g x)⁻¹) 0 1 := by
  have hc : ContinuousOn g (Icc 0 1) := by
    simpa [uIcc_of_le (zero_le_one' ℝ)] using hg.continuousOn
  obtain ⟨xm, hxm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (zero_le_one' ℝ)) hc
  obtain ⟨xM, hxM, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 (zero_le_one' ℝ)) hc
  exact ac_comp_cd (f := fun y : ℝ => y⁻¹)
    (contDiffOn_inv_Icc (c := g xm) (d := g xM) (hpos xm hxm)) hg (fun x hx => ⟨hmin hx, hmax hx⟩)

theorem ac_abs {g : ℝ → ℝ} (hg : AbsolutelyContinuousOnInterval g 0 1) :
    AbsolutelyContinuousOnInterval (fun x => |g x|) 0 1 :=
  (lipschitzWith_one_norm (E := ℝ)).comp_absolutelyContinuousOnInterval hg

theorem HypH.tau0_pos (h : HypH a m κ) {s : ℝ} (hs : s = 1 ∨ s = -1) : 0 < tau0 a s :=
  h.tau_pos hs (by simp)

theorem HypH.Damp_arg_pos (h : HypH a m κ) {s : ℝ} (hs : s = 1 ∨ s = -1) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) : 0 < tau0 a s / (|kfun a x| * tau a s x) :=
  div_pos (h.tau0_pos hs) (mul_pos (abs_pos.2 (h.kfun_ne_zero hx)) (h.tau_pos hs hx))

theorem HypH.Damp_pos (h : HypH a m κ) {s : ℝ} (hs : s = 1 ∨ s = -1) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) : 0 < Damp a s x :=
  Real.sqrt_pos.2 (h.Damp_arg_pos hs hx)

theorem HypH.Damp_sq (h : HypH a m κ) {s : ℝ} (hs : s = 1 ∨ s = -1) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) : Damp a s x ^ 2 = tau0 a s / (|kfun a x| * tau a s x) :=
  Real.sq_sqrt (h.Damp_arg_pos hs hx).le

theorem HypH.ac_Damp (h : HypH a m κ) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    AbsolutelyContinuousOnInterval (Damp a s) 0 1 := by
  have h1 : AbsolutelyContinuousOnInterval (fun x => |kfun a x| * tau a s x) 0 1 :=
    (ac_abs h.ac_kfun).fun_mul (h.ac_tau hs)
  have h2 := ac_inv_of_pos h1 (fun x hx => mul_pos
    (abs_pos.2 (h.kfun_ne_zero (mem_Icc_neg_one_of_mem hx)))
    (h.tau_pos hs (mem_Icc_neg_one_of_mem hx)))
  have h3 : AbsolutelyContinuousOnInterval (fun x => tau0 a s / (|kfun a x| * tau a s x)) 0 1 := by
    simpa [div_eq_mul_inv] using h2.const_mul (tau0 a s)
  exact ac_sqrt_of_pos h3 (fun x hx => h.Damp_arg_pos hs (mem_Icc_neg_one_of_mem hx))

theorem ae_good (h : HypH a m κ) : ∀ᵐ x : ℝ, x ∈ Ioo (0 : ℝ) 1 →
    DifferentiableAt ℝ a x ∧ DifferentiableAt ℝ a (-x) := by
  have h1 := h.ac.ae_differentiableAt
  have h2 : ∀ᵐ x : ℝ, -x ∈ uIcc (-1 : ℝ) 1 → DifferentiableAt ℝ a (-x) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae h1
  filter_upwards [h1, h2] with x hx1 hx2 hx
  have hxI : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2.le⟩
  rw [← uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hxI
  have hxI' : -x ∈ uIcc (-1 : ℝ) 1 := by
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  exact ⟨hx1 hxI, hx2 hxI'⟩

theorem HypH.differentiableAt_kfun (h : HypH a m κ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ a (-x)) :
    DifferentiableAt ℝ (kfun a) x := by
  have hxI : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2.le⟩
  have hb' : DifferentiableAt ℝ (fun y => a (-y)) x := hb.comp x differentiableAt_id.neg
  have hdiv := DifferentiableAt.div hb' ha (h.ne_zero hxI)
  have hsq := hdiv.sqrt (h.ratio_pos hxI).ne'
  exact hsq.const_mul (eps a)

theorem HypH.differentiableAt_tau (h : HypH a m κ) {s : ℝ} (hs : s = 1 ∨ s = -1) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1)
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ a (-x)) :
    DifferentiableAt ℝ (tau a s) x := by
  have hxI : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2.le⟩
  have hb' : DifferentiableAt ℝ (fun y => a (-y)) x := hb.comp x differentiableAt_id.neg
  have hp := (ha.mul hb').sqrt (h.pos_p hxI).ne'
  have hσ : DifferentiableAt ℝ (fun y => 1 + s * Real.sqrt (a y * a (-y))) x :=
    (hp.const_mul s).const_add 1
  have hσ' := hσ.sqrt (h.sigma_pos hs hxI).ne'
  exact hσ'.inv (Real.sqrt_pos.2 (h.sigma_pos hs hxI)).ne'

theorem kfun_eps_abs (a : ℝ → ℝ) (x : ℝ) : |kfun a x| = eps a * kfun a x := by
  unfold kfun
  rw [abs_mul, abs_eps, one_mul, abs_of_nonneg (Real.sqrt_nonneg _), ← mul_assoc,
    eps_mul_eps, one_mul]

theorem HypH.hasDerivAt_Damp (h : HypH a m κ) {s : ℝ} (hs : s = 1 ∨ s = -1) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hk : DifferentiableAt ℝ (kfun a) x)
    (ht : DifferentiableAt ℝ (tau a s) x) :
    HasDerivAt (Damp a s)
      (Damp a s x * (-(deriv (kfun a) x / (2 * kfun a x)) -
        deriv (tau a s) x / (2 * tau a s x))) x := by
  have hxI : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2.le⟩
  have hk' := hk.hasDerivAt
  have ht' := ht.hasDerivAt
  have hkne := h.kfun_ne_zero hxI
  have htne := (h.tau_pos hs hxI).ne'
  have hden : HasDerivAt (fun y => eps a * kfun a y * tau a s y)
      (eps a * deriv (kfun a) x * tau a s x + eps a * kfun a x * deriv (tau a s) x) x :=
    (hk'.const_mul (eps a)).mul ht'
  have hdenne : eps a * kfun a x * tau a s x ≠ 0 :=
    mul_ne_zero (mul_ne_zero (eps_ne_zero a) hkne) htne
  have hg := HasDerivAt.div (hasDerivAt_const x (tau0 a s)) hden hdenne
  have hD2 : Damp a s x ^ 2 = tau0 a s / (eps a * kfun a x * tau a s x) := by
    rw [h.Damp_sq hs hxI, kfun_eps_abs, mul_assoc]
  have hDpos := h.Damp_pos hs hxI
  have hgpos : 0 < tau0 a s / (eps a * kfun a x * tau a s x) := by
    rw [← hD2]; positivity
  have hsq := hg.sqrt hgpos.ne'
  have hev : (fun y => Real.sqrt (((fun _ : ℝ => tau0 a s) /
      fun y => eps a * kfun a y * tau a s y) y)) =ᶠ[nhds x] Damp a s := by
    filter_upwards [Icc_mem_nhds (show (-1 : ℝ) < x by linarith [hx.1])
      (show x < 1 from hx.2)] with y hy
    simp only [Pi.div_apply, Damp]
    rw [kfun_eps_abs, mul_assoc]
  refine (hsq.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  have hDx : Real.sqrt (((fun _ : ℝ => tau0 a s) / fun y => eps a * kfun a y * tau a s y) x)
      = Damp a s x := by
    simp only [Pi.div_apply, Damp]
    rw [kfun_eps_abs, mul_assoc]
  rw [hDx]
  have heps := eps_ne_zero a
  have htau0 : tau0 a s = Damp a s x ^ 2 * (eps a * kfun a x * tau a s x) := by
    rw [hD2]; field_simp
  rw [htau0]
  field_simp
  ring

theorem HypH.hasDerivAt_W (h : HypH a m κ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ a (-x)) (i c : Fin 4) :
    HasDerivAt (fun y => Wmat a y i c) (Wder a x i c) x := by
  have hk := (h.differentiableAt_kfun hx ha hb).hasDerivAt
  have ht := (h.differentiableAt_tau (chan_eq c) hx ha hb).hasDerivAt
  have hk' : HasDerivAt (fun y => ((kfun a y : ℝ) : ℂ)) ((deriv (kfun a) x : ℝ) : ℂ) x :=
    hk.ofReal_comp
  have ht' : HasDerivAt (fun y => ((tau a (chan c) y : ℝ) : ℂ))
      ((deriv (tau a (chan c)) x : ℝ) : ℂ) x := ht.ofReal_comp
  fin_cases i
  · simpa [Wmat, gvec, Wder] using hasDerivAt_const x (1 : ℂ)
  · have := (hk'.const_mul (chan c : ℂ))
    simp only [Wmat, gvec, Wder, dk, Matrix.of_apply, Fin.mk_one, Fin.isValue,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    push_cast
    exact this
  · have := (ht'.const_mul (Complex.I * (sgn c : ℂ)))
    simp only [Wmat, gvec, Wder, dtau, Matrix.of_apply, Fin.reduceFinMk, Fin.isValue,
      Matrix.cons_val]
    exact this
  · have := ((ht'.const_mul (Complex.I * (sgn c : ℂ))).mul (hk'.const_mul (chan c : ℂ)))
    simp only [Wmat, gvec, Wder, dtau, dk, Matrix.of_apply, Fin.reduceFinMk, Fin.isValue,
      Matrix.cons_val]
    push_cast
    convert this using 1
    ring

theorem WD_apply (a : ℝ → ℝ) (y : ℝ) (i k : Fin 4) :
    (Wmat a y * Dmat a y) i k = Wmat a y i k * (Damp a (chan k) y : ℂ) := by
  simp [Dmat, Matrix.mul_diagonal]

theorem HypH.hasDerivAt_WD (h : HypH a m κ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ a (-x)) (i k : Fin 4) :
    HasDerivAt (fun y => (Wmat a y * Dmat a y) i k) (Nmat a x i k) x := by
  have hk := h.differentiableAt_kfun hx ha hb
  have ht := h.differentiableAt_tau (chan_eq k) hx ha hb
  have hD := (h.hasDerivAt_Damp (chan_eq k) hx hk ht).ofReal_comp
  have hW := h.hasDerivAt_W hx ha hb i k
  have := hW.mul hD
  simp only [WD_apply]
  convert this using 1
  simp [Nmat, Dder, Dmat, acoef, dk, dtau, Matrix.mul_diagonal, Matrix.add_apply]

theorem ac_ofReal {f : ℝ → ℝ} (hf : AbsolutelyContinuousOnInterval f 0 1) :
    AbsolutelyContinuousOnInterval (fun x => (f x : ℂ)) 0 1 :=
  Complex.ofRealLI.isometry.lipschitzWith.comp_absolutelyContinuousOnInterval hf

theorem HypH.ac_W (h : HypH a m κ) (i c : Fin 4) :
    AbsolutelyContinuousOnInterval (fun y => Wmat a y i c) 0 1 := by
  have hk := ac_ofReal h.ac_kfun
  have ht := ac_ofReal (h.ac_tau (chan_eq c))
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℂ)) 0 1 :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  fin_cases i
  · simpa [Wmat, gvec] using hc
  · simpa [Wmat, gvec] using hk.const_smul (chan c : ℂ)
  · simpa [Wmat, gvec] using ht.const_smul (Complex.I * (sgn c : ℂ))
  · have := (ht.fun_smul hk).const_smul (Complex.I * (sgn c : ℂ) * (chan c : ℂ))
    simp only [Wmat, gvec, Matrix.of_apply, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
    convert this using 2 with y
    simp only [smul_eq_mul]
    push_cast
    ring

theorem HypH.ac_WD (h : HypH a m κ) (i k : Fin 4) :
    AbsolutelyContinuousOnInterval (fun y => (Wmat a y * Dmat a y) i k) 0 1 := by
  simp only [WD_apply]
  exact (h.ac_W i k).fun_smul (ac_ofReal (h.ac_Damp (chan_eq k)))

theorem HypH.continuousOn_Kmat (h : HypH a m κ) (i j : Fin 4) :
    ContinuousOn (fun x => Kmat a x i j) (Icc (0 : ℝ) 1) := by
  have ha : ContinuousOn a (Icc 0 1) := h.continuousOn.mono (fun x hx => mem_Icc_neg_one_of_mem hx)
  have hb : ContinuousOn (fun x => a (-x)) (Icc 0 1) :=
    h.continuousOn.comp continuousOn_neg
      (fun x hx => neg_mem_Icc_one (mem_Icc_neg_one_of_mem hx))
  have haC : ContinuousOn (fun x => (a x : ℂ)) (Icc 0 1) :=
    Complex.continuous_ofReal.comp_continuousOn ha
  have hbC : ContinuousOn (fun x => (a (-x) : ℂ)) (Icc 0 1) :=
    Complex.continuous_ofReal.comp_continuousOn hb
  have hqC : ContinuousOn (fun x => (1 - (a x : ℂ) * (a (-x) : ℂ))⁻¹) (Icc 0 1) := by
    refine (continuousOn_const.sub (haC.mul hbC)).inv₀ (fun x hx => ?_)
    have := h.upper x (mem_Icc_neg_one_of_mem hx)
    have hne : (1 : ℝ) - a x * a (-x) ≠ 0 := by linarith [h.kappa_lt]
    simp only [Pi.sub_apply, Pi.mul_apply]
    exact_mod_cast hne
  fin_cases i <;> fin_cases j <;>
    simp only [Kmat, Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_mul, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] <;> first
    | exact continuousOn_const
    | exact hqC.neg
    | exact hqC
    | exact hqC.mul haC
    | exact hqC.mul hbC

theorem acc_cont {f : ℝ → ℝ} (hf : AbsolutelyContinuousOnInterval f 0 1) :
    ContinuousOn f (Icc 0 1) := by
  simpa [uIcc_of_le (zero_le_one' ℝ)] using hf.continuousOn

theorem intInt_ofReal' {g : ℝ → ℝ} (hg : IntervalIntegrable g volume 0 1) :
    IntervalIntegrable (fun x => (g x : ℂ)) volume 0 1 :=
  ⟨hg.1.ofReal, hg.2.ofReal⟩

theorem HypH.integrable_Atilde (h : HypH a m κ) (c c' : Fin 4) :
    IntervalIntegrable (fun x => Atilde a x c c') volume 0 1 := by
  have hk := h.ac_kfun
  have hkc := acc_cont hk
  have hunc : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le (zero_le_one' ℝ)
  by_cases hcc : c = c'
  · subst hcc
    have : (fun x => Atilde a x c c) = fun _ => (0 : ℂ) := funext fun x => Atilde_diag a x c
    rw [this]
    exact intervalIntegrable_const
  by_cases hch : chan c = chan c'
  · have hs := chan_eq c
    have htc := acc_cont (h.ac_tau hs)
    have hint : IntervalIntegrable
        (fun x => deriv (tau a (chan c)) x * (2 * tau a (chan c) x)⁻¹) volume 0 1 :=
      (h.ac_tau hs).intervalIntegrable_deriv.mul_continuousOn
      (g := fun x => (2 * tau a (chan c) x)⁻¹) (by
        rw [hunc]
        exact (continuousOn_const.mul htc).inv₀ (fun x hx =>
          mul_ne_zero two_ne_zero (h.tau_pos hs (mem_Icc_neg_one_of_mem hx)).ne'))
    have hreal : IntervalIntegrable
        (fun x => dtau a (chan c) x / (2 * tau a (chan c) x)) volume 0 1 := by
      simpa only [div_eq_mul_inv, dtau] using hint
    have e : ∀ x, Atilde a x c c' =
        ((dtau a (chan c) x / (2 * tau a (chan c) x) : ℝ) : ℂ) := fun x => by
      simp [Atilde, hcc, hch]
    simp_rw [e]
    exact intInt_ofReal' hreal
  · have hs := chan_eq c
    have hs' := chan_eq c'
    have hτc := acc_cont (h.ac_tau hs)
    have hτc' := acc_cont (h.ac_tau hs')
    have hDc := acc_cont (h.ac_Damp hs)
    have hDc' := acc_cont (h.ac_Damp hs')
    have hsg : sgn c ≠ 0 := by rcases sgn_eq c with h1 | h1 <;> rw [h1] <;> norm_num
    have hsg' : sgn c' ≠ 0 := by rcases sgn_eq c' with h1 | h1 <;> rw [h1] <;> norm_num
    have hnz : ∀ x ∈ Icc (0 : ℝ) 1, kfun a x ≠ 0 := fun x hx =>
      h.kfun_ne_zero (mem_Icc_neg_one_of_mem hx)
    have r1 : ContinuousOn (fun x => 1 / (4 * kfun a x)) (Icc 0 1) :=
      continuousOn_const.div (continuousOn_const.mul hkc) (fun x hx =>
        mul_ne_zero four_ne_zero (hnz x hx))
    have r2 : ContinuousOn (fun x => (sgn c' * tau a (chan c') x) / (sgn c * tau a (chan c) x))
        (Icc 0 1) :=
      (continuousOn_const.mul hτc').div (continuousOn_const.mul hτc) (fun x hx =>
        mul_ne_zero hsg (h.tau_pos hs (mem_Icc_neg_one_of_mem hx)).ne')
    have r3 : ContinuousOn (fun x => Damp a (chan c') x / Damp a (chan c) x) (Icc 0 1) :=
      hDc'.div hDc (fun x hx => (h.Damp_pos hs (mem_Icc_neg_one_of_mem hx)).ne')
    have G : ContinuousOn (fun x => (((1 / (4 * kfun a x) : ℝ) : ℂ) *
        (1 + (((sgn c' * tau a (chan c') x) / (sgn c * tau a (chan c) x) : ℝ) : ℂ)) *
        (((Damp a (chan c') x / Damp a (chan c) x : ℝ)) : ℂ))) (uIcc 0 1) := by
      rw [hunc]
      exact ((Complex.continuous_ofReal.comp_continuousOn r1).mul
        (continuousOn_const.add (Complex.continuous_ofReal.comp_continuousOn r2))).mul
        (Complex.continuous_ofReal.comp_continuousOn r3)
    have hdk : IntervalIntegrable (fun x => ((dk a x : ℝ) : ℂ)) volume 0 1 :=
      intInt_ofReal' hk.intervalIntegrable_deriv
    have := hdk.mul_continuousOn G
    have e : ∀ x, Atilde a x c c' = ((dk a x : ℝ) : ℂ) * (((1 / (4 * kfun a x) : ℝ) : ℂ) *
        (1 + (((sgn c' * tau a (chan c') x) / (sgn c * tau a (chan c) x) : ℝ) : ℂ)) *
        (((Damp a (chan c') x / Damp a (chan c) x : ℝ)) : ℂ)) := fun x => by
      simp only [Atilde, Matrix.of_apply, hcc, hch, ite_false]
      push_cast
      ring
    simp_rw [e]
    exact this

theorem ae_Icc_of_Ioo {P : ℝ → Prop} (hP : ∀ᵐ x : ℝ, x ∈ Ioo (0 : ℝ) 1 → P x) :
    ∀ᵐ x : ℝ, x ∈ Icc (0 : ℝ) 1 → P x := by
  filter_upwards [hP, (Set.toFinite ({0, 1} : Set ℝ)).countable.ae_notMem (volume : Measure ℝ)]
    with x hx hn hmem
  apply hx
  refine ⟨lt_of_le_of_ne hmem.1 ?_, lt_of_le_of_ne hmem.2 ?_⟩
  · intro h0; exact hn (by simp [← h0])
  · intro h1; exact hn (by simp [h1])

/-- Подстановка `Z` из интегрального уравнения: абсолютная непрерывность и производная п.в. -/
theorem matSol_entry_ac {M Z : ℝ → Matrix (Fin 4) (Fin 4) ℂ} (hZ : IsMatSol M Z)
    (hint : ∀ i j, IntervalIntegrable (fun x => (M x * Z x) i j) volume 0 1) (i j : Fin 4) :
    AbsolutelyContinuousOnInterval (fun x => Z x i j) 0 1 := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => Z 0 i j) 0 1 :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  have := hc.fun_add (complex_primitive_absolutelyContinuous (zero_le_one' ℝ) (hint i j))
  refine this.congr ?_
  intro x hx
  rw [uIcc_of_le (zero_le_one' ℝ)] at hx
  exact (hZ x hx i j).symm

theorem matSol_ae_deriv {M Z : ℝ → Matrix (Fin 4) (Fin 4) ℂ} (hZ : IsMatSol M Z)
    (hint : ∀ i j, IntervalIntegrable (fun x => (M x * Z x) i j) volume 0 1) :
    ∀ᵐ x : ℝ, x ∈ Ioo (0 : ℝ) 1 → ∀ i j, HasDerivAt (fun y => Z y i j) ((M x * Z x) i j) x := by
  have hae : ∀ᵐ x : ℝ, ∀ i j, (x ∈ uIcc (0 : ℝ) 1 → ∀ c ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun u => ∫ v in c..u, (M v * Z v) i j) ((M x * Z x) i j) x) := by
    rw [ae_all_iff]; intro i
    rw [ae_all_iff]; intro j
    exact (hint i j).ae_hasDerivAt_integral
  filter_upwards [hae] with x hx hxI i j
  have hxu : x ∈ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le (zero_le_one' ℝ)]; exact ⟨hxI.1.le, hxI.2.le⟩
  have h0 : (0 : ℝ) ∈ uIcc (0 : ℝ) 1 := left_mem_uIcc
  have := (hx i j hxu 0 h0).const_add (Z 0 i j)
  refine this.congr_of_eventuallyEq ?_
  filter_upwards [Icc_mem_nhds hxI.1 hxI.2] with y hy
  exact hZ y hy i j

theorem transfer_matrix_identity {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (ρ : ℂ) (Z : Matrix (Fin 4) (Fin 4) ℂ) :
    Nmat a x * Z + (Wmat a x * Dmat a x) * ((Atilde a x + ρ • Lam a x) * Z) =
      ρ • (Kmat a x * (Wmat a x * Dmat a x * Z)) := by
  have hxI := mem_Icc_neg_one_of_mem hx
  have hk := h.kfun_ne_zero hxI
  have h1 := (h.tau_pos (Or.inl rfl) hxI).ne'
  have h2 := (h.tau_pos (Or.inr rfl) hxI).ne'
  have d1 := (h.Damp_pos (Or.inl rfl) hxI).ne'
  have d2 := (h.Damp_pos (Or.inr rfl) hxI).ne'
  have e1 := WDAtilde hk h1 h2 d1 d2
  have e2 := Kmat_mul_WD h hxI
  calc Nmat a x * Z + (Wmat a x * Dmat a x) * ((Atilde a x + ρ • Lam a x) * Z)
      = (Nmat a x + Wmat a x * Dmat a x * Atilde a x) * Z
        + ρ • (Wmat a x * Dmat a x * Lam a x * Z) := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_assoc]
        abel
    _ = ρ • (Kmat a x * (Wmat a x * Dmat a x * Z)) := by
        rw [e1, add_neg_cancel, Matrix.zero_mul, zero_add, ← e2, Matrix.mul_assoc]

theorem HypH.hasDerivAt_Y (h : HypH a m κ) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1)
    (ha : DifferentiableAt ℝ a y) (hb : DifferentiableAt ℝ a (-y)) (ρ : ℂ)
    {Z : ℝ → Matrix (Fin 4) (Fin 4) ℂ} {Gm : Matrix (Fin 4) (Fin 4) ℂ}
    (hZ : ∀ k j, HasDerivAt (fun z => Z z k j) (Gm k j) y)
    (hG : Gm = (Atilde a y + ρ • Lam a y) * Z y) (i j : Fin 4) :
    HasDerivAt (fun z => (Wmat a z * Dmat a z * Z z) i j)
      ((ρ • (Kmat a y * (Wmat a y * Dmat a y * Z y))) i j) y := by
  have hsum : HasDerivAt (fun z => ∑ k : Fin 4, (Wmat a z * Dmat a z) i k * Z z k j)
      (∑ k : Fin 4, (Nmat a y i k * Z y k j + (Wmat a y * Dmat a y) i k * Gm k j)) y :=
    HasDerivAt.fun_sum (fun k _ => (h.hasDerivAt_WD hy ha hb i k).mul (hZ k j))
  have hval := transfer_matrix_identity h (show y ∈ Icc (0 : ℝ) 1 from ⟨hy.1.le, hy.2.le⟩) ρ (Z y)
  rw [← hG] at hval
  have hvalij := congrFun (congrFun hval i) j
  simp only [Matrix.add_apply, Matrix.mul_apply] at hvalij
  have e : (∑ k : Fin 4, (Nmat a y i k * Z y k j + (Wmat a y * Dmat a y) i k * Gm k j))
      = (ρ • (Kmat a y * (Wmat a y * Dmat a y * Z y))) i j := by
    rw [← hvalij, Finset.sum_add_distrib]
    rfl
  rw [e] at hsum
  simpa only [Matrix.mul_apply] using hsum


theorem ac_sum {n : ℕ} (f : Fin n → ℝ → ℂ) (hf : ∀ k, AbsolutelyContinuousOnInterval (f k) 0 1) :
    AbsolutelyContinuousOnInterval (fun y => ∑ k, f k y) 0 1 := by
  classical
  have : ∀ s : Finset (Fin n), AbsolutelyContinuousOnInterval (fun y => ∑ k ∈ s, f k y) 0 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simpa using (LipschitzWith.const (0 : ℂ)).lipschitzOnWith.absolutelyContinuousOnInterval
    | insert k s hk ih =>
      simp only [Finset.sum_insert hk]
      exact (hf k).fun_add ih
  exact this Finset.univ

theorem HypH.transfer (h : HypH a m κ) (ρ : ℂ) {Z : ℝ → Matrix (Fin 4) (Fin 4) ℂ}
    (hint : ∀ i j, IntervalIntegrable
      (fun x => ((Atilde a x + ρ • Lam a x) * Z x) i j) volume 0 1)
    (hZ : IsMatSol (fun x => Atilde a x + ρ • Lam a x) Z) :
    IsSol a ρ (fun x => Wmat a x * Dmat a x * Z x) := by
  have hZac := matSol_entry_ac hZ hint
  have hZder := matSol_ae_deriv hZ hint
  have hYac : ∀ i j, AbsolutelyContinuousOnInterval
      (fun y => (Wmat a y * Dmat a y * Z y) i j) 0 1 := by
    intro i j
    have term : ∀ k, AbsolutelyContinuousOnInterval
        (fun y => (Wmat a y * Dmat a y) i k * Z y k j) 0 1 := fun k => by
      simpa using (h.ac_WD i k).fun_smul (hZac k j)
    have hs := ac_sum (fun k y => (Wmat a y * Dmat a y) i k * Z y k j) term
    simpa only [Matrix.mul_apply] using hs
  have hYc : ∀ i j, ContinuousOn (fun y => (Wmat a y * Dmat a y * Z y) i j) (Icc 0 1) := by
    intro i j
    simpa [uIcc_of_le (zero_le_one' ℝ)] using (hYac i j).continuousOn
  have hgood := ae_good h
  intro x hx i j
  have hF'c : ContinuousOn (fun y => (ρ • (Kmat a y * (Wmat a y * Dmat a y * Z y))) i j)
      (Icc 0 1) := by
    simp only [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
    exact continuousOn_const.mul (continuousOn_finsetSum _ (fun l _ =>
      (h.continuousOn_Kmat i l).mul (hYc l j)))
  have hder : ∀ᵐ y : ℝ, y ∈ Icc (0 : ℝ) 1 → HasDerivAt
      (fun z => (Wmat a z * Dmat a z * Z z) i j)
      ((ρ • (Kmat a y * (Wmat a y * Dmat a y * Z y))) i j) y := by
    apply ae_Icc_of_Ioo
    filter_upwards [hgood, hZder] with y hy1 hy2 hyI
    obtain ⟨ha, hb⟩ := hy1 hyI
    exact h.hasDerivAt_Y hyI ha hb ρ (hy2 hyI) rfl i j
  have hsub : Icc (0 : ℝ) x ⊆ Icc 0 1 := Icc_subset_Icc le_rfl hx.2
  have hx' : uIcc (0 : ℝ) x ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le hx.1, uIcc_of_le (zero_le_one' ℝ)]
    exact hsub
  have hint' : IntervalIntegrable
      (fun y => (ρ • (Kmat a y * (Wmat a y * Dmat a y * Z y))) i j) volume 0 x :=
    (hF'c.mono hsub).intervalIntegrable_of_Icc hx.1
  have key := complex_ac_integral_eq_sub ((hYac i j).mono hx') hint'
    (by
      filter_upwards [hder] with y hy hyu
      rw [uIcc_of_le hx.1] at hyu
      exact hy ⟨hyu.1, hyu.2.trans hx.2⟩)
  change (Wmat a x * Dmat a x * Z x) i j = (Wmat a 0 * Dmat a 0 * Z 0) i j + _
  rw [key]
  ring


theorem Lam_eq (a : ℝ → ℝ) (x : ℝ) (ρ : ℂ) :
    ρ • Lam a x = (Complex.I * ρ) •
      Matrix.diagonal fun c => ((sgn c * tau a (chan c) x : ℝ) : ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Lam]
    ring
  · simp [Lam, hij]

end Anal
end Involution.GeneralBC
