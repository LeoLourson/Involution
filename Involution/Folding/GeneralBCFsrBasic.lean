module

public import Involution.Folding.GeneralBCAsymptoticCoeffTransfer
public import Involution.Folding.GeneralBCAsymptoticCoeffW21
public import Involution.Folding.GeneralBCIntegrable

/-! # lem:fsr, lem:fsr2: вспомогательные факты (G2c, часть (а))

Суммируемость `Kmat`; попарное различие функций `c_j = sgn_j τ_{chan j}`; мост от интегрального
уравнения `Z' = (B + ρ·i·diag c) Z` внешних теорем S51/S54 к `IsSol a ρ (W D (I + R) E)`. -/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Involution.GeneralBC
section Basic
variable {a : ℝ → ℝ} {m κ : ℝ}

/-- Каждый элемент `Kmat a` интервально интегрируем на `[0,1]` при (H). -/
theorem HypH.kmat_intervalIntegrable (h : HypH a m κ) (i j : Fin 4) :
    IntervalIntegrable (fun x => Kmat a x i j) volume 0 1 :=
  (h.continuousOn_Kmat i j).intervalIntegrable_of_Icc (zero_le_one' ℝ)

/-- Гипотеза `hK` леммы `isSol_integrable` выполнена при `Hyp a`. -/
theorem Kmat_intervalIntegrable (ha : Hyp a) (i j : Fin 4) :
    IntervalIntegrable (fun x => Kmat a x i j) volume 0 1 := by
  obtain ⟨m, κ, h⟩ := ha
  exact h.kmat_intervalIntegrable i j

/-- Функции `c_j(x) = sgn_j τ_{chan j}(x)`, формирующие диагональ `Λ`. -/
def cfun (a : ℝ → ℝ) (j : Fin 4) (x : ℝ) : ℝ := sgn j * tau a (chan j) x

theorem cfun_zero (a : ℝ → ℝ) (x : ℝ) : cfun a 0 x = tau a 1 x := by simp [cfun, sgn, chan]
theorem cfun_one (a : ℝ → ℝ) (x : ℝ) : cfun a 1 x = -tau a 1 x := by simp [cfun, sgn, chan]
theorem cfun_two (a : ℝ → ℝ) (x : ℝ) : cfun a 2 x = tau a (-1) x := by simp [cfun, sgn, chan]
theorem cfun_three (a : ℝ → ℝ) (x : ℝ) : cfun a 3 x = -tau a (-1) x := by simp [cfun, sgn, chan]

theorem HypH.cfun_ne (h : HypH a m κ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) {i j : Fin 4}
    (hij : i ≠ j) : cfun a i x ≠ cfun a j x := by
  have h1 := h.tau_pos (Or.inl rfl) hx
  have h2 := h.tau_pos (Or.inr rfl) hx
  have h3 := h.tau_lt hx
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | (simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, cfun_zero, cfun_one,
        cfun_two, cfun_three]
       intro hc
       linarith)

theorem HypH.continuousOn_cfun (h : HypH a m κ) (j : Fin 4) :
    ContinuousOn (cfun a j) (Icc 0 1) :=
  continuousOn_const.mul (acc_cont (h.ac_tau (chan_eq j)))

theorem HypH.ac_cfun (h : HypH a m κ) (j : Fin 4) :
    AbsolutelyContinuousOnInterval (cfun a j) 0 1 :=
  (h.ac_tau (chan_eq j)).const_mul (sgn j)

/-- Диагональ `ρ • Λ` в записи S51/S54. -/
theorem Lam_eq_cfun (a : ℝ → ℝ) (x : ℝ) (ρ : ℂ) :
    ρ • Lam a x = ρ • Matrix.diagonal fun j => Complex.I * (cfun a j x : ℂ) := by
  congr 1
  unfold Lam cfun
  congr 1
  funext j
  push_cast
  ring

theorem integral_cfun (a : ℝ → ℝ) (j : Fin 4) (x : ℝ) :
    (∫ t in (0 : ℝ)..x, cfun a j t) = sgn j * tPhase a (chan j) x := by
  unfold cfun tPhase
  rw [intervalIntegral.integral_const_mul]

theorem exp_cfun_eq (a : ℝ → ℝ) (x : ℝ) (ρ : ℂ) :
    (Matrix.diagonal fun j =>
      Complex.exp (ρ * (Complex.I * ((∫ t in (0 : ℝ)..x, cfun a j t : ℝ) : ℂ)))) = Emat a x ρ := by
  unfold Emat
  congr 1
  funext j
  rw [integral_cfun]
  congr 1
  push_cast
  ring

/-- Элементы `Ã + ρ Λ` суммируемы на `[0,1]`. -/
theorem HypH.intervalIntegrable_AtildeLam (h : HypH a m κ) (ρ : ℂ) (i j : Fin 4) :
    IntervalIntegrable (fun x => (Atilde a x + ρ • Lam a x) i j) volume 0 1 := by
  have h1 := h.integrable_Atilde i j
  have h2 : IntervalIntegrable (fun x => (ρ • Lam a x) i j) volume 0 1 := by
    simp_rw [Lam_eq_cfun]
    by_cases hij : i = j
    · subst hij
      have hc : ContinuousOn
          (fun x => (ρ • Matrix.diagonal fun j => Complex.I * (cfun a j x : ℂ)) i i) (Icc 0 1) := by
        simp only [Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
        exact continuousOn_const.mul (continuousOn_const.mul
          (Complex.continuous_ofReal.comp_continuousOn (h.continuousOn_cfun i)))
      exact hc.intervalIntegrable_of_Icc (zero_le_one' ℝ)
    · simp [Matrix.diagonal_apply_ne _ hij]
  simpa using h1.add h2

/-- Замена матрицы системы и решения почти всюду на `[0,1]` сохраняет `IsMatSol`. -/
theorem isMatSol_congr {M M' Zb Z : ℝ → Matrix (Fin 4) (Fin 4) ℂ}
    (hZb : ∀ x ∈ Icc (0 : ℝ) 1, Zb x = Z x)
    (hM : ∀ᵐ t : ℝ, t ∈ Icc (0 : ℝ) 1 → M t = M' t) (hsol : IsMatSol M Zb) :
    IsMatSol M' Z := by
  intro x hx i j
  rw [← hZb x hx, ← hZb 0 ⟨le_rfl, zero_le_one⟩, hsol x hx i j]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hM] with t ht htI
  rw [uIoc_of_le hx.1] at htI
  have htm : t ∈ Icc (0 : ℝ) 1 := ⟨htI.1.le, htI.2.trans hx.2⟩
  rw [hZb t htm, ht htm]

/-- Мост: решение интегрального уравнения внешних теорем даёт `IsSol a ρ (W D (I + R) E)`.
`B` совпадает с `Ã` почти всюду на `[0,1]`, его диагональные интегралы нулевые. -/
theorem HypH.fsr_bridge (h : HypH a m κ) (ρ : ℂ) (R : ℝ → Matrix (Fin 4) (Fin 4) ℂ)
    (B : ℝ → Matrix (Fin 4) (Fin 4) ℂ)
    (hB : ∀ᵐ x : ℝ, x ∈ Icc (0 : ℝ) 1 → Atilde a x = B x)
    (hdiag : ∀ x ∈ Icc (0 : ℝ) 1, ∀ j, (∫ t in (0 : ℝ)..x, B t j j) = 0)
    (hsol : IsMatSol (fun x => B x + ρ • Matrix.diagonal fun j => Complex.I * (cfun a j x : ℂ))
      (fun x => Matrix.diagonal (fun j => Complex.exp (∫ t in (0 : ℝ)..x, B t j j)) *
        (1 + R x) *
        Matrix.diagonal fun j => Complex.exp
          (ρ * (Complex.I * ((∫ t in (0 : ℝ)..x, cfun a j t : ℝ) : ℂ))))) :
    IsSol a ρ (fun x => Wmat a x * Dmat a x * (1 + R x) * Emat a x ρ) := by
  have hZeq : ∀ x ∈ Icc (0 : ℝ) 1,
      (Matrix.diagonal (fun j => Complex.exp (∫ t in (0 : ℝ)..x, B t j j)) * (1 + R x) *
        Matrix.diagonal fun j => Complex.exp
          (ρ * (Complex.I * ((∫ t in (0 : ℝ)..x, cfun a j t : ℝ) : ℂ)))) =
      (1 + R x) * Emat a x ρ := by
    intro x hx
    have : (Matrix.diagonal fun j => Complex.exp (∫ t in (0 : ℝ)..x, B t j j)) = 1 := by
      rw [← Matrix.diagonal_one]
      congr 1
      funext j
      rw [hdiag x hx j, Complex.exp_zero]
    rw [this, one_mul, exp_cfun_eq]
  have hsol2 : IsMatSol (fun x => Atilde a x + ρ • Lam a x) (fun x => (1 + R x) * Emat a x ρ) :=
    isMatSol_congr hZeq (by
      filter_upwards [hB] with t ht htm
      rw [← ht htm, Lam_eq_cfun]) hsol
  have hint := isMatSol_integrable (fun i j => h.intervalIntegrable_AtildeLam ρ i j) hsol2
  have := h.transfer ρ hint hsol2
  intro x hx i j
  have h1 := this x hx i j
  simpa only [Matrix.mul_assoc] using h1

end Basic
end Involution.GeneralBC

end
