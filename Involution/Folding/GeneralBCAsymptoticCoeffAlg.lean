module

public import Involution.Folding.GeneralBCAsymptoticCoeffBasic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Алгебра сложенной системы: `KW = WΛ`, обратная к `W`, `Ã` (G2a, часть (б))

`Λ = diag(i s τ_±)`; явная `W⁻¹` (строка `¼(1, χ/k, 1/λ, χ/(kλ))`); `det W = 16 k² τ_+ τ_-`;
`Kmat * Wmat = Wmat * Lam` (собственные векторы `K`); матрица `Ã = -(WD)⁻¹(WD)'` записана явно
через `dk = deriv k`, `dtau = deriv τ`: нулевая диагональ, внутри канала `τ'/(2τ)`, между
каналами `(k'/(4k))(1 + s'τ'/(sτ)) D_{c'}/D_c`. Тождество `W D Ã = -(W'D + W D')`
доказано поэлементно. Дифференцирование и интегрируемость — в следующем модуле. -/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Involution.GeneralBC
section Alg
variable {a : ℝ → ℝ} {m κ : ℝ}

/-- `Λ(x) = diag(i s τ_χ)`. -/
def Lam (a : ℝ → ℝ) (x : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal fun c => Complex.I * (sgn c : ℂ) * (tau a (chan c) x : ℂ)

theorem chan_eq (c : Fin 4) : chan c = 1 ∨ chan c = -1 := by
  unfold chan; split_ifs <;> simp

theorem sgn_eq (c : Fin 4) : sgn c = 1 ∨ sgn c = -1 := by
  unfold sgn; split_ifs <;> simp

theorem HypH.tau_sq_eq (h : HypH a m κ) {s : ℝ} (hs : s = 1 ∨ s = -1) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    tau a s x ^ 2 = (1 - a x * a (-x))⁻¹ * (1 - s * Real.sqrt (a x * a (-x))) := by
  have h1 := h.tau_sq_mul hs hx
  have hσ := h.sigma_pos hs hx
  have hp := h.pos_p hx
  have hr := h.sqrt_lt_one hx
  have hr0 := h.sqrt_pos' hx
  have hsq := Real.sq_sqrt hp.le
  have hσ' : sigma a s x = 1 + s * Real.sqrt (a x * a (-x)) := rfl
  have : 1 - a x * a (-x) =
      (1 + s * Real.sqrt (a x * a (-x))) * (1 - s * Real.sqrt (a x * a (-x))) := by
    rcases hs with rfl | rfl <;> nlinarith
  have hne : 1 - s * Real.sqrt (a x * a (-x)) ≠ 0 := by
    rcases hs with rfl | rfl <;> intro h0 <;> nlinarith
  have ht : tau a s x ^ 2 = (sigma a s x)⁻¹ := eq_inv_of_mul_eq_one_left h1
  have hne' : sigma a s x ≠ 0 := hσ.ne'
  rw [ht, this]
  rw [hσ'] at hne' ⊢
  field_simp

theorem HypH.b_eq (h : HypH a m κ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    a (-x) = Real.sqrt (a x * a (-x)) * kfun a x := by
  have h1 := h.kfun_sq hx
  have h2 := h.kfun_mul_a hx
  calc a (-x) = kfun a x ^ 2 * a x := h1.symm
    _ = kfun a x * (kfun a x * a x) := by ring
    _ = _ := by rw [h2, mul_comm]

theorem HypH.E3 (h : HypH a m κ) {χ : ℝ} (hχ : χ = 1 ∨ χ = -1) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    -(1 - a x * a (-x))⁻¹ + (1 - a x * a (-x))⁻¹ * a x * (χ * kfun a x) = -(tau a χ x) ^ 2 := by
  have hk := h.kfun_mul_a hx
  rw [h.tau_sq_eq hχ hx]
  rcases hχ with rfl | rfl
  · linear_combination (1 - a x * a (-x))⁻¹ * hk
  · linear_combination (-(1 - a x * a (-x))⁻¹) * hk

theorem HypH.E4 (h : HypH a m κ) {χ : ℝ} (hχ : χ = 1 ∨ χ = -1) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    (1 - a x * a (-x))⁻¹ * a (-x) - (1 - a x * a (-x))⁻¹ * (χ * kfun a x) =
      -(tau a χ x) ^ 2 * (χ * kfun a x) := by
  have hb := h.b_eq hx
  rw [h.tau_sq_eq hχ hx]
  rcases hχ with rfl | rfl
  · linear_combination (1 - a x * a (-x))⁻¹ * hb
  · linear_combination (1 - a x * a (-x))⁻¹ * hb

theorem HypH.Kmat_mul_Wmat (h : HypH a m κ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    Kmat a x * Wmat a x = Wmat a x * Lam a x := by
  ext i c
  have hχ := chan_eq c
  have E3 := h.E3 hχ hx
  have E4 := h.E4 hχ hx
  have E3c : ((-(1 - a x * a (-x))⁻¹ + (1 - a x * a (-x))⁻¹ * a x * (chan c * kfun a x) : ℝ) : ℂ)
      = ((-(tau a (chan c) x) ^ 2 : ℝ) : ℂ) := by rw [E3]
  have E4c : (((1 - a x * a (-x))⁻¹ * a (-x) - (1 - a x * a (-x))⁻¹ * (chan c * kfun a x) : ℝ) : ℂ)
      = ((-(tau a (chan c) x) ^ 2 * (chan c * kfun a x) : ℝ) : ℂ) := by rw [E4]
  push_cast at E3c E4c
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hs2 : (sgn c : ℂ) ^ 2 = 1 := by
    rcases sgn_eq c with h1 | h1 <;> rw [h1] <;> norm_num
  rw [Lam, Matrix.mul_diagonal]
  fin_cases i <;> simp only [Kmat, Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_mul, Wmat, gvec, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
    Matrix.mul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.sum_univ_four, mul_one,
    zero_mul, add_zero, one_mul, zero_add, neg_mul]
  all_goals first
    | ring1
    | linear_combination E3c - (tau a (chan c) x : ℂ) ^ 2 * (sgn c : ℂ) ^ 2 * hI
        + (tau a (chan c) x : ℂ) ^ 2 * hs2
    | linear_combination E4c
        - (tau a (chan c) x : ℂ) ^ 2 * (sgn c : ℂ) ^ 2 * ((chan c : ℝ) * kfun a x : ℂ) * hI
        + (tau a (chan c) x : ℂ) ^ 2 * ((chan c : ℝ) * kfun a x : ℂ) * hs2

/-- Явная обратная к `W`: строка `c` равна `¼(1, χ/k, 1/λ, χ/(kλ))`, `λ = i s τ_χ`. -/
def Winv (a : ℝ → ℝ) (x : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun c j =>
    (1 / 4 : ℂ) * ![1, (chan c : ℂ) / (kfun a x : ℂ),
      1 / (Complex.I * (sgn c : ℂ) * (tau a (chan c) x : ℂ)),
      (chan c : ℂ) / ((kfun a x : ℂ) * (Complex.I * (sgn c : ℂ) * (tau a (chan c) x : ℂ)))] j

theorem Winv_mul_Wmat {a : ℝ → ℝ} {x : ℝ} (hk : kfun a x ≠ 0) (h1 : tau a 1 x ≠ 0)
    (h2 : tau a (-1) x ≠ 0) : Winv a x * Wmat a x = 1 := by
  have hk' : (kfun a x : ℂ) ≠ 0 := by exact_mod_cast hk
  have h1' : (tau a 1 x : ℂ) ≠ 0 := by exact_mod_cast h1
  have h2' : (tau a (-1) x : ℂ) ≠ 0 := by exact_mod_cast h2
  ext c c'
  fin_cases c <;> fin_cases c' <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Winv, Wmat, gvec, chan, sgn] <;>
    field_simp <;> (try simp only [Complex.I_sq]) <;> ring

theorem det_Wmat (a : ℝ → ℝ) (x : ℝ) :
    (Wmat a x).det = 16 * (kfun a x : ℂ) ^ 2 * (tau a 1 x : ℂ) * (tau a (-1) x : ℂ) := by
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Wmat, gvec, chan, sgn]
  simp [Fin.succAbove, Matrix.submatrix]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Производная `k` (в смысле `deriv`; на практике берётся в точках дифференцируемости). -/
def dk (a : ℝ → ℝ) (x : ℝ) : ℝ := deriv (kfun a) x

/-- Производная `τ_s`. -/
def dtau (a : ℝ → ℝ) (s : ℝ) (x : ℝ) : ℝ := deriv (tau a s) x

/-- `W'`: покомпонентная производная `W` через `dk`, `dtau`. -/
def Wder (a : ℝ → ℝ) (x : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun r c =>
    ![0, ((chan c * dk a x : ℝ) : ℂ), Complex.I * (sgn c : ℂ) * (dtau a (chan c) x : ℂ),
      Complex.I * (sgn c : ℂ) * (chan c : ℂ) *
        ((dtau a (chan c) x : ℂ) * (kfun a x : ℂ) + (tau a (chan c) x : ℂ) * (dk a x : ℂ))] r

/-- Поправочный множитель `a_± = -k'/(2k) - τ_±'/(2τ_±)` (`D'/D`) в канале `c`. -/
def acoef (a : ℝ → ℝ) (c : Fin 4) (x : ℝ) : ℝ :=
  -(dk a x / (2 * kfun a x)) - dtau a (chan c) x / (2 * tau a (chan c) x)

/-- `D'` : `D · a_±`. -/
def Dder (a : ℝ → ℝ) (x : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal fun c => (Damp a (chan c) x : ℂ) * (acoef a c x : ℂ)

/-- `(WD)'` через `W'`, `D'`. -/
def Nmat (a : ℝ → ℝ) (x : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Wder a x * Dmat a x + Wmat a x * Dder a x

/-- Матрица `Ã = -(WD)⁻¹ (WD)'`, записанная явно: нулевая диагональ, внутри канала
`τ'/(2τ)`, между каналами `(k'/(4k))(1 + s'τ'/(sτ)) D_{c'}/D_c`. -/
def Atilde (a : ℝ → ℝ) (x : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun c c' =>
    if c = c' then 0
    else if chan c = chan c' then ((dtau a (chan c) x / (2 * tau a (chan c) x) : ℝ) : ℂ)
    else ((dk a x / (4 * kfun a x) : ℝ) : ℂ) *
      (1 + ((sgn c' * tau a (chan c') x : ℝ) : ℂ) / ((sgn c * tau a (chan c) x : ℝ) : ℂ)) *
      ((Damp a (chan c') x / Damp a (chan c) x : ℝ) : ℂ)

theorem Atilde_diag (a : ℝ → ℝ) (x : ℝ) (c : Fin 4) : Atilde a x c c = 0 := by
  simp [Atilde]

theorem Dmat_mul_Atilde {a : ℝ → ℝ} {x : ℝ} (hk : kfun a x ≠ 0) (h1 : tau a 1 x ≠ 0)
    (h2 : tau a (-1) x ≠ 0) (d1 : Damp a 1 x ≠ 0) (d2 : Damp a (-1) x ≠ 0) :
    Dmat a x * Atilde a x = -(Winv a x * Nmat a x) := by
  have hk' : (kfun a x : ℂ) ≠ 0 := by exact_mod_cast hk
  have h1' : (tau a 1 x : ℂ) ≠ 0 := by exact_mod_cast h1
  have h2' : (tau a (-1) x : ℂ) ≠ 0 := by exact_mod_cast h2
  have d1' : (Damp a 1 x : ℂ) ≠ 0 := by exact_mod_cast d1
  have d2' : (Damp a (-1) x : ℂ) ≠ 0 := by exact_mod_cast d2
  have e1 : ((1 : ℝ) = -1) = False := by norm_num
  have e2 : ((-1 : ℝ) = 1) = False := by norm_num
  ext c c'
  rw [Dmat, Matrix.diagonal_mul]
  fin_cases c <;> fin_cases c' <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Winv, Nmat, Wder, Wmat, Dmat, Dder, Atilde, gvec,
      acoef, chan, sgn, e1, e2, Matrix.add_apply, Matrix.diagonal_apply] <;>
    field_simp <;> (try simp only [Complex.I_sq]) <;> ring

theorem Wmat_mul_Winv {a : ℝ → ℝ} {x : ℝ} (hk : kfun a x ≠ 0) (h1 : tau a 1 x ≠ 0)
    (h2 : tau a (-1) x ≠ 0) : Wmat a x * Winv a x = 1 :=
  mul_eq_one_comm.mp (Winv_mul_Wmat hk h1 h2)

theorem det_Wmat_ne_zero {a : ℝ → ℝ} {x : ℝ} (hk : kfun a x ≠ 0) (h1 : tau a 1 x ≠ 0)
    (h2 : tau a (-1) x ≠ 0) : (Wmat a x).det ≠ 0 := by
  rw [det_Wmat]
  have hk' : (kfun a x : ℂ) ≠ 0 := by exact_mod_cast hk
  have h1' : (tau a 1 x : ℂ) ≠ 0 := by exact_mod_cast h1
  have h2' : (tau a (-1) x : ℂ) ≠ 0 := by exact_mod_cast h2
  simp [hk', h1', h2']

theorem WDAtilde {a : ℝ → ℝ} {x : ℝ} (hk : kfun a x ≠ 0) (h1 : tau a 1 x ≠ 0)
    (h2 : tau a (-1) x ≠ 0) (d1 : Damp a 1 x ≠ 0) (d2 : Damp a (-1) x ≠ 0) :
    Wmat a x * Dmat a x * Atilde a x = -Nmat a x := by
  rw [Matrix.mul_assoc, Dmat_mul_Atilde hk h1 h2 d1 d2, Matrix.mul_neg, ← Matrix.mul_assoc,
    Wmat_mul_Winv hk h1 h2, Matrix.one_mul]

theorem Kmat_mul_WD {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    Kmat a x * (Wmat a x * Dmat a x) = Wmat a x * Dmat a x * Lam a x := by
  rw [← Matrix.mul_assoc, h.Kmat_mul_Wmat hx, Matrix.mul_assoc, Matrix.mul_assoc, Lam, Dmat,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 2
  ext c
  ring

theorem HypH.Winv_bound (h : HypH a m κ) :
    ∃ C : ℝ, ∀ x ∈ Icc (-1 : ℝ) 1, ∀ i j, ‖Winv a x i j‖ ≤ C := by
  obtain ⟨c, C, hc, hb⟩ := h.kfun_abs_bounds
  set t0 := (Real.sqrt (1 + Real.sqrt κ))⁻¹ with ht0
  have ht0pos : 0 < t0 := inv_pos.2 (Real.sqrt_pos.2 (by linarith [h.sqrtK_pos]))
  refine ⟨(1 / 4) * ((1 + c⁻¹) * (1 + t0⁻¹)), fun x hx i j => ?_⟩
  have hk := (hb x hx).1
  have hτc : t0 ≤ tau a (chan i) x := h.tau_ge (chan_eq i) hx
  have htpos : 0 < tau a (chan i) x := lt_of_lt_of_le ht0pos hτc
  have hkpos : 0 < |kfun a x| := lt_of_lt_of_le hc hk
  have hs1 : |sgn i| = 1 := by rcases sgn_eq i with h1 | h1 <;> rw [h1] <;> simp
  have hχ1 : |chan i| = 1 := by rcases chan_eq i with h1 | h1 <;> rw [h1] <;> simp
  have hinvt : (tau a (chan i) x)⁻¹ ≤ t0⁻¹ := inv_anti₀ ht0pos hτc
  have hinvk : |kfun a x|⁻¹ ≤ c⁻¹ := inv_anti₀ hc hk
  have hp1 : 0 ≤ (tau a (chan i) x)⁻¹ := (inv_pos.2 htpos).le
  have hp2 : 0 ≤ |kfun a x|⁻¹ := (inv_pos.2 hkpos).le
  have hb1 : 0 ≤ c⁻¹ := (inv_pos.2 hc).le
  have hb2 : 0 ≤ t0⁻¹ := (inv_pos.2 ht0pos).le
  have key : ‖Winv a x i j‖ * 4 ≤ (1 + c⁻¹) * (1 + t0⁻¹) := by
    unfold Winv
    fin_cases j <;>
      simp [hχ1, hs1, abs_of_pos htpos] <;>
      nlinarith [mul_nonneg hp1 hp2, mul_le_mul hinvk hinvt hp1 hb1, mul_nonneg hb1 hb2]
  linarith

end Alg







end Involution.GeneralBC
