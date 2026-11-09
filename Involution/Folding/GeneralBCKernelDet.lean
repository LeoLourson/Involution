module

public import Involution.Folding.GeneralBCKernelVec

/-! # Лемма `lem:kernel`(c): `det 𝔘⁰(ρ) = c_U F(ρ)` (C24 шаги 7–8, формула (7))

Элементы `𝔘⁰` по строкам, разложение 4×4-определителя и сведение к тождеству в `exp(iρℓ_±)`,
разбор по видам форм `(0,0)`, `(1,1)`, `(1,0)` и знаку `ε`. Нормировка `D(0) = 1` записи C24. -/

@[expose] public noncomputable section

open Matrix

namespace Involution
namespace GeneralBC


theorem det4 (M : Matrix (Fin 4) (Fin 4) ℂ) : M.det =
    M 0 0 * (M 1 1 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) - M 1 2 * (M 2 1 * M 3 3 - M 2 3 * M 3 1)
      + M 1 3 * (M 2 1 * M 3 2 - M 2 2 * M 3 1))
    - M 0 1 * (M 1 0 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) - M 1 2 * (M 2 0 * M 3 3 - M 2 3 * M 3 0)
      + M 1 3 * (M 2 0 * M 3 2 - M 2 2 * M 3 0))
    + M 0 2 * (M 1 0 * (M 2 1 * M 3 3 - M 2 3 * M 3 1) - M 1 1 * (M 2 0 * M 3 3 - M 2 3 * M 3 0)
      + M 1 3 * (M 2 0 * M 3 1 - M 2 1 * M 3 0))
    - M 0 3 * (M 1 0 * (M 2 1 * M 3 2 - M 2 2 * M 3 1) - M 1 1 * (M 2 0 * M 3 2 - M 2 2 * M 3 0)
      + M 1 2 * (M 2 0 * M 3 1 - M 2 1 * M 3 0)) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix, Fin.succAbove]
  ring

theorem Ufrak0_row0 {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) (U : Forms) (ρ : ℂ) (c : Fin 4) :
    Ufrak0 a U ρ 0 c = 1 - (chan c : ℂ) * (eps a : ℂ) := by
  obtain ⟨c0, c1, c2, c3⟩ := chan_vals
  have hp := Damp_zero h 1 (Or.inl rfl)
  have hm := Damp_zero h (-1) (Or.inr rfl)
  fin_cases c <;>
  simp [Ufrak0, colv, gvec, tPhase_zero, kfun_zero h, hp, hm, c0, c1, c2, c3]

theorem Ufrak0_row1 {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) (U : Forms) (ρ : ℂ) (c : Fin 4) :
    Ufrak0 a U ρ 1 c = Complex.I * (sgn c : ℂ) * (tau0 a (chan c) : ℂ) *
      (1 + (chan c : ℂ) * (eps a : ℂ)) := by
  obtain ⟨c0, c1, c2, c3⟩ := chan_vals
  obtain ⟨s0, s1, s2, s3⟩ := sgn_vals
  have hp := Damp_zero h 1 (Or.inl rfl)
  have hm := Damp_zero h (-1) (Or.inr rfl)
  fin_cases c <;>
  simp [Ufrak0, colv, gvec, tPhase_zero, kfun_zero h, hp, hm, c0, c1, c2, c3, s0, s1, s2, s3,
    tau0] <;> ring

open Classical in
theorem Ufrak0_row2 (a : ℝ → ℝ) (U : Forms) (ρ : ℂ) (c : Fin 4) :
    Ufrak0 a U ρ 2 c = (Damp a (chan c) 1 : ℂ) *
      Complex.exp (Complex.I * (sgn c : ℂ) * ρ * (ell a (chan c) : ℂ)) *
      (if U.HasDeriv 0 then Complex.I * (sgn c : ℂ) * (tau a (chan c) 1 : ℂ) *
        Pc a U 0 (chan c) else Qc a U 0 (chan c)) := by
  by_cases hd : U.HasDeriv 0 <;>
  fin_cases c <;>
  simp [Ufrak0, colv, gvec, U0row, Pc, Qc, hd, chan, sgn, ell, varkappa, Fin.sum_univ_four] <;> ring

open Classical in
theorem Ufrak0_row3 (a : ℝ → ℝ) (U : Forms) (ρ : ℂ) (c : Fin 4) :
    Ufrak0 a U ρ 3 c = (Damp a (chan c) 1 : ℂ) *
      Complex.exp (Complex.I * (sgn c : ℂ) * ρ * (ell a (chan c) : ℂ)) *
      (if U.HasDeriv 1 then Complex.I * (sgn c : ℂ) * (tau a (chan c) 1 : ℂ) *
        Pc a U 1 (chan c) else Qc a U 1 (chan c)) := by
  by_cases hd : U.HasDeriv 1 <;>
  fin_cases c <;>
  simp [Ufrak0, colv, gvec, U0row, Pc, Qc, hd, chan, sgn, ell, varkappa, Fin.sum_univ_four] <;> ring

theorem kind_k00 {U : Forms} (h0 : ¬ U.HasDeriv 0) (h1 : ¬ U.HasDeriv 1) :
    U.kind = Forms.Kind.k00 := by simp [Forms.kind, h0, h1]
theorem kind_k11 {U : Forms} (h0 : U.HasDeriv 0) (h1 : U.HasDeriv 1) :
    U.kind = Forms.Kind.k11 := by simp [Forms.kind, h0, h1]
theorem kind_k10 {U : Forms} (h0 : U.HasDeriv 0) (h1 : ¬ U.HasDeriv 1) :
    U.kind = Forms.Kind.k10 := by simp [Forms.kind, h0, h1]

theorem cos_exp' (r l : ℂ) : Complex.cos (r * l) =
    (Complex.exp (Complex.I * r * l) + (Complex.exp (Complex.I * r * l))⁻¹) / 2 := by
  rw [Complex.cos, ← Complex.exp_neg]; ring_nf
theorem sin_exp' (r l : ℂ) : Complex.sin (r * l) =
    ((Complex.exp (Complex.I * r * l))⁻¹ - Complex.exp (Complex.I * r * l)) * Complex.I / 2 := by
  rw [Complex.sin, ← Complex.exp_neg]; ring_nf
theorem epos (r l : ℂ) : Complex.exp (Complex.I * 1 * r * l) = Complex.exp (Complex.I * r * l) := by
  ring_nf
theorem eneg (r l : ℂ) : Complex.exp (Complex.I * (-1) * r * l) =
    (Complex.exp (Complex.I * r * l))⁻¹ := by
  rw [← Complex.exp_neg]; ring_nf

theorem kernel_det_k10 {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) (U : Forms)
    (h0 : U.HasDeriv 0) (h1 : ¬ U.HasDeriv 1) (ρ : ℂ) :
    (Ufrak0 a U ρ).det = cU a U * Fchar a U ρ := by
  classical
  obtain ⟨c0, c1, c2, c3⟩ := chan_vals
  obtain ⟨s0, s1, s2, s3⟩ := sgn_vals
  rw [det4]
  simp only [Ufrak0_row0 h, Ufrak0_row1 h, Ufrak0_row2, Ufrak0_row3, c0, c1, c2, c3, s0, s1, s2, s3,
    h0, h1, ↓reduceIte, Complex.ofReal_neg, Complex.ofReal_one, epos, eneg]
  have hk := kind_k10 h0 h1
  have hX := Complex.exp_ne_zero (Complex.I * ρ * (ell a 1 : ℂ))
  have hY := Complex.exp_ne_zero (Complex.I * ρ * (ell a (-1) : ℂ))
  have ht1 := (tau0_pos h 1 (Or.inl rfl)).ne'
  have ht2 := (tau0_pos h (-1) (Or.inr rfl)).ne'
  unfold cU gammaU Fchar calA calB Forms.J0 Forms.J1 Pc Qc
  simp only [hk]
  rw [cos_exp', cos_exp', sin_exp', sin_exp']
  have hom1 : tau a 1 1 = omega a 1 := rfl
  have hom2 : tau a (-1) 1 = omega a (-1) := rfl
  try simp only [hom1, hom2]
  by_cases hε : 0 < a 0
  · have he : eps a = 1 := by simp [eps, hε]
    simp only [he, hε, ↓reduceIte, Complex.ofReal_one]
    generalize Complex.exp (Complex.I * ρ * (ell a 1 : ℂ)) = X at *
    generalize Complex.exp (Complex.I * ρ * (ell a (-1) : ℂ)) = Y at *
    push_cast
    field_simp
    ring_nf
    try simp only [Complex.I_sq]
    try ring_nf
  · have he : eps a = -1 := by simp [eps, hε]
    simp only [he, hε, ↓reduceIte, Complex.ofReal_neg, Complex.ofReal_one]
    generalize Complex.exp (Complex.I * ρ * (ell a 1 : ℂ)) = X at *
    generalize Complex.exp (Complex.I * ρ * (ell a (-1) : ℂ)) = Y at *
    push_cast
    field_simp
    ring_nf
    try simp only [Complex.I_sq]
    try ring_nf

theorem kernel_det_k00 {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) (U : Forms)
    (h0 : ¬ U.HasDeriv 0) (h1 : ¬ U.HasDeriv 1) (ρ : ℂ) :
    (Ufrak0 a U ρ).det = cU a U * Fchar a U ρ := by
  classical
  obtain ⟨c0, c1, c2, c3⟩ := chan_vals
  obtain ⟨s0, s1, s2, s3⟩ := sgn_vals
  rw [det4]
  simp only [Ufrak0_row0 h, Ufrak0_row1 h, Ufrak0_row2, Ufrak0_row3, c0, c1, c2, c3, s0, s1, s2, s3,
    h0, h1, ↓reduceIte, Complex.ofReal_neg, Complex.ofReal_one, epos, eneg]
  have hk := kind_k00 h0 h1
  have hX := Complex.exp_ne_zero (Complex.I * ρ * (ell a 1 : ℂ))
  have hY := Complex.exp_ne_zero (Complex.I * ρ * (ell a (-1) : ℂ))
  have ht1 := (tau0_pos h 1 (Or.inl rfl)).ne'
  have ht2 := (tau0_pos h (-1) (Or.inr rfl)).ne'
  unfold cU gammaU Fchar calA calB Forms.J0 Forms.J1 Pc Qc
  simp only [hk]
  rw [cos_exp', cos_exp', sin_exp', sin_exp']
  have hom1 : tau a 1 1 = omega a 1 := rfl
  have hom2 : tau a (-1) 1 = omega a (-1) := rfl
  try simp only [hom1, hom2]
  by_cases hε : 0 < a 0
  · have he : eps a = 1 := by simp [eps, hε]
    simp only [he, hε, ↓reduceIte, Complex.ofReal_one]
    generalize Complex.exp (Complex.I * ρ * (ell a 1 : ℂ)) = X at *
    generalize Complex.exp (Complex.I * ρ * (ell a (-1) : ℂ)) = Y at *
    push_cast
    field_simp
    ring_nf
    try simp only [Complex.I_sq]
    try ring_nf
  · have he : eps a = -1 := by simp [eps, hε]
    simp only [he, hε, ↓reduceIte, Complex.ofReal_neg, Complex.ofReal_one]
    generalize Complex.exp (Complex.I * ρ * (ell a 1 : ℂ)) = X at *
    generalize Complex.exp (Complex.I * ρ * (ell a (-1) : ℂ)) = Y at *
    push_cast
    field_simp
    ring_nf
    try simp only [Complex.I_sq]
    try ring_nf

theorem kernel_det_k11 {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) (U : Forms)
    (h0 : U.HasDeriv 0) (h1 : U.HasDeriv 1) (ρ : ℂ) :
    (Ufrak0 a U ρ).det = cU a U * Fchar a U ρ := by
  classical
  obtain ⟨c0, c1, c2, c3⟩ := chan_vals
  obtain ⟨s0, s1, s2, s3⟩ := sgn_vals
  rw [det4]
  simp only [Ufrak0_row0 h, Ufrak0_row1 h, Ufrak0_row2, Ufrak0_row3, c0, c1, c2, c3, s0, s1, s2, s3,
    h0, h1, ↓reduceIte, Complex.ofReal_neg, Complex.ofReal_one, epos, eneg]
  have hk := kind_k11 h0 h1
  have hX := Complex.exp_ne_zero (Complex.I * ρ * (ell a 1 : ℂ))
  have hY := Complex.exp_ne_zero (Complex.I * ρ * (ell a (-1) : ℂ))
  have ht1 := (tau0_pos h 1 (Or.inl rfl)).ne'
  have ht2 := (tau0_pos h (-1) (Or.inr rfl)).ne'
  unfold cU gammaU Fchar calA calB Forms.J0 Forms.J1 Pc Qc
  simp only [hk]
  rw [cos_exp', cos_exp', sin_exp', sin_exp']
  have hom1 : tau a 1 1 = omega a 1 := rfl
  have hom2 : tau a (-1) 1 = omega a (-1) := rfl
  try simp only [hom1, hom2]
  by_cases hε : 0 < a 0
  · have he : eps a = 1 := by simp [eps, hε]
    simp only [he, hε, ↓reduceIte, Complex.ofReal_one]
    generalize Complex.exp (Complex.I * ρ * (ell a 1 : ℂ)) = X at *
    generalize Complex.exp (Complex.I * ρ * (ell a (-1) : ℂ)) = Y at *
    push_cast
    field_simp
    ring_nf
    try simp only [Complex.I_sq]
    try ring_nf
  · have he : eps a = -1 := by simp [eps, hε]
    simp only [he, hε, ↓reduceIte, Complex.ofReal_neg, Complex.ofReal_one]
    generalize Complex.exp (Complex.I * ρ * (ell a 1 : ℂ)) = X at *
    generalize Complex.exp (Complex.I * ρ * (ell a (-1) : ℂ)) = Y at *
    push_cast
    field_simp
    ring_nf
    try simp only [Complex.I_sq]
    try ring_nf

/-- Лемма `lem:kernel`(c), первое равенство: `det 𝔘⁰(ρ) = c_U F(ρ)` (формула (7) C24 и шаг 8). -/
theorem lem_kernel_det {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms}
    (hU : AdmissibleForms U) (ρ : ℂ) : (Ufrak0 a U ρ).det = cU a U * Fchar a U ρ := by
  have hord := hU.ordered
  by_cases h0 : U.HasDeriv 0 <;> by_cases h1 : U.HasDeriv 1
  · exact kernel_det_k11 h U h0 h1 ρ
  · exact kernel_det_k10 h U h0 h1 ρ
  · exfalso
    simp [Forms.IsOrdered, Forms.ord, h0, h1] at hord
  · exact kernel_det_k00 h U h0 h1 ρ

end GeneralBC
end Involution

