module

public import Involution.Folding.GeneralBCKernelBasis

/-! # Лемма `lem:kernel`(c): постоянные и ненулевость (C24 шаги 7–8, C25 шаг 9)

`det 𝔐(ρ) = J_U F(ρ)`, `J_U = iγ_U/4`, `c_U ≠ 0`, `c_∗ = c_U / (16 τ⁰_+ τ⁰_-)`, невырожденность
миноров `J_0`, `J_1` (под именами `kernel_*`) и `γ_U`.

Нормировка: Lean — `D(0) = 1`, статья — `D(1) = 1`. Множитель: `c_U` статьи
(`cUpaper`) равно `cU / (D_+(1) D_-(1))²`. -/

@[expose] public noncomputable section

open Matrix

namespace Involution
namespace GeneralBC

theorem real_aux {A B p q k : ℝ} (hA : 0 < A) (hB : 0 < B) (hp : 0 < p) (hq : 0 < q) (hk : 0 < k) :
    Real.sqrt (A / (k * p)) * Real.sqrt (B / (k * q)) * k * Real.sqrt (p * q * A * B) = A * B := by
  have h1 : 0 ≤ A / (k * p) := by positivity
  have h2 : 0 ≤ B / (k * q) := by positivity
  have h3 : 0 ≤ k ^ 2 := by positivity
  have h4 : 0 ≤ p * q * A * B := by positivity
  apply (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1
  simp only [mul_pow, Real.sq_sqrt h1, Real.sq_sqrt h2, Real.sq_sqrt h4]
  field_simp

theorem cStar_eq_cU {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) (U : Forms) :
    cStar a U = cU a U / (16 * (tau0 a 1 : ℂ) * (tau0 a (-1) : ℂ)) := by
  have hk : 0 < |varkappa a| := abs_pos.2 (varkappa_ne_zero h)
  have hR := real_aux (tau0_pos h 1 (Or.inl rfl)) (tau0_pos h (-1) (Or.inr rfl))
    (omega_pos h 1 (Or.inl rfl)) (omega_pos h (-1) (Or.inr rfl)) hk
  have hS : 0 < Real.sqrt (omega a 1 * omega a (-1) * tau0 a 1 * tau0 a (-1)) :=
    Real.sqrt_pos.2 (by
      have := omega_pos h 1 (Or.inl rfl); have := omega_pos h (-1) (Or.inr rfl)
      have := tau0_pos h 1 (Or.inl rfl); have := tau0_pos h (-1) (Or.inr rfl); positivity)
  have hC : ((Damp a 1 1 : ℝ) : ℂ) * (Damp a (-1) 1 : ℝ) * ((|varkappa a| : ℝ) : ℂ) *
      (Real.sqrt (omega a 1 * omega a (-1) * tau0 a 1 * tau0 a (-1)) : ℂ) =
      (tau0 a 1 : ℂ) * (tau0 a (-1) : ℂ) := by
    exact_mod_cast hR
  have t1 : (tau0 a 1 : ℂ) ≠ 0 := by exact_mod_cast (tau0_pos h 1 (Or.inl rfl)).ne'
  have t2 : (tau0 a (-1) : ℂ) ≠ 0 := by exact_mod_cast (tau0_pos h (-1) (Or.inr rfl)).ne'
  have k0 : ((|varkappa a| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have s0 : (Real.sqrt (omega a 1 * omega a (-1) * tau0 a 1 * tau0 a (-1)) : ℂ) ≠ 0 := by
    exact_mod_cast hS.ne'
  unfold cStar cU
  have n1 : (4 * ((|varkappa a| : ℝ) : ℂ) *
      (Real.sqrt (omega a 1 * omega a (-1) * tau0 a 1 * tau0 a (-1)) : ℂ)) ≠ 0 := by
    simp [k0, s0]
  have n2 : (16 * (tau0 a 1 : ℂ) * (tau0 a (-1) : ℂ)) ≠ 0 := by simp [t1, t2]
  rw [div_eq_div_iff n1 n2]
  linear_combination (-16 * Complex.I * (eps a : ℂ) * (tau0 a (eps a) : ℂ) * gammaU a U) * hC

theorem row_eq (U : Forms) : U.row = ![U.row 0, U.row 1] := by
  ext j i; fin_cases j <;> rfl

theorem pair_of_linIndep {U : Forms} (hU : U.LinIndep) (s t : ℂ)
    (h : ∀ i, s * U.row 0 i + t * U.row 1 i = 0) : s = 0 ∧ t = 0 := by
  unfold Forms.LinIndep at hU
  rw [row_eq U] at hU
  rw [LinearIndependent.pair_iff] at hU
  apply hU
  ext i; simpa using h i

theorem noDeriv {U : Forms} {j : Fin 2} (h : ¬ U.HasDeriv j) : U.α j 1 = 0 ∧ U.β j 1 = 0 := by
  simp only [Forms.HasDeriv, not_or, not_not] at h; exact h

theorem kernel_J0_ne_zero {U : Forms} (hU : AdmissibleForms U) (hk : U.kind = Forms.Kind.k00) :
    U.J0 ≠ 0 := by
  have h01 : ¬ U.HasDeriv 0 ∧ ¬ U.HasDeriv 1 := by
    by_contra hc
    unfold Forms.kind at hk
    by_cases h : ¬ U.HasDeriv 0 ∧ ¬ U.HasDeriv 1
    · exact hc h
    · simp only [h, ite_false] at hk
      split_ifs at hk
  obtain ⟨a0, b0⟩ := noDeriv h01.1
  obtain ⟨a1, b1⟩ := noDeriv h01.2
  intro hJ
  unfold Forms.J0 at hJ
  have key := pair_of_linIndep hU.indep
  have r1 := key (U.α 1 0) (-U.α 0 0) (by
    intro i; fin_cases i
    · change U.α 1 0 * U.α 0 0 + -U.α 0 0 * U.α 1 0 = 0
      ring
    · change U.α 1 0 * U.α 0 1 + -U.α 0 0 * U.α 1 1 = 0
      rw [a0, a1]; ring
    · change U.α 1 0 * U.β 0 0 + -U.α 0 0 * U.β 1 0 = 0
      linear_combination (-1 : ℂ) * hJ
    · change U.α 1 0 * U.β 0 1 + -U.α 0 0 * U.β 1 1 = 0
      rw [b0, b1]; ring)
  have r2 := key (U.β 1 0) (-U.β 0 0) (by
    intro i; fin_cases i
    · change U.β 1 0 * U.α 0 0 + -U.β 0 0 * U.α 1 0 = 0
      linear_combination hJ
    · change U.β 1 0 * U.α 0 1 + -U.β 0 0 * U.α 1 1 = 0
      rw [a0, a1]; ring
    · change U.β 1 0 * U.β 0 0 + -U.β 0 0 * U.β 1 0 = 0
      ring
    · change U.β 1 0 * U.β 0 1 + -U.β 0 0 * U.β 1 1 = 0
      rw [b0, b1]; ring)
  have z1 : U.α 1 0 = 0 := r1.1
  have z2 : U.α 0 0 = 0 := neg_eq_zero.1 r1.2
  have z3 : U.β 1 0 = 0 := r2.1
  have z4 : U.β 0 0 = 0 := neg_eq_zero.1 r2.2
  have := key 1 0 (by
    intro i; fin_cases i <;> simp [Forms.row, a0, b0, z2, z4])
  exact one_ne_zero this.1

theorem hasDeriv_of_ne {U : Forms} {j : Fin 2} (h : U.α j 1 ≠ 0 ∨ U.β j 1 ≠ 0) : U.HasDeriv j := h

theorem kind_k11_hasDeriv {U : Forms} (hk : U.kind = Forms.Kind.k11) :
    U.HasDeriv 0 ∧ U.HasDeriv 1 := by
  unfold Forms.kind at hk
  by_cases h : ¬ U.HasDeriv 0 ∧ ¬ U.HasDeriv 1
  · simp only [h, and_self] at hk; cases hk
  · simp only [h, ite_false] at hk
    by_cases h' : U.HasDeriv 0 ∧ U.HasDeriv 1
    · exact h'
    · simp only [h', ite_false] at hk; cases hk

theorem J1_aux {U : Forms} (hU : U.IsNormalized) (h0 : U.HasDeriv 0) (l : ℂ)
    (ha : U.α 1 1 - l * U.α 0 1 = 0) (hb : U.β 1 1 - l * U.β 0 1 = 0) (h1 : U.HasDeriv 1) :
    False := by
  classical
  have hc : IsUnit (!![1, 0; -l, 1] : Matrix (Fin 2) (Fin 2) ℂ).det := by
    simp [Matrix.det_fin_two_of]
  have := hU _ hc
  have e0 : (U.combo !![1, 0; -l, 1]).HasDeriv 0 := by
    simpa [Forms.combo, Forms.HasDeriv, Fin.sum_univ_two] using h0
  have e1 : ¬ (U.combo !![1, 0; -l, 1]).HasDeriv 1 := by
    simp only [Forms.HasDeriv, not_or, not_not]
    simp only [Forms.combo, Fin.sum_univ_two]
    constructor
    · simpa [sub_eq_add_neg, add_comm] using ha
    · simpa [sub_eq_add_neg, add_comm] using hb
  simp [Forms.ord, h0, h1, e0, e1] at this

theorem kernel_J1_ne_zero {U : Forms} (hU : AdmissibleForms U) (hk : U.kind = Forms.Kind.k11) :
    U.J1 ≠ 0 := by
  obtain ⟨h0, h1⟩ := kind_k11_hasDeriv hk
  intro hJ
  unfold Forms.J1 at hJ
  rcases h0 with ha | hb
  · exact J1_aux hU.normalized (Or.inl ha) (U.α 1 1 / U.α 0 1)
      (by field_simp; ring) (by field_simp; linear_combination (-1 : ℂ) * hJ) h1
  · exact J1_aux hU.normalized (Or.inr hb) (U.β 1 1 / U.β 0 1)
      (by field_simp; linear_combination hJ) (by field_simp; ring) h1

theorem eps_cases (a : ℝ → ℝ) : eps a = 1 ∨ eps a = -1 := by
  unfold eps; split_ifs <;> simp

theorem kernel_gammaU_ne_zero {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms}
    (hU : AdmissibleForms U) : gammaU a U ≠ 0 := by
  have hk := varkappa_ne_zero h
  have hε : (eps a : ℂ) ≠ 0 := by
    rcases eps_cases a with e | e <;> simp [e]
  have w1 : (omega a 1 : ℂ) ≠ 0 := by exact_mod_cast (omega_pos h 1 (Or.inl rfl)).ne'
  have w2 : (omega a (-1) : ℂ) ≠ 0 := by exact_mod_cast (omega_pos h (-1) (Or.inr rfl)).ne'
  have k0 : (varkappa a : ℂ) ≠ 0 := by exact_mod_cast hk
  unfold gammaU
  cases hkd : U.kind
  · have := kernel_J0_ne_zero hU hkd
    simp [k0, this]
  · have := kernel_J1_ne_zero hU hkd
    simp [k0, this, w1, w2]
  · simp [hε]

theorem cU_ne_zero {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms}
    (hU : AdmissibleForms U) : cU a U ≠ 0 := by
  have hε : (eps a : ℂ) ≠ 0 := by
    rcases eps_cases a with e | e <;> simp [e]
  have t : (tau0 a (eps a) : ℂ) ≠ 0 := by
    have := tau0_pos h (eps a) (eps_cases a)
    exact_mod_cast this.ne'
  have d1 : (Damp a 1 1 : ℂ) ≠ 0 := by exact_mod_cast (Damp_pos h 1 (Or.inl rfl)).ne'
  have d2 : (Damp a (-1) 1 : ℂ) ≠ 0 := by exact_mod_cast (Damp_pos h (-1) (Or.inr rfl)).ne'
  have g := kernel_gammaU_ne_zero h hU
  unfold cU
  simp [d1, d2, hε, t, g]

theorem kernel_det_Mmat_k10 {a : ℝ → ℝ} (U : Forms)
    (h0 : U.HasDeriv 0) (h1 : ¬ U.HasDeriv 1) (ρ : ℂ) :
    (Mmat a U ρ).det = JU a U * Fchar a U ρ := by
  classical
  have hk := kind_k10 h0 h1
  rw [Matrix.det_fin_two]
  simp only [Mmat, Matrix.of_apply, h0, h1, ↓reduceIte, Fin.isValue, one_ne_zero]
  unfold JU Fchar calA calB
  simp only [hk]
  have he := eps_sq a
  by_cases hε : 0 < a 0
  · have he1 : eps a = 1 := by simp [eps, hε]
    simp only [chiP, chiP', chiM, chiM', hε, ↓reduceIte, he1]
    push_cast; ring
  · have he1 : eps a = -1 := by simp [eps, hε]
    simp only [chiP, chiP', chiM, chiM', hε, ↓reduceIte, he1]
    push_cast; ring

theorem kernel_det_Mmat_k00 {a : ℝ → ℝ} (U : Forms)
    (h0 : ¬ U.HasDeriv 0) (h1 : ¬ U.HasDeriv 1) (ρ : ℂ) :
    (Mmat a U ρ).det = JU a U * Fchar a U ρ := by
  classical
  have hk := kind_k00 h0 h1
  rw [Matrix.det_fin_two]
  simp only [Mmat, Matrix.of_apply, h0, h1, ↓reduceIte, Fin.isValue, one_ne_zero]
  unfold JU Fchar Forms.J0 Qc
  simp only [hk]
  by_cases hε : 0 < a 0
  · simp only [chiP, chiM, hε, ↓reduceIte]
    push_cast; ring
  · simp only [chiP, chiM, hε, ↓reduceIte]
    push_cast; ring

theorem kernel_det_Mmat_k11 {a : ℝ → ℝ} (U : Forms)
    (h0 : U.HasDeriv 0) (h1 : U.HasDeriv 1) (ρ : ℂ) :
    (Mmat a U ρ).det = JU a U * Fchar a U ρ := by
  classical
  have hk := kind_k11 h0 h1
  rw [Matrix.det_fin_two]
  simp only [Mmat, Matrix.of_apply, h0, h1, ↓reduceIte, Fin.isValue, one_ne_zero]
  unfold JU Fchar Forms.J1 Pc
  simp only [hk]
  by_cases hε : 0 < a 0
  · simp only [chiP', chiM', hε, ↓reduceIte]
    push_cast; ring
  · simp only [chiP', chiM', hε, ↓reduceIte]
    push_cast; ring

theorem kernel_det_Mmat {a : ℝ → ℝ} {U : Forms} (hU : AdmissibleForms U) (ρ : ℂ) :
    (Mmat a U ρ).det = JU a U * Fchar a U ρ := by
  have hord := hU.ordered
  by_cases h0 : U.HasDeriv 0 <;> by_cases h1 : U.HasDeriv 1
  · exact kernel_det_Mmat_k11 U h0 h1 ρ
  · exact kernel_det_Mmat_k10 U h0 h1 ρ
  · exfalso
    simp [Forms.IsOrdered, Forms.ord, h0, h1] at hord
  · exact kernel_det_Mmat_k00 U h0 h1 ρ

/-- Постоянная статьи `J_U = i γ_U / 4`. -/
theorem JU_eq_gammaU (a : ℝ → ℝ) (U : Forms) : JU a U = Complex.I * gammaU a U / 4 := by
  unfold JU gammaU
  cases U.kind
  · linear_combination (2 * (varkappa a : ℂ) * U.J0) * Complex.I_sq
  · linear_combination (-2 * (omega a 1 : ℂ) * (omega a (-1) : ℂ) * (varkappa a : ℂ) * U.J1) *
      Complex.I_sq
  · linear_combination (-(eps a : ℂ)) * Complex.I_sq

/-- `c_U` записи через `J_U`: `cU = D_+(1) D_-(1) · 16 ε τ_ε(0) J_U`. -/
theorem cU_eq_JU (a : ℝ → ℝ) (U : Forms) :
    cU a U = (Damp a 1 1 : ℂ) * (Damp a (-1) 1 : ℂ) * (16 * (eps a : ℂ) * (tau0 a (eps a) : ℂ) *
      JU a U) := by
  rw [JU_eq_gammaU]; unfold cU; ring

/-- `c_U` статьи (`D(1) = 1`) равно `cU / (D_+(1) D_-(1))²`: множитель нормировки. -/
theorem cUpaper_eq {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) (U : Forms) :
    cUpaper a U = cU a U / ((Damp a 1 1 : ℂ) * (Damp a (-1) 1 : ℂ)) ^ 2 := by
  have d1 : (Damp a 1 1 : ℂ) ≠ 0 := by exact_mod_cast (Damp_pos h 1 (Or.inl rfl)).ne'
  have d2 : (Damp a (-1) 1 : ℂ) ≠ 0 := by exact_mod_cast (Damp_pos h (-1) (Or.inr rfl)).ne'
  rw [cU_eq_JU]; unfold cUpaper; field_simp

/-- `J_U ≠ 0`. -/
theorem JU_ne_zero {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms}
    (hU : AdmissibleForms U) : JU a U ≠ 0 := by
  rw [JU_eq_gammaU]
  have := kernel_gammaU_ne_zero h hU
  simp [this, Complex.I_ne_zero]

/-- Лемма `lem:kernel`(c): определитель `𝔐` и `c_U ≠ 0` (само равенство
`det 𝔘⁰ = c_U F` — `lem_kernel_det`). -/
theorem lem_kernel_c {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms}
    (hU : AdmissibleForms U) (ρ : ℂ) :
    (Mmat a U ρ).det = JU a U * Fchar a U ρ ∧ JU a U ≠ 0 ∧
      (Ufrak0 a U ρ).det = cU a U * Fchar a U ρ ∧ cU a U ≠ 0 :=
  ⟨kernel_det_Mmat hU ρ, JU_ne_zero h hU, lem_kernel_det h hU ρ, cU_ne_zero h hU⟩

/-- `c_U` статьи отлично от нуля. -/
theorem cUpaper_ne_zero {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms}
    (hU : AdmissibleForms U) : cUpaper a U ≠ 0 := by
  have d1 : (Damp a 1 1 : ℂ) ≠ 0 := by exact_mod_cast (Damp_pos h 1 (Or.inl rfl)).ne'
  have d2 : (Damp a (-1) 1 : ℂ) ≠ 0 := by exact_mod_cast (Damp_pos h (-1) (Or.inr rfl)).ne'
  rw [cUpaper_eq h]
  exact div_ne_zero (cU_ne_zero h hU) (pow_ne_zero 2 (mul_ne_zero d1 d2))

/-- Амплитуда статьи (`D(1) = 1`) есть `Damp a s x / Damp a s 1`; в точке `1` она равна `1`. -/
theorem Damp_paper_one {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    Damp a s 1 / Damp a s 1 = 1 :=
  div_self (Damp_pos h s hs).ne'

/-- В нуле амплитуда статьи равна `1 / Damp a s 1` (`D_±(0)` статьи). -/
theorem Damp_paper_zero {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    Damp a s 0 / Damp a s 1 = 1 / Damp a s 1 := by
  rw [Damp_zero h s hs]

/-- `c_U` статьи через амплитуды статьи в нуле: `16 ε τ_ε(0) D₊(0) D₋(0) J_U`. -/
theorem cUpaper_eq_amp {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) (U : Forms) :
    cUpaper a U = 16 * (eps a : ℂ) * (tau0 a (eps a) : ℂ) *
      (((Damp a 1 0 / Damp a 1 1 : ℝ) : ℂ) * ((Damp a (-1) 0 / Damp a (-1) 1 : ℝ) : ℂ)) *
      JU a U := by
  rw [Damp_zero h 1 (Or.inl rfl), Damp_zero h (-1) (Or.inr rfl)]
  unfold cUpaper
  push_cast
  ring

end GeneralBC
end Involution
