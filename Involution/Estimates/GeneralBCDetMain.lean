module

public import Involution.Estimates.GeneralBCDetEst
public import Involution.Estimates.GeneralBCRegularityEntire

/-! # Лемма `lem:det`: связь `Δ` и `F` (пакет G4, C24 шаги 7, 9)

`ρ^{1-κ₁-κ₂} Δ(ρ²) = c_∗ (F(ρ) + η(ρ))`, `η` голоморфна при `ρ ≠ 0`,
`sup_{|ρ|≥r} |η| e^{-L|Im ρ|} → 0`. Вывод леммы `lem:fsr` входит гипотезой `hfsr`. -/

@[expose] public noncomputable section

open MeasureTheory Set Matrix Complex

namespace Involution
namespace GeneralBC

/-- Алгебраическая оценка: `Pq (d₁ cU) = cU F + η₁`, `‖d₁ − 1‖ ≤ t ≤ 1/2` дают
`‖Pq − F‖ ≤ 2t‖F‖ + 2E₁/‖cU‖`. -/
theorem alg_bound {cU d1 η1 F Pq : ℂ} {t E1 : ℝ} (hcU : cU ≠ 0) (ht : t ≤ 1 / 2)
    (hd : ‖d1 - 1‖ ≤ t) (hη : ‖η1‖ ≤ E1) (heq : Pq * (d1 * cU) = cU * F + η1) :
    ‖Pq - F‖ ≤ 2 * t * ‖F‖ + 2 * E1 / ‖cU‖ := by
  have hcn : 0 < ‖cU‖ := norm_pos_iff.2 hcU
  have hd1 : 1 / 2 ≤ ‖d1‖ := by
    have := norm_sub_norm_le (1 : ℂ) d1
    rw [norm_sub_rev] at this
    simp at this
    linarith
  have key : (Pq - F) * (d1 * cU) = η1 + cU * F * (1 - d1) := by linear_combination heq
  have hk : ‖Pq - F‖ * (‖d1‖ * ‖cU‖) ≤ E1 + ‖cU‖ * ‖F‖ * t := by
    have h1 : ‖(Pq - F) * (d1 * cU)‖ ≤ E1 + ‖cU‖ * ‖F‖ * t := by
      rw [key]
      refine (norm_add_le _ _).trans (add_le_add hη ?_)
      rw [norm_mul, norm_mul, norm_sub_rev]
      exact mul_le_mul_of_nonneg_left hd (by positivity)
    rwa [norm_mul, norm_mul] at h1
  have h2 : ‖Pq - F‖ * ((1 / 2) * ‖cU‖) ≤ E1 + ‖cU‖ * ‖F‖ * t := by
    refine le_trans ?_ hk
    rw [← mul_assoc, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd1 (norm_nonneg _)) hcn.le
  have : 2 * t * ‖F‖ + 2 * E1 / ‖cU‖ = (2 * t * ‖F‖ * ‖cU‖ + 2 * E1) / ‖cU‖ := by
    field_simp
  rw [this, le_div_iff₀ hcn]
  nlinarith

/-- Сумма модулей коэффициентов `F`. -/
def CF (a : ℝ → ℝ) (U : Forms) : ℝ :=
  ‖thetaPlus a U‖ + ‖thetaMinus a U‖ + ‖thetaDPlus a U‖ + ‖thetaDMinus a U‖

/-- Постоянная оценки `‖ρ^{1-κ}Δ(ρ²)/c_∗ − F‖ ≤ K ε e^{L|Im ρ|}`. -/
def Kc (a : ℝ → ℝ) (U : Forms) : ℝ :=
  1536 * CF a U + 192 * (Bd a U + 1) ^ 3 * Cc a U / ‖cU a U‖

theorem norm_Fchar_le {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) (U : Forms) (ρ : ℂ) :
    ‖Fchar a U ρ‖ ≤ CF a U * Real.exp (Ltot a * |ρ.im|) := by
  have := Involution.norm_expPoly_le (θp := theta a U) (θm := thetaMinus a U)
    (θdp := thetaDPlus a U) (θdm := thetaDMinus a U) (L := Ltot a) (d := dlt a)
    (abs_dlt_lt_Ltot h).le ρ
  rw [Fchar_eq_expPoly a U]
  exact this

theorem det_one_sub_le (R : Matrix (Fin 4) (Fin 4) ℂ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hR : ∀ i j, ‖R i j‖ ≤ ε) : ‖(1 + R).det - 1‖ ≤ 768 * ε := by
  have := det_sub_le (M := 1 + R) (N := 1) (Bd := 1) zero_le_one hε0 hε1
    (fun i j => by by_cases hij : i = j <;> simp [Matrix.one_apply, hij])
    (fun i j => by simpa using hR i j)
  simp only [Matrix.det_one] at this
  norm_num at this
  linarith

theorem det_Wmat_zero {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) :
    (Wmat a 0).det = 16 * (tau0 a 1 : ℂ) * (tau0 a (-1) : ℂ) := by
  rw [det_Wmat, kfun_zero h]
  have : (eps a : ℂ) ^ 2 = 1 := by
    have := eps_sq a
    exact_mod_cast (by nlinarith : eps a ^ 2 = 1)
  rw [this]
  simp [tau0]

/-- Оценка для одного `ρ`: при малом остатке `R` и большом `|ρ|`
`‖ρ^{1-κ}Δ(ρ²)/c_∗ − F‖ ≤ K ε e^{L|Im ρ|}`. -/
theorem core_bound {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms} (hU : AdmissibleForms U)
    {ρ : ℂ} (hρ0 : ρ ≠ 0) (R : ℝ → ℂ → Matrix (Fin 4) (Fin 4) ℂ)
    (hsol : IsSol a ρ (fun x => Wmat a x * Dmat a x * (1 + R x ρ) * Emat a x ρ))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hCε : Cc a U * ε ≤ 1) (h768 : 768 * ε ≤ 1 / 2)
    (hρ : ‖ρ⁻¹‖ ≤ ε) (hR0 : ∀ i j, ‖R 0 ρ i j‖ ≤ ε) (hR1 : ∀ i j, ‖R 1 ρ i j‖ ≤ ε) :
    ‖ρ ^ (1 - (kappaSum U : ℤ)) * Delta a U (ρ ^ 2) / cStar a U - Fchar a U ρ‖ ≤
      Kc a U * ε * Real.exp (Ltot a * |ρ.im|) := by
  have hcU := cU_ne_zero h hU
  have hdet := det_UA h U hρ0 hsol
  have hY0 : Wmat a 0 * Dmat a 0 * (1 + R 0 ρ) * Emat a 0 ρ = Wmat a 0 * (1 + R 0 ρ) := by
    simp only [Emat_zero, Dmat_zero h, Matrix.mul_one]
  rw [hY0, Matrix.det_mul, det_Wmat_zero h] at hdet
  have hT0 : (16 * (tau0 a 1 : ℂ) * (tau0 a (-1) : ℂ)) ≠ 0 := by
    have h1 : (tau0 a 1 : ℂ) ≠ 0 := by exact_mod_cast (tau0_pos h 1 (Or.inl rfl)).ne'
    have h2 : (tau0 a (-1) : ℂ) ≠ 0 := by exact_mod_cast (tau0_pos h (-1) (Or.inr rfl)).ne'
    simp [h1, h2]
  have hK := lem_kernel_det h hU ρ
  have hE := det_UA_sub_le h U ρ R hε0 hε1 hCε hρ hR0 hR1
  have hd1 := det_one_sub_le (R 0 ρ) hε0 hε1 hR0
  have hclose := alg_bound (cU := cU a U) (d1 := (1 + R 0 ρ).det)
    (η1 := (UA U ρ (fun x => Wmat a x * Dmat a x * (1 + R x ρ) * Emat a x ρ)).det -
      (Ufrak0 a U ρ).det)
    (F := Fchar a U ρ)
    (Pq := ρ ^ (1 - (kappaSum U : ℤ)) * Delta a U (ρ ^ 2) / cStar a U)
    hcU h768 hd1 hE (by
      rw [cStar_eq_cU h, hdet, hK]
      field_simp
      ring)
  refine hclose.trans ?_
  have hF := norm_Fchar_le h U ρ
  have hcn : 0 < ‖cU a U‖ := norm_pos_iff.2 hcU
  unfold Kc
  have e1 : 2 * (768 * ε) * ‖Fchar a U ρ‖ ≤ 2 * (768 * ε) * (CF a U * Real.exp (Ltot a * |ρ.im|)) :=
    mul_le_mul_of_nonneg_left hF (by positivity)
  have e2 : 2 * (96 * (Bd a U + 1) ^ 3 * (Cc a U * ε) * Real.exp (Ltot a * |ρ.im|)) / ‖cU a U‖ =
      192 * (Bd a U + 1) ^ 3 * Cc a U / ‖cU a U‖ * ε * Real.exp (Ltot a * |ρ.im|) := by
    field_simp
    ring
  rw [e2] at hclose
  nlinarith

theorem CF_nonneg (a : ℝ → ℝ) (U : Forms) : 0 ≤ CF a U := by
  unfold CF; positivity

theorem Kc_nonneg (a : ℝ → ℝ) (U : Forms) : 0 ≤ Kc a U := by
  unfold Kc
  have := Bd_nonneg a U
  have := Cc_nonneg a U
  have := CF_nonneg a U
  positivity

/-- Малый параметр `ε` для заданного `η`. -/
theorem exists_eps (a : ℝ → ℝ) (U : Forms) {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ Cc a U * ε ≤ 1 ∧ 768 * ε ≤ 1 / 2 ∧ Kc a U * ε ≤ η := by
  have hC := Cc_nonneg a U
  have hK := Kc_nonneg a U
  refine ⟨min (1 / 1536) (min (1 / (Cc a U + 1)) (η / (Kc a U + 1))), ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · exact (min_le_left _ _).trans (by norm_num)
  · have h1 : min (1 / 1536) (min (1 / (Cc a U + 1)) (η / (Kc a U + 1))) ≤ 1 / (Cc a U + 1) :=
      (min_le_right _ _).trans (min_le_left _ _)
    calc _ ≤ Cc a U * (1 / (Cc a U + 1)) := mul_le_mul_of_nonneg_left h1 hC
      _ ≤ 1 := by rw [mul_one_div, div_le_one (by linarith)]; linarith
  · have := min_le_left (1 / 1536 : ℝ) (min (1 / (Cc a U + 1)) (η / (Kc a U + 1)))
    linarith
  · have h1 : min (1 / 1536) (min (1 / (Cc a U + 1)) (η / (Kc a U + 1))) ≤ η / (Kc a U + 1) :=
      (min_le_right _ _).trans (min_le_right _ _)
    calc _ ≤ Kc a U * (η / (Kc a U + 1)) := mul_le_mul_of_nonneg_left h1 hK
      _ ≤ η := by
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]
        nlinarith

/-- Для одного знака `s`: из решения вида `W D (1+R) E` с равномерно малым `R` следует оценка
`‖ρ^{1-κ}Δ(ρ²)/c_∗ − F‖ ≤ η e^{L|Im ρ|}` при больших `|ρ|` в полуплоскости `s Im ρ ≥ 0`. -/
theorem eta_small_s {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms} (hU : AdmissibleForms U)
    {s : ℝ} (R : ℝ → ℂ → Matrix (Fin 4) (Fin 4) ℂ)
    (hRs : UniformlySmall R {ρ | -0 ≤ s * ρ.im}) (r₀ : ℝ)
    (hsol : ∀ ρ : ℂ, -0 ≤ s * ρ.im → r₀ ≤ ‖ρ‖ →
      IsSol a ρ (fun x => Wmat a x * Dmat a x * (1 + R x ρ) * Emat a x ρ))
    {η : ℝ} (hη : 0 < η) :
    ∃ r : ℝ, 1 ≤ r ∧ ∀ ρ : ℂ, -0 ≤ s * ρ.im → r ≤ ‖ρ‖ →
      ‖ρ ^ (1 - (kappaSum U : ℤ)) * Delta a U (ρ ^ 2) / cStar a U - Fchar a U ρ‖ ≤
        η * Real.exp (Ltot a * |ρ.im|) := by
  obtain ⟨ε, hε0, hε1, hCε, h768, hKε⟩ := exists_eps a U hη
  obtain ⟨r1, hr1⟩ := hRs ε hε0
  refine ⟨max (max r₀ r1) (max 1 (1 / ε)), le_trans (le_max_left _ _) (le_max_right _ _), ?_⟩
  intro ρ hρs hρr
  have hr0 : r₀ ≤ ‖ρ‖ := (le_max_left _ _).trans ((le_max_left _ _).trans hρr)
  have hr1' : r1 ≤ ‖ρ‖ := (le_max_right _ _).trans ((le_max_left _ _).trans hρr)
  have hone : 1 / ε ≤ ‖ρ‖ := (le_max_right _ _).trans ((le_max_right _ _).trans hρr)
  have hpos : 0 < ‖ρ‖ := lt_of_lt_of_le (by positivity) hone
  have hρ0 : ρ ≠ 0 := norm_pos_iff.1 hpos
  have hinv : ‖ρ⁻¹‖ ≤ ε := by
    rw [norm_inv, inv_le_comm₀ hpos hε0, ← one_div]
    exact hone
  have hb := core_bound h hU hρ0 R (hsol ρ hρs hr0) hε0.le hε1 hCε h768 hinv
    (fun i j => hr1 ρ hρs hr1' 0 ⟨le_rfl, zero_le_one⟩ i j)
    (fun i j => hr1 ρ hρs hr1' 1 ⟨zero_le_one, le_rfl⟩ i j)
  refine hb.trans ?_
  exact mul_le_mul_of_nonneg_right hKε (Real.exp_pos _).le

theorem cStar_ne_zero {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms}
    (hU : AdmissibleForms U) : cStar a U ≠ 0 := by
  have h1 : (tau0 a 1 : ℂ) ≠ 0 := by exact_mod_cast (tau0_pos h 1 (Or.inl rfl)).ne'
  have h2 : (tau0 a (-1) : ℂ) ≠ 0 := by exact_mod_cast (tau0_pos h (-1) (Or.inr rfl)).ne'
  rw [cStar_eq_cU h]
  exact div_ne_zero (cU_ne_zero h hU) (by simp [h1, h2])

/-- **Лемма `lem:det`** (C24 шаги 7, 9; `paper/exposition-G.tex`, `lem:det`):
`ρ^{1-κ₁-κ₂} Δ(ρ²) = c_∗ (F(ρ) + η(ρ))`, `η` голоморфна при `ρ ≠ 0` и
`‖η(ρ)‖ e^{-L|Im ρ|} → 0`. Вывод леммы `lem:fsr` (`h = 0`) — гипотеза `hfsr`. -/
theorem lem_det {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {U : Forms} (hU : AdmissibleForms U)
    (hfsr : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      ∃ R : ℝ → ℂ → Matrix (Fin 4) (Fin 4) ℂ,
        UniformlySmall R {ρ | -0 ≤ s * ρ.im} ∧
        ∃ r₀ : ℝ, ∀ ρ : ℂ, -0 ≤ s * ρ.im → r₀ ≤ ‖ρ‖ →
          IsSol a ρ (fun x => Wmat a x * Dmat a x * (1 + R x ρ) * Emat a x ρ)) :
    ∃ η : ℂ → ℂ, DifferentiableOn ℂ η {0}ᶜ ∧
      (∀ ρ : ℂ, ρ ≠ 0 →
        ρ ^ (1 - (kappaSum U : ℤ)) * Delta a U (ρ ^ 2) = cStar a U * (Fchar a U ρ + η ρ)) ∧
      ∀ ε > 0, ∃ r : ℝ, ∀ ρ : ℂ, r ≤ ‖ρ‖ → ‖η ρ‖ * Real.exp (-(Ltot a) * |ρ.im|) ≤ ε := by
  have hc := cStar_ne_zero h hU
  refine ⟨fun ρ => ρ ^ (1 - (kappaSum U : ℤ)) * Delta a U (ρ ^ 2) / cStar a U - Fchar a U ρ,
    ?_, ?_, ?_⟩
  · intro ρ hρ
    refine DifferentiableAt.differentiableWithinAt ?_
    have h1 : DifferentiableAt ℂ (fun ρ : ℂ => ρ ^ (1 - (kappaSum U : ℤ))) ρ :=
      differentiableAt_zpow.2 (Or.inl hρ)
    have h2 : DifferentiableAt ℂ (fun ρ : ℂ => Delta a U (ρ ^ 2)) ρ :=
      ((Delta_differentiable a U).comp (differentiable_pow 2)).differentiableAt
    exact ((h1.mul h2).div_const _).sub ((Fchar_differentiable a U).differentiableAt)
  · intro ρ _
    field_simp
    ring
  · intro ε hε
    obtain ⟨Rp, hRp, r₀p, hsp⟩ := hfsr 1 (Or.inl rfl)
    obtain ⟨Rm, hRm, r₀m, hsm⟩ := hfsr (-1) (Or.inr rfl)
    obtain ⟨rp, hrp1, hp⟩ := eta_small_s h hU Rp hRp r₀p hsp hε
    obtain ⟨rm, hrm1, hm⟩ := eta_small_s h hU Rm hRm r₀m hsm hε
    refine ⟨max rp rm, fun ρ hρ => ?_⟩
    have hb : ‖ρ ^ (1 - (kappaSum U : ℤ)) * Delta a U (ρ ^ 2) / cStar a U - Fchar a U ρ‖ ≤
        ε * Real.exp (Ltot a * |ρ.im|) := by
      rcases le_total 0 ρ.im with hi | hi
      · exact hp ρ (by simpa using hi) ((le_max_left _ _).trans hρ)
      · exact hm ρ (by simpa using hi) ((le_max_right _ _).trans hρ)
    have he : 0 < Real.exp (Ltot a * |ρ.im|) := Real.exp_pos _
    have : Real.exp (-(Ltot a) * |ρ.im|) * Real.exp (Ltot a * |ρ.im|) = 1 := by
      rw [← Real.exp_add]; simp
    calc _ ≤ ε * Real.exp (Ltot a * |ρ.im|) * Real.exp (-(Ltot a) * |ρ.im|) :=
          mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
      _ = ε := by rw [mul_assoc, mul_comm (Real.exp (Ltot a * |ρ.im|)), this, mul_one]

end GeneralBC
end Involution

end
