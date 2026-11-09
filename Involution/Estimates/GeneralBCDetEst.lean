module

public import Involution.Estimates.GeneralBCDetCauchy
public import Involution.Estimates.GeneralBCDetPerturb
public import Involution.Estimates.GeneralBCRegularityBridge
public import Involution.Folding.GeneralBCExternal
public import Involution.Folding.GeneralBCAdmissible
public import Involution.Estimates.ExpPoly
public import Involution.Folding.GeneralBCKernelDet
public import Involution.Folding.GeneralBCKernelMain

/-! # Оценка возмущения 𝔘_a − 𝔘⁰ (пакет G4, формула (eq:eta1))

Матрицы `𝔘_a(ρ)` (`UA`) и `𝔘⁰(ρ)` (`Ufrak0`) записываются как `NmatW A B e` с постоянными
`A⁰ = V₀ W(0) D(0)`, `B⁰ = V1a W(1) D(1)` и весами `e_c = e^{isρℓ_±}`; возмущение `A − A⁰`,
`B − B⁰` оценивается через `R` и `ρ⁻¹`. -/

@[expose] public noncomputable section

open MeasureTheory Set Matrix Complex

namespace Involution
namespace GeneralBC

/-- Веса `e_c(ρ) = e^{i s_c ρ ℓ_{χ_c}}` (диагональ `E(1,ρ)`). -/
def eW (a : ℝ → ℝ) (ρ : ℂ) (c : Fin 4) : ℂ :=
  Complex.exp (Complex.I * ρ * ((sgn c * ell a (chan c) : ℝ) : ℂ))

theorem Emat_one (a : ℝ → ℝ) (ρ : ℂ) : Emat a 1 ρ = Matrix.diagonal (eW a ρ) := by
  unfold Emat eW
  congr 1
  funext c
  congr 1
  simp only [ell]
  push_cast
  ring

theorem Emat_zero (a : ℝ → ℝ) (ρ : ℂ) : Emat a 0 ρ = 1 := by
  rw [← Matrix.diagonal_one]
  unfold Emat
  congr 1
  funext c
  simp [tPhase_zero]

theorem Dmat_zero {m κ : ℝ} {a : ℝ → ℝ} (h : HypH a m κ) : Dmat a 0 = 1 := by
  rw [← Matrix.diagonal_one]
  unfold Dmat
  congr 1
  funext c
  have : chan c = 1 ∨ chan c = -1 := by
    unfold chan; split_ifs <;> simp
  simp [Damp_zero h _ this]

theorem norm_eW (a : ℝ → ℝ) (ρ : ℂ) (c : Fin 4) :
    ‖eW a ρ c‖ = Real.exp (-((sgn c * ell a (chan c)) * ρ.im)) :=
  Involution.norm_cexp_I_mul ρ _

/-- Произведение двух весов из разных столбцов не превосходит `e^{L|Im ρ|}`. -/
theorem eW_prod_le {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) {c c' : Fin 4} (hne : c ≠ c')
    (ρ : ℂ) : ‖eW a ρ c * eW a ρ c'‖ ≤ Real.exp (Ltot a * |ρ.im|) := by
  rw [norm_mul, norm_eW, norm_eW, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 := ell_pos h (Or.inl rfl)
  have h2 := ell_pos h (Or.inr rfl)
  unfold Ltot
  rcases le_total 0 ρ.im with ht | ht
  · rw [abs_of_nonneg ht]
    fin_cases c <;> fin_cases c' <;> first | exact absurd rfl hne | (simp [chan, sgn]; nlinarith)
  · rw [abs_of_nonpos ht]
    fin_cases c <;> fin_cases c' <;> first | exact absurd rfl hne | (simp [chan, sgn]; nlinarith)

theorem foldV0_row (i c : Fin 4) (hi : 2 ≤ (i : ℕ)) : foldV0 i c = 0 := by
  fin_cases i <;> first | (exfalso; simp at hi; done) | (fin_cases c <;> rfl)

theorem V1a_row (U : Forms) (i c : Fin 4) (hi : (i : ℕ) < 2) : V1a U i c = 0 := by
  fin_cases i <;> first | (exfalso; simp at hi; done) | (fin_cases c <;> rfl)

theorem V1b_row (U : Forms) (i c : Fin 4) (hi : (i : ℕ) < 2) : V1b U i c = 0 := by
  fin_cases i <;> first | (exfalso; simp at hi; done) | (fin_cases c <;> rfl)

theorem NmatW_split (V0 V M0 M1 : Matrix (Fin 4) (Fin 4) ℂ) (e : Fin 4 → ℂ)
    (hV0 : ∀ (i c : Fin 4), 2 ≤ (i : ℕ) → V0 i c = 0)
    (hV : ∀ (i c : Fin 4), (i : ℕ) < 2 → V i c = 0) :
    V0 * M0 + V * (M1 * Matrix.diagonal e) = NmatW (V0 * M0) (V * M1) e := by
  ext i c
  have e2 : (V * (M1 * Matrix.diagonal e)) i c = (V * M1) i c * e c := by
    rw [← Matrix.mul_assoc, Matrix.mul_diagonal]
  rw [Matrix.add_apply, e2]
  by_cases hi : (i : ℕ) < 2
  · have : (V * M1) i c = 0 := by
      simp only [Matrix.mul_apply]
      exact Finset.sum_eq_zero fun j _ => by rw [hV i j hi, zero_mul]
    unfold NmatW
    simp only [Matrix.of_apply, hi, ↓reduceIte, this, zero_mul, add_zero]
  · have : (V0 * M0) i c = 0 := by
      simp only [Matrix.mul_apply]
      exact Finset.sum_eq_zero fun j _ => by rw [hV0 i j (not_lt.1 hi), zero_mul]
    unfold NmatW
    simp only [Matrix.of_apply, hi, ↓reduceIte, this, zero_add]

theorem UA_eq_N {a : ℝ → ℝ} (U : Forms) (ρ : ℂ) (M : ℝ → Matrix (Fin 4) (Fin 4) ℂ) :
    UA U ρ (fun x => M x * Emat a x ρ) =
      NmatW (foldV0 * M 0) ((V1a U + ρ⁻¹ • V1b U) * M 1) (eW a ρ) := by
  unfold UA
  simp only [Emat_zero, Emat_one, Matrix.mul_one]
  exact NmatW_split _ _ _ _ _ (fun i c hi => foldV0_row i c hi) (fun i c hi => by
    simp [V1a_row U i c hi, V1b_row U i c hi])

theorem colv_eq (a : ℝ → ℝ) (c : Fin 4) (ρ : ℂ) (x : ℝ) (i : Fin 4) :
    colv a c ρ x i = (Wmat a x * Dmat a x * Emat a x ρ) i c := by
  simp only [colv, Wmat, Dmat, Emat, Matrix.mul_diagonal, Matrix.of_apply]
  ring

theorem Ufrak0_eq_N {a : ℝ → ℝ} (U : Forms) (ρ : ℂ) :
    Ufrak0 a U ρ = NmatW (foldV0 * (Wmat a 0 * Dmat a 0)) (V1a U * (Wmat a 1 * Dmat a 1))
      (eW a ρ) := by
  have key : Ufrak0 a U ρ = foldV0 * (Wmat a 0 * Dmat a 0 * Emat a 0 ρ) +
      V1a U * (Wmat a 1 * Dmat a 1 * Emat a 1 ρ) := by
    simp only [Ufrak0, colv_eq]
    generalize Wmat a 0 * Dmat a 0 * Emat a 0 ρ = Z0
    generalize Wmat a 1 * Dmat a 1 * Emat a 1 ρ = Z1
    ext i c
    fin_cases i <;>
      simp [foldV0, V1a, Matrix.vecMul, dotProduct, Fin.sum_univ_four, U0row, sub_eq_add_neg]
  rw [key, Emat_zero, Emat_one, Matrix.mul_one]
  exact NmatW_split (foldV0) (V1a U) (Wmat a 0 * Dmat a 0) (Wmat a 1 * Dmat a 1) (eW a ρ)
    (fun i c hi => foldV0_row i c hi) (fun i c hi => V1a_row U i c hi)

/-! ## Оценка возмущения -/

/-- Сумма модулей элементов матрицы. -/
def nsum (Q : Matrix (Fin 4) (Fin 4) ℂ) : ℝ := ∑ i, ∑ k, ‖Q i k‖

theorem nsum_nonneg (Q : Matrix (Fin 4) (Fin 4) ℂ) : 0 ≤ nsum Q :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_le_nsum (Q : Matrix (Fin 4) (Fin 4) ℂ) (i k : Fin 4) : ‖Q i k‖ ≤ nsum Q := by
  unfold nsum
  calc ‖Q i k‖ ≤ ∑ k', ‖Q i k'‖ :=
        Finset.single_le_sum (f := fun k' => ‖Q i k'‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ k)
    _ ≤ ∑ i', ∑ k', ‖Q i' k'‖ :=
        Finset.single_le_sum (f := fun i' => ∑ k', ‖Q i' k'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

theorem norm_mul_le_nsum (Q R : Matrix (Fin 4) (Fin 4) ℂ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : ∀ k j, ‖R k j‖ ≤ r) (i j : Fin 4) : ‖(Q * R) i j‖ ≤ nsum Q * r := by
  rw [Matrix.mul_apply]
  calc _ ≤ ∑ k, ‖Q i k * R k j‖ := norm_sum_le _ _
    _ ≤ ∑ k, ‖Q i k‖ * r := Finset.sum_le_sum fun k _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hr k j) (norm_nonneg _)
    _ = (∑ k, ‖Q i k‖) * r := (Finset.sum_mul _ _ _).symm
    _ ≤ nsum Q * r := by
        refine mul_le_mul_of_nonneg_right ?_ hr0
        unfold nsum
        exact Finset.single_le_sum (f := fun i' => ∑ k', ‖Q i' k'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

/-- Постоянные матрицы возмущения. -/
def Q0 (a : ℝ → ℝ) : Matrix (Fin 4) (Fin 4) ℂ := foldV0 * (Wmat a 0 * Dmat a 0)
def Q1 (a : ℝ → ℝ) (U : Forms) : Matrix (Fin 4) (Fin 4) ℂ := V1a U * (Wmat a 1 * Dmat a 1)
def Q2 (a : ℝ → ℝ) (U : Forms) : Matrix (Fin 4) (Fin 4) ℂ := V1b U * (Wmat a 1 * Dmat a 1)

/-- Постоянные оценки: `Bd` — граница элементов `A⁰`, `B⁰`; `Cc` — коэффициент возмущения. -/
def Bd (a : ℝ → ℝ) (U : Forms) : ℝ := nsum (Q0 a) + nsum (Q1 a U)
def Cc (a : ℝ → ℝ) (U : Forms) : ℝ := nsum (Q0 a) + nsum (Q1 a U) + 2 * nsum (Q2 a U)

theorem Cc_nonneg (a : ℝ → ℝ) (U : Forms) : 0 ≤ Cc a U := by
  unfold Cc
  have := nsum_nonneg (Q0 a)
  have := nsum_nonneg (Q1 a U)
  have := nsum_nonneg (Q2 a U)
  linarith

theorem Bd_nonneg (a : ℝ → ℝ) (U : Forms) : 0 ≤ Bd a U := by
  unfold Bd
  have := nsum_nonneg (Q0 a)
  have := nsum_nonneg (Q1 a U)
  linarith

theorem det_UA_sub_le {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) (U : Forms) (ρ : ℂ)
    (R : ℝ → ℂ → Matrix (Fin 4) (Fin 4) ℂ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hCε : Cc a U * ε ≤ 1) (hρ : ‖ρ⁻¹‖ ≤ ε)
    (hR0 : ∀ i j, ‖R 0 ρ i j‖ ≤ ε) (hR1 : ∀ i j, ‖R 1 ρ i j‖ ≤ ε) :
    ‖(UA U ρ (fun x => Wmat a x * Dmat a x * (1 + R x ρ) * Emat a x ρ)).det -
        (Ufrak0 a U ρ).det‖ ≤
      96 * (Bd a U + 1) ^ 3 * (Cc a U * ε) * Real.exp (Ltot a * |ρ.im|) := by
  rw [UA_eq_N U ρ (fun x => Wmat a x * Dmat a x * (1 + R x ρ)), Ufrak0_eq_N U ρ]
  have hC := Cc_nonneg a U
  have hAdiff : foldV0 * (Wmat a 0 * Dmat a 0 * (1 + R 0 ρ)) - foldV0 * (Wmat a 0 * Dmat a 0)
      = Q0 a * R 0 ρ := by
    simp only [Q0, Matrix.mul_add, Matrix.mul_one, Matrix.mul_assoc, add_sub_cancel_left]
  have hBdiff : (V1a U + ρ⁻¹ • V1b U) * (Wmat a 1 * Dmat a 1 * (1 + R 1 ρ)) -
      V1a U * (Wmat a 1 * Dmat a 1) = Q1 a U * R 1 ρ + ρ⁻¹ • (Q2 a U + Q2 a U * R 1 ρ) := by
    simp only [Q1, Q2, Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_assoc, smul_add]
    abel
  refine det_NmatW_sub_le (Bd := Bd a U) (δ := Cc a U * ε) (Bd_nonneg a U) (mul_nonneg hC hε0)
    hCε (fun c c' hne => eW_prod_le h hne ρ) (fun i c => ?_) (fun i c => ?_) (fun i c => ?_)
    (fun i c => ?_)
  · exact (norm_le_nsum (Q0 a) i c).trans (by unfold Bd; linarith [nsum_nonneg (Q1 a U)])
  · exact (norm_le_nsum (Q1 a U) i c).trans (by unfold Bd; linarith [nsum_nonneg (Q0 a)])
  · rw [← Matrix.sub_apply, hAdiff]
    refine (norm_mul_le_nsum _ _ hε0 hR0 i c).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hε0
    unfold Cc; linarith [nsum_nonneg (Q1 a U), nsum_nonneg (Q2 a U)]
  · rw [← Matrix.sub_apply, hBdiff]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    have h1 := norm_mul_le_nsum (Q1 a U) (R 1 ρ) hε0 hR1 i c
    have h2 := norm_mul_le_nsum (Q2 a U) (R 1 ρ) hε0 hR1 i c
    have h3 := norm_le_nsum (Q2 a U) i c
    have h4 : ‖ρ⁻¹ * (Q2 a U i c + (Q2 a U * R 1 ρ) i c)‖ ≤ ε * (2 * nsum (Q2 a U)) := by
      rw [norm_mul]
      refine mul_le_mul hρ ((norm_add_le _ _).trans ?_) (norm_nonneg _) hε0
      have := nsum_nonneg (Q2 a U)
      nlinarith
    refine (norm_add_le _ _).trans ?_
    have : nsum (Q0 a) * ε ≥ 0 := mul_nonneg (nsum_nonneg _) hε0
    unfold Cc
    nlinarith

end GeneralBC
end Involution

end
