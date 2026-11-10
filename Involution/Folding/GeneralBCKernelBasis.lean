module

public import Involution.Folding.GeneralBCKernelDet

/-! # Лемма `lem:kernel`(b): ядро первых двух строк `𝔘⁰(ρ)`

Нормировка `D(0) = 1` записи: `𝔘⁰ c(ξ,ζ) = (0, 0, 𝔐 (D_+(1)ξ, D_-(1)ζ))`, где `𝔐` — матрица
статьи (`D(1) = 1`). -/

@[expose] public noncomputable section

open Matrix

namespace Involution
namespace GeneralBC

/-- `lem:kernel`(b): `𝔘⁰(ρ) c(ξ,ζ) = (0, 0, 𝔐(ρ)(D_+(1)ξ, D_-(1)ζ))`. В статье `D(1) = 1`. -/
theorem kernel_b_apply {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) (U : Forms) (ρ ξ ζ : ℂ) :
    Ufrak0 a U ρ *ᵥ cvec a ξ ζ =
      ![0, 0, (Mmat a U ρ *ᵥ ![(Damp a 1 1 : ℂ) * ξ, (Damp a (-1) 1 : ℂ) * ζ]) 0,
        (Mmat a U ρ *ᵥ ![(Damp a 1 1 : ℂ) * ξ, (Damp a (-1) 1 : ℂ) * ζ]) 1] := by
  classical
  obtain ⟨c0, c1, c2, c3⟩ := chan_vals
  obtain ⟨s0, s1, s2, s3⟩ := sgn_vals
  have e : ∀ (r t : ℂ), Complex.I * r * t = r * t * Complex.I := fun _ _ => by ring
  ext i
  fin_cases i
  · by_cases hε : 0 < a 0
    · have he : eps a = 1 := by simp [eps, hε]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Ufrak0_row0 h, cvec, hε, he, c0, c1, c2,
        c3]
    · have he : eps a = -1 := by simp [eps, hε]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Ufrak0_row0 h, cvec, hε, he, c0, c1, c2,
        c3]
  · by_cases hε : 0 < a 0
    · have he : eps a = 1 := by simp [eps, hε]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Ufrak0_row1 h, cvec, hε, he, c0, c1, c2,
        c3, s0, s1, s2, s3]
    · have he : eps a = -1 := by simp [eps, hε]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Ufrak0_row1 h, cvec, hε, he, c0, c1, c2,
        c3, s0, s1, s2, s3]
  · by_cases hε : 0 < a 0 <;> by_cases hd : U.HasDeriv 0 <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Ufrak0_row2, cvec, Mmat, hε, hd, c0, c1, c2,
      c3, s0, s1, s2, s3, chiP, chiP', chiM, chiM', cos_exp, sin_exp, omega] <;>
    simp only [e] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf
  · by_cases hε : 0 < a 0 <;> by_cases hd : U.HasDeriv 1 <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Ufrak0_row3, cvec, Mmat, hε, hd, c0, c1, c2,
      c3, s0, s1, s2, s3, chiP, chiP', chiM, chiM', cos_exp, sin_exp, omega] <;>
    simp only [e] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf

/-- Отображение `(ξ,ζ) ↦ c(ξ,ζ)` инъективно. -/
theorem cvec_injective (a : ℝ → ℝ) {ξ ζ ξ' ζ' : ℂ} (h : cvec a ξ ζ = cvec a ξ' ζ') :
    ξ = ξ' ∧ ζ = ζ' := by
  have h0 := congrFun h 0
  have h2 := congrFun h 2
  by_cases hε : 0 < a 0
  · simp only [cvec, hε, ↓reduceIte, Fin.isValue, cons_val_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, div_left_inj', cons_val, neg_inj, mul_eq_mul_left_iff, Complex.I_ne_zero,
      or_false] at h0 h2
    exact ⟨h0, h2⟩
  · simp only [cvec, hε, ↓reduceIte, Fin.isValue, cons_val_zero, neg_inj, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, div_left_inj', mul_eq_mul_left_iff,
      Complex.I_ne_zero, or_false, cons_val] at h0 h2
    exact ⟨h0, h2⟩

/-- `lem:kernel`(b): общее ядро первых двух строк `𝔘⁰(ρ)` есть `{c(ξ,ζ)}`. -/
theorem kernel_b_iff {a : ℝ → ℝ} {m κ : ℝ} (h : HypH a m κ) (U : Forms) (ρ : ℂ)
    (v : Fin 4 → ℂ) :
    ((Ufrak0 a U ρ *ᵥ v) 0 = 0 ∧ (Ufrak0 a U ρ *ᵥ v) 1 = 0) ↔ ∃ ξ ζ, v = cvec a ξ ζ := by
  obtain ⟨c0, c1, c2, c3⟩ := chan_vals
  obtain ⟨s0, s1, s2, s3⟩ := sgn_vals
  constructor
  · rintro ⟨r0, r1⟩
    have t1 : (tau0 a 1 : ℂ) ≠ 0 := by exact_mod_cast (tau0_pos h 1 (Or.inl rfl)).ne'
    have t2 : (tau0 a (-1) : ℂ) ≠ 0 := by exact_mod_cast (tau0_pos h (-1) (Or.inr rfl)).ne'
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Ufrak0_row0 h, Ufrak0_row1 h,
      c0, c1, c2, c3, s0, s1, s2, s3] at r0 r1
    by_cases hε : 0 < a 0
    · have he : eps a = 1 := by simp [eps, hε]
      simp only [he] at r0 r1
      push_cast at r0 r1
      refine ⟨2 * v 0, 2 * Complex.I * v 2, ?_⟩
      have e1 : v 1 = v 0 := by
        have : Complex.I * (tau0 a 1 : ℂ) * (v 0 - v 1) = 0 := by linear_combination r1 / 2
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h (mul_ne_zero Complex.I_ne_zero t1)
        · exact (sub_eq_zero.1 h).symm
      have e3 : v 3 = - v 2 := by linear_combination r0 / 2
      have q2 : v 2 = -(Complex.I * (2 * Complex.I * v 2) / 2) := by
        linear_combination (v 2) * Complex.I_sq
      have q3 : v 3 = Complex.I * (2 * Complex.I * v 2) / 2 := by
        linear_combination e3 - v 2 * Complex.I_sq
      ext i; fin_cases i
      · simp [cvec, hε]
      · simpa [cvec, hε] using e1
      · simpa [cvec, hε] using q2
      · simpa [cvec, hε] using q3
    · have he : eps a = -1 := by simp [eps, hε]
      simp only [he] at r0 r1
      push_cast at r0 r1
      refine ⟨-2 * Complex.I * v 1, 2 * v 2, ?_⟩
      have e0 : v 0 = - v 1 := by linear_combination r0 / 2
      have e3 : v 3 = v 2 := by
        have : Complex.I * (tau0 a (-1) : ℂ) * (v 2 - v 3) = 0 := by linear_combination r1 / 2
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h (mul_ne_zero Complex.I_ne_zero t2)
        · exact (sub_eq_zero.1 h).symm
      have q0 : v 0 = -(Complex.I * (-2 * Complex.I * v 1) / 2) := by
        linear_combination e0 - (v 1) * Complex.I_sq
      have q1 : v 1 = Complex.I * (-2 * Complex.I * v 1) / 2 := by
        linear_combination (v 1) * Complex.I_sq
      ext i; fin_cases i
      · simpa [cvec, hε] using q0
      · simpa [cvec, hε] using q1
      · simp [cvec, hε]
      · simpa [cvec, hε] using e3
  · rintro ⟨ξ, ζ, rfl⟩
    rw [kernel_b_apply h]
    simp

end GeneralBC
end Involution

