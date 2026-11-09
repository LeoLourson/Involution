module

public import Involution.Folding.GeneralBCKernelDef

/-! # Лемма `lem:kernel`(a): формулы Эйлера

`W(x) 𝐃(x) E(x,ρ) c(ξ,ζ) = 𝐲⁰(x)` при всех `x`, `ρ` (без гипотез на `a`). -/

@[expose] public noncomputable section

open Matrix

namespace Involution
namespace GeneralBC

theorem chan_vals : chan 0 = 1 ∧ chan 1 = 1 ∧ chan 2 = -1 ∧ chan 3 = -1 := by
  simp [chan]
theorem sgn_vals : sgn 0 = 1 ∧ sgn 1 = -1 ∧ sgn 2 = 1 ∧ sgn 3 = -1 := by
  simp [sgn]

theorem cos_exp (z : ℂ) :
    Complex.cos z = (Complex.exp (z * Complex.I) + Complex.exp (-(z * Complex.I))) / 2 := by
  rw [Complex.cos, neg_mul]
theorem sin_exp (z : ℂ) : Complex.sin z =
    (Complex.exp (-(z * Complex.I)) - Complex.exp (z * Complex.I)) * Complex.I / 2 := by
  rw [Complex.sin, neg_mul]

theorem kernel_a (a : ℝ → ℝ) (ξ ζ ρ : ℂ) (x : ℝ) :
    (Wmat a x * Dmat a x * Emat a x ρ) *ᵥ cvec a ξ ζ = yPrin a ξ ζ ρ x := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  obtain ⟨c0, c1, c2, c3⟩ := chan_vals
  obtain ⟨s0, s1, s2, s3⟩ := sgn_vals
  have e : ∀ (r t : ℂ), Complex.I * r * t = r * t * Complex.I := fun _ _ => by ring
  ext i
  by_cases hε : 0 < a 0
  · fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Wmat, Dmat, Emat, gvec, cvec, yPrin, hε,
      chiP, chiP', chiM, chiM', c0, c1, c2, c3, s0, s1, s2, s3, Matrix.diagonal_apply, cos_exp,
      sin_exp] <;>
    simp only [e] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf
  · fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Wmat, Dmat, Emat, gvec, cvec, yPrin, hε,
      chiP, chiP', chiM, chiM', c0, c1, c2, c3, s0, s1, s2, s3, Matrix.diagonal_apply, cos_exp,
      sin_exp] <;>
    simp only [e] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf

end GeneralBC
end Involution

