module

public import Involution.Estimates.DirichletSeriesRegular
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
public import Mathlib.Analysis.Normed.Group.AddCircle

/-! Иррациональное отношение `a / b`: нули двух серий `dirCS a b` сколь угодно близки
(плотность дробных частей `{j α}`, Кронекер), поэтому сильной регулярности нет. -/

@[expose] public noncomputable section

namespace Involution

/-- Плотность: для иррационального `α` и `ε > 0` найдутся целые `j`, `m` с
`|j α - 1/2 - m| < ε`. -/
lemma exists_close_half (α : ℝ) (hα : Irrational α) (ε : ℝ) (hε : 0 < ε) :
    ∃ j m : ℤ, |(j : ℝ) * α - 1 / 2 - m| < ε := by
  have hd : DenseRange (· • ((α : ℝ) : AddCircle (1 : ℝ)) : ℤ → AddCircle (1 : ℝ)) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr (by simpa using hα)
  obtain ⟨j, hj⟩ := hd.exists_dist_lt (((1 / 2 : ℝ)) : AddCircle (1 : ℝ)) hε
  rw [dist_eq_norm] at hj
  have : ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) - j • ((α : ℝ) : AddCircle (1 : ℝ)) =
      ((1 / 2 - j * α : ℝ) : AddCircle (1 : ℝ)) := by simp
  rw [this, AddCircle.norm_eq] at hj
  refine ⟨j, -round ((1 : ℝ)⁻¹ * (1 / 2 - j * α)), ?_⟩
  rw [← abs_neg]
  convert hj using 2
  push_cast; ring

/-- То же с неотрицательным `j`. -/
lemma exists_close_half_nonneg (α : ℝ) (hα : Irrational α) (ε : ℝ) (hε : 0 < ε) :
    ∃ j m : ℤ, 0 ≤ j ∧ |(j : ℝ) * α - 1 / 2 - m| < ε := by
  obtain ⟨j, m, h⟩ := exists_close_half α hα ε hε
  rcases le_total 0 j with hj | hj
  · exact ⟨j, m, hj, h⟩
  · refine ⟨-j, -m - 1, by omega, ?_⟩
    rw [← abs_neg]
    convert h using 2
    push_cast; ring

/-- Иррациональное `a / b`: сильной регулярности нет. -/
theorem not_dirCS_strongRegular_of_irrational (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hirr : Irrational (a / b)) : ¬ DirichletStrongRegular (dirCS a b) := by
  rintro ⟨⟨δ, hδ, hsep⟩, -⟩
  have hπ := Real.pi_pos
  set ε : ℝ := min (1 / 2) (a * δ / Real.pi) with hεdef
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε ≤ 1 / 2 := min_le_left _ _
  have hε2 : ε ≤ a * δ / Real.pi := min_le_right _ _
  obtain ⟨j, m, hj, hd⟩ := exists_close_half_nonneg (a / b) hirr ε hε
  have hjr : (0 : ℝ) ≤ j := by exact_mod_cast hj
  have hd' := abs_lt.mp hd
  have hm : 0 ≤ m := by
    have : (-1 : ℝ) < m := by
      have : 0 ≤ (j : ℝ) * (a / b) := by positivity
      linarith
    have : (-1 : ℤ) < m := by exact_mod_cast this
    omega
  have hmr : (0 : ℝ) ≤ m := by exact_mod_cast hm
  have hzero : dirCS a b (((2 * (m : ℝ) + 1) * Real.pi / (2 * a) : ℝ) : ℂ) = 0 :=
    (dirCS_eq_zero_iff a b ha.ne' hb.ne' _).mpr (Or.inl ⟨m, by push_cast; rfl⟩)
  have hzero' : dirCS a b ((j * Real.pi / b : ℝ) : ℂ) = 0 :=
    (dirCS_eq_zero_iff a b ha.ne' hb.ne' _).mpr (Or.inr ⟨j, rfl⟩)
  have hne : (((2 * (m : ℝ) + 1) * Real.pi / (2 * a) : ℝ) : ℂ) ≠ ((j * Real.pi / b : ℝ) : ℂ) := by
    intro heq
    have heq' : (2 * (m : ℝ) + 1) * Real.pi / (2 * a) = j * Real.pi / b := by exact_mod_cast heq
    have hj0 : (j : ℝ) ≠ 0 := by
      intro h0
      rw [h0] at heq'
      simp only [zero_mul, zero_div] at heq'
      have : 0 < (2 * (m : ℝ) + 1) * Real.pi / (2 * a) :=
        div_pos (mul_pos (by linarith) hπ) (by positivity)
      linarith
    apply hirr
    refine ⟨((2 * m + 1 : ℤ) : ℚ) / ((2 * j : ℤ) : ℚ), ?_⟩
    push_cast
    field_simp
    field_simp at heq'
    linarith
  have hlt := hsep _ _ hzero hzero'
    (by rw [Complex.ofReal_re]; exact div_nonneg (mul_nonneg (by linarith) hπ.le) (by positivity))
    (by rw [Complex.ofReal_re]; exact div_nonneg (mul_nonneg hjr hπ.le) hb.le) hne
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hlt
  have hval : (2 * (m : ℝ) + 1) * Real.pi / (2 * a) - j * Real.pi / b =
      -(Real.pi / a) * ((j : ℝ) * (a / b) - 1 / 2 - m) := by
    field_simp; ring
  rw [hval, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < Real.pi / a)] at hlt
  have h1 : Real.pi / a * |(j : ℝ) * (a / b) - 1 / 2 - m| < Real.pi / a * ε :=
    mul_lt_mul_of_pos_left hd (by positivity)
  have h2 : Real.pi / a * ε ≤ δ := by
    calc Real.pi / a * ε ≤ Real.pi / a * (a * δ / Real.pi) :=
          mul_le_mul_of_nonneg_left hε2 (by positivity)
      _ = δ := by field_simp
  linarith

end Involution
