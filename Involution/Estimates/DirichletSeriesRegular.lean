module

public import Involution.Estimates.DirichletSeriesZeros

/-! Критерий сильной регулярности для задачи Дирихле (предложение `prop:dir`).
* `DirichletStrongRegular F`: нули `F` с `Re ρ ≥ 0` попарно отделены положительным числом,
  и все, кроме конечного числа, простые (`analyticOrderAt = 1`).
* Достаточность: рациональное отношение `a / b = p / q` с нечётным `q`. -/

@[expose] public noncomputable section

namespace Involution

/-- Сильная регулярность по нулям `F`: нули с `0 ≤ Re ρ` попарно отделены числом `δ > 0`,
и вне конечного множества они простые. -/
def DirichletStrongRegular (F : ℂ → ℂ) : Prop :=
  (∃ δ : ℝ, 0 < δ ∧ ∀ ρ σ : ℂ, F ρ = 0 → F σ = 0 → 0 ≤ ρ.re → 0 ≤ σ.re → ρ ≠ σ →
      δ ≤ ‖ρ - σ‖) ∧
  {ρ : ℂ | 0 ≤ ρ.re ∧ F ρ = 0 ∧ analyticOrderAt F ρ ≠ 1}.Finite

/-- Общий нуль обоих сомножителей даёт целочисленное равенство `(2k+1) b = 2 j a`. -/
lemma dirCS_double_zero (a b : ℝ) (ρ : ℂ) (hc : Complex.cos (ρ * a) = 0)
    (hs : Complex.sin (ρ * b) = 0) :
    ∃ k j : ℤ, (2 * k + 1) * b = 2 * j * a := by
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hc
  obtain ⟨j, hj⟩ := Complex.sin_eq_zero_iff.mp hs
  refine ⟨k, j, ?_⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have E : (Real.pi : ℂ) * (((2 * k + 1) * b : ℝ) - ((2 * j * a : ℝ))) = 0 := by
    push_cast
    linear_combination (-2 * (b : ℂ)) * hk + 2 * (a : ℂ) * hj
  have := (mul_eq_zero.mp E).resolve_left hpi
  have h2 : (((2 * k + 1) * b : ℝ) : ℂ) = ((2 * j * a : ℝ) : ℂ) := sub_eq_zero.mp this
  exact_mod_cast h2

/-- Если `a / b = p / q` и `q` нечётно, общих нулей нет. -/
lemma dirCS_no_double_zero (a b : ℝ) (ha : 0 < a) (p q : ℕ) (hodd : Odd q)
    (h : b * p = a * q) (ρ : ℂ) (hc : Complex.cos (ρ * a) = 0)
    (hs : Complex.sin (ρ * b) = 0) : False := by
  obtain ⟨k, j, hkj⟩ := dirCS_double_zero a b ρ hc hs
  have h1 : ((2 * k + 1) * q : ℝ) * a = (2 * j * p : ℝ) * a := by
    linear_combination (p : ℝ) * hkj - (2 * (k : ℝ) + 1) * h
  have h2 : ((2 * k + 1) * q : ℝ) = (2 * j * p : ℝ) := mul_right_cancel₀ ha.ne' h1
  have h3 : (2 * k + 1) * (q : ℤ) = 2 * j * p := by exact_mod_cast h2
  have ho : Odd ((2 * k + 1) * (q : ℤ)) := by
    exact (odd_two_mul_add_one k).mul (by exact_mod_cast hodd)
  rw [h3] at ho
  exact (Int.not_even_iff_odd.mpr ho) ⟨j * p, by ring⟩

/-- Нули `dirCS` при `a / b = p / q` лежат в решётке `(π / (2 q a)) ℤ`. -/
lemma dirCS_zero_lattice (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (p q : ℕ) (hq : 0 < q)
    (h : b * p = a * q) (ρ : ℂ) (hρ : dirCS a b ρ = 0) :
    ∃ n : ℤ, ρ = ((Real.pi / (2 * q * a) * n : ℝ) : ℂ) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rcases (dirCS_eq_zero_iff a b ha.ne' hb.ne' ρ).mp hρ with ⟨k, hk⟩ | ⟨j, hj⟩
  · refine ⟨(2 * k + 1) * q, ?_⟩
    rw [hk]; congr 1; push_cast; field_simp
  · refine ⟨2 * j * p, ?_⟩
    rw [hj]; congr 1
    have hp : (p : ℝ) = a * q / b := by field_simp; linarith
    push_cast; rw [hp]; field_simp

/-- Достаточность: рациональное отношение с нечётным знаменателем. -/
theorem dirCS_strongRegular_of_rat (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (p q : ℕ)
    (hq : 0 < q) (hodd : Odd q) (h : b * p = a * q) :
    DirichletStrongRegular (dirCS a b) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  refine ⟨⟨Real.pi / (2 * q * a), by positivity, ?_⟩, ?_⟩
  · intro ρ σ hρ hσ _ _ hne
    obtain ⟨m, rfl⟩ := dirCS_zero_lattice a b ha hb p q hq h ρ hρ
    obtain ⟨n, rfl⟩ := dirCS_zero_lattice a b ha hb p q hq h σ hσ
    have hmn : m ≠ n := by rintro rfl; exact hne rfl
    have h1 : (1 : ℝ) ≤ |(m : ℝ) - n| := by
      have : (1 : ℤ) ≤ |m - n| := Int.one_le_abs (sub_ne_zero.mpr hmn)
      exact_mod_cast this
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      ← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < Real.pi / (2 * q * a))]
    nlinarith [(by positivity : 0 < Real.pi / (2 * q * a))]
  · refine (Set.finite_empty).subset ?_
    rintro ρ ⟨_, hF, hord⟩
    exact ((dirCS_order_ne_one_iff a b ha.ne' hb.ne' ρ hF).mp hord |>.elim
      (fun hc hs => dirCS_no_double_zero a b ha p q hodd h ρ hc hs))

end Involution
