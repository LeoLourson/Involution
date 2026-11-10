module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecificLimits.Normed

/-! Оценки вольтерровского типа: если `‖g t‖ ≤ C (M t)^k / k!` на `[0,x]`, то интеграл
`∫₀ˣ g` оценивается величиной `C M^k x^(k+1) / (k+1)!`. Отсюда единственность
решения интегрального уравнения `D(x) = ∫₀ˣ B D` с `‖B‖ ≤ M` (вариант леммы Гронуолла). -/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Involution

/-- Один шаг итерации Вольтерры. -/
theorem norm_integral_le_poly {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g : ℝ → V} {C M x : ℝ} {k : ℕ} (hx : 0 ≤ x)
    (hg : ∀ t ∈ Icc 0 x, ‖g t‖ ≤ C * (M * t) ^ k / k.factorial) :
    ‖∫ t in (0 : ℝ)..x, g t‖ ≤ C * M ^ k * x ^ (k + 1) / (k + 1).factorial := by
  have hint : IntervalIntegrable (fun t : ℝ => C * (M * t) ^ k / k.factorial) volume 0 x :=
    (by fun_prop : Continuous fun t : ℝ => C * (M * t) ^ k / k.factorial).intervalIntegrable _ _
  refine (intervalIntegral.norm_integral_le_of_norm_le hx
    (Filter.Eventually.of_forall fun t ht => hg t (Ioc_subset_Icc_self ht)) hint).trans
    (le_of_eq ?_)
  have h1 : (fun t : ℝ => C * (M * t) ^ k / k.factorial)
      = fun t => (C * M ^ k / k.factorial) * t ^ k := by
    ext t; rw [mul_pow]; ring
  rw [h1, intervalIntegral.integral_const_mul, integral_pow, Nat.factorial_succ]
  push_cast
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- Единственность: непрерывная на `[0,T]` функция `D` с оценкой
`‖D x‖ ≤ M ∫₀ˣ ‖D‖` тождественно равна нулю. -/
theorem eq_zero_of_norm_le_integral {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {D : ℝ → V} {M T : ℝ} (hD : ContinuousOn D (Icc 0 T)) (hM : 0 ≤ M)
    (h : ∀ x ∈ Icc (0 : ℝ) T, ‖D x‖ ≤ M * ∫ t in (0 : ℝ)..x, ‖D t‖) :
    ∀ x ∈ Icc (0 : ℝ) T, D x = 0 := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hD
  have key : ∀ k : ℕ, ∀ x ∈ Icc (0 : ℝ) T, ‖D x‖ ≤ max C 0 * (M * x) ^ k / k.factorial := by
    intro k
    induction k with
    | zero =>
      intro x hx
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
      exact (hC x hx).trans (le_max_left _ _)
    | succ k ih =>
      intro x hx
      have h0 : 0 ≤ x := hx.1
      have hb : ∀ t ∈ Icc 0 x, ‖‖D t‖‖ ≤ max C 0 * (M * t) ^ k / k.factorial := by
        intro t ht
        rw [norm_norm]
        exact ih t ⟨ht.1, ht.2.trans hx.2⟩
      have h2 := norm_integral_le_poly (V := ℝ) h0 hb
      have h3 : ∫ t in (0 : ℝ)..x, ‖D t‖ ≤ max C 0 * M ^ k * x ^ (k + 1) / (k + 1).factorial :=
        (le_abs_self _).trans (by simpa using h2)
      refine (h x hx).trans ?_
      calc M * ∫ t in (0 : ℝ)..x, ‖D t‖
          ≤ M * (max C 0 * M ^ k * x ^ (k + 1) / (k + 1).factorial) :=
            mul_le_mul_of_nonneg_left h3 hM
        _ = max C 0 * (M * x) ^ (k + 1) / (k + 1).factorial := by ring
  intro x hx
  have hlim : Filter.Tendsto (fun k : ℕ => max C 0 * ((M * x) ^ k / k.factorial)) Filter.atTop
      (nhds 0) := by
    simpa using (Real.summable_pow_div_factorial (M * x)).tendsto_atTop_zero.const_mul (max C 0)
  have : ‖D x‖ ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hlim (fun k => by
      have := key k x hx
      rwa [mul_div_assoc] at this)
  exact norm_le_zero_iff.mp this

/-- Вольтерровская единственность в форме интегрального уравнения: если
`u x = ∫₀ˣ F`, `‖F t‖ ≤ M ‖u t‖` и `u` непрерывна на `[0,1]`, то `u = 0` на `[0,1]`. -/
theorem eq_zero_of_integral_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {u F : ℝ → V} {M : ℝ} (hu : ContinuousOn u (Icc 0 1)) (hM : 0 ≤ M)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, ‖F t‖ ≤ M * ‖u t‖)
    (h : ∀ x ∈ Icc (0 : ℝ) 1, u x = ∫ t in (0 : ℝ)..x, F t) :
    ∀ x ∈ Icc (0 : ℝ) 1, u x = 0 := by
  refine eq_zero_of_norm_le_integral hu hM (fun x hx => ?_)
  have hsub : uIcc (0 : ℝ) x ⊆ Icc 0 1 := by
    rw [uIcc_of_le hx.1]; exact Icc_subset_Icc le_rfl hx.2
  have hint : IntervalIntegrable (fun t => M * ‖u t‖) volume 0 x :=
    ((continuousOn_const.mul hu.norm).mono hsub).intervalIntegrable
  rw [h x hx]
  refine (intervalIntegral.norm_integral_le_of_norm_le hx.1
    (Filter.Eventually.of_forall fun t ht => hF t ⟨ht.1.le, ht.2.trans hx.2⟩) hint).trans
    (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul]

/-- Обратная единственность: если `u x = ∫_{x₀}ˣ F` на `[0,1]` (то есть `u x₀ = 0`) и
`‖F t‖ ≤ M ‖u t‖`, то `u 0 = 0`. -/
theorem eq_zero_at_zero_of_integral_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {u F : ℝ → V} {M x₀ : ℝ} (hx₀ : x₀ ∈ Icc (0 : ℝ) 1) (hu : ContinuousOn u (Icc 0 1))
    (hM : 0 ≤ M) (hF : ∀ t ∈ Icc (0 : ℝ) 1, ‖F t‖ ≤ M * ‖u t‖)
    (h : ∀ x ∈ Icc (0 : ℝ) 1, u x = ∫ t in x₀..x, F t) : u 0 = 0 := by
  have hmap : ∀ s ∈ Icc (0 : ℝ) x₀, x₀ - s ∈ Icc (0 : ℝ) 1 := fun s hs =>
    ⟨by linarith [hs.2], by linarith [hs.1, hx₀.2]⟩
  have hcont : ContinuousOn (fun s => u (x₀ - s)) (Icc 0 x₀) :=
    hu.comp (by fun_prop) hmap
  have key := eq_zero_of_norm_le_integral (D := fun s => u (x₀ - s)) (T := x₀) hcont hM
    (fun s hs => by
      have hsm := hmap s hs
      have hs0 : 0 ≤ s := hs.1
      have hle : x₀ - s ≤ x₀ := by linarith
      have hsub : Icc (x₀ - s) x₀ ⊆ Icc 0 1 := fun t ht =>
        ⟨hsm.1.trans ht.1, ht.2.trans hx₀.2⟩
      have hint : IntervalIntegrable (fun t => M * ‖u t‖) volume (x₀ - s) x₀ :=
        ((continuousOn_const.mul hu.norm).mono hsub).intervalIntegrable_of_Icc hle
      have h1 : ‖u (x₀ - s)‖ ≤ ∫ t in (x₀ - s)..x₀, M * ‖u t‖ := by
        rw [h _ hsm, intervalIntegral.integral_symm]
        rw [norm_neg]
        exact intervalIntegral.norm_integral_le_of_norm_le hle
          (Filter.Eventually.of_forall fun t ht => hF t (hsub ⟨ht.1.le, ht.2⟩)) hint
      have h2 : ∫ t in (x₀ - s)..x₀, M * ‖u t‖ = M * ∫ t in (0 : ℝ)..s, ‖u (x₀ - t)‖ := by
        rw [intervalIntegral.integral_const_mul]
        congr 1
        rw [intervalIntegral.integral_comp_sub_left (fun t => ‖u t‖) x₀]
        simp
      rwa [h2] at h1)
  simpa using key x₀ ⟨hx₀.1, le_rfl⟩

end Involution

end
