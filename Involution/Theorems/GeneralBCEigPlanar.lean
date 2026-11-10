module

public import Involution.Theorems.GeneralBCEigDisc
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Analytic.Order

/-! # Планарные данные: счёт нулей в кольцах и хорошие радиусы (пакет G6, thm:eig (b))

Из `PlanarData`: порядок нуля `F` не меньше единицы; в кольце `u < ‖z‖ ≤ u + 3` правой
полуплоскости не больше `K₀` различных нулей; в каждом отрезке `[u, u+1)` есть радиус `b`,
для которого все нормы нулей отстоят от `b` не меньше чем на `2ε`; далёкий нуль `F + η`
лежит в `δ`-окрестности нуля `F`. -/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace Involution
namespace GeneralBC

variable {F η : ℂ → ℂ} {L : ℝ}

/-- Кратность нуля `F`: `analyticOrderAt` в `ℕ`. -/
abbrev mult (f : ℂ → ℂ) (z : ℂ) : ℕ := zeroMult f z

theorem mult_pos_of_zero (hP : PlanarData F η L) {z : ℂ} (hz : F z = 0) : 1 ≤ mult F z := by
  obtain ⟨w, hw⟩ := hP.nz
  have hA : AnalyticAt ℂ F z := hP.entire.analyticAt z
  have hne : analyticOrderAt F z ≠ ⊤ := by
    intro htop
    have := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (f := F) z
      (fun x => hP.entire.analyticAt x)).1 htop
    exact hw (by rw [this]; rfl)
  have hne0 : analyticOrderAt F z ≠ 0 := by
    intro h0
    rw [analyticOrderAt_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact h0 hA
    · exact h0 hz
  unfold mult zeroMult analyticOrderNatAt
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hne
  rw [← hn] at hne0 ⊢
  simp only [ENat.toNat_natCast]
  have : n ≠ 0 := by
    intro h; apply hne0; rw [h]; rfl
  omega

/-- Нули `F` в правой полуплоскости в кольце `u < ‖z‖ ≤ u + 3`. -/
def rz (F : ℂ → ℂ) (u : ℝ) : Set ℂ := {z | F z = 0 ∧ 0 < z.re ∧ u < ‖z‖ ∧ ‖z‖ ≤ u + 3}

/-- В кольце `u < ‖z‖ ≤ u+3` правой полуплоскости не более `K` различных нулей `F`. -/
theorem window_card (hP : PlanarData F η L) :
    ∃ K : ℕ, ∀ u : ℝ, (rz F u).Finite ∧ (rz F u).ncard ≤ K := by
  obtain ⟨h₀, N₀, hstrip, hcount⟩ := hP.count
  set M : ℕ := ⌈h₀⌉₊ + 4 with hM
  refine ⟨M * N₀, fun u => ?_⟩
  let X : ℕ → ℝ := fun j => ((⌊u - h₀⌋ : ℤ) : ℝ) + (j : ℝ)
  let S : ℕ → Finset ℂ := fun j => (hcount (X j)).1.toFinset
  have hS : ∀ j, (S j).card ≤ N₀ := by
    intro j
    obtain ⟨hfin, hsum⟩ := hcount (X j)
    have h1 : (S j).card ≤ ∑ z ∈ S j, mult F z := by
      calc (S j).card = ∑ z ∈ S j, 1 := by simp
        _ ≤ ∑ z ∈ S j, mult F z := Finset.sum_le_sum (fun z hz => by
            have hz' := (hfin.mem_toFinset).1 hz
            exact mult_pos_of_zero hP hz'.1)
    have h2 : ∑ z ∈ S j, mult F z =
        ∑ᶠ z ∈ {z : ℂ | F z = 0 ∧ z.re ∈ Icc (X j) (X j + 1) ∧ |z.im| ≤ h₀}, mult F z :=
      (finsum_mem_eq_finite_toFinset_sum _ hfin).symm
    exact h1.trans (h2 ▸ hsum)
  have hsub : rz F u ⊆ ↑(Finset.biUnion (Finset.range M) S) := by
    intro z hz
    obtain ⟨hF, hre, hn1, hn2⟩ := hz
    have him := hstrip z hF
    have hnorm : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hre] at hnorm
    have hre1 : u - h₀ < z.re := by linarith
    have hre2 : z.re ≤ u + 3 := by
      have := Complex.re_le_norm z; linarith
    have hfl : ⌊u - h₀⌋ ≤ ⌊z.re⌋ := Int.floor_le_floor hre1.le
    simp only [Finset.coe_biUnion, Finset.coe_range, Set.mem_iUnion, Set.mem_Iio, Finset.mem_coe]
    refine ⟨(⌊z.re⌋ - ⌊u - h₀⌋).toNat, ?_, ?_⟩
    · have h3 : ((⌊z.re⌋ - ⌊u - h₀⌋ : ℤ) : ℝ) < (M : ℝ) := by
        have a1 := Int.floor_le z.re
        have a2 := Int.lt_floor_add_one (u - h₀)
        have a3 := Nat.le_ceil h₀
        have : (M : ℝ) = (⌈h₀⌉₊ : ℝ) + 4 := by rw [hM]; push_cast; ring
        push_cast; linarith
      have h4 : ((⌊z.re⌋ - ⌊u - h₀⌋ : ℤ)) < (M : ℤ) := by exact_mod_cast h3
      omega
    · have hj : (((⌊z.re⌋ - ⌊u - h₀⌋).toNat : ℕ) : ℤ) = ⌊z.re⌋ - ⌊u - h₀⌋ :=
        Int.toNat_of_nonneg (by omega)
      have hX : X (⌊z.re⌋ - ⌊u - h₀⌋).toNat = (⌊z.re⌋ : ℝ) := by
        have := congrArg (Int.cast : ℤ → ℝ) hj
        push_cast at this
        simp only [X]; linarith
      refine ((hcount _).1.mem_toFinset).2 ⟨hF, ⟨?_, ?_⟩, him.le⟩
      · rw [hX]; exact Int.floor_le _
      · rw [hX]; exact (Int.lt_floor_add_one _).le
  have hfin : (rz F u).Finite := (Finset.finite_toSet _).subset hsub
  refine ⟨hfin, ?_⟩
  calc (rz F u).ncard ≤ (↑(Finset.biUnion (Finset.range M) S) : Set ℂ).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (Finset.biUnion (Finset.range M) S).card := Set.ncard_coe_finset _
    _ ≤ ∑ j ∈ Finset.range M, (S j).card := Finset.card_biUnion_le
    _ ≤ ∑ j ∈ Finset.range M, N₀ := Finset.sum_le_sum (fun j _ => hS j)
    _ = M * N₀ := by simp

/-- `b` — `ε`-хороший радиус: нормы всех нулей `F` правой полуплоскости отстоят от `b`
не меньше чем на `2ε`. -/
def GoodRad (F : ℂ → ℂ) (ε b : ℝ) : Prop :=
  ∀ z : ℂ, F z = 0 → 0 < z.re → 2 * ε ≤ |‖z‖ - b|

/-- В каждом `[u, u+1)` есть хороший радиус, если `4εK < 1`, `ε ≤ 1/2`. -/
theorem exists_good_radius (hP : PlanarData F η L) :
    ∃ K : ℕ, ∀ ε u : ℝ, 0 < ε → 4 * ε * K < 1 → ε ≤ 1 / 2 →
      ∃ b ∈ Ico u (u + 1), GoodRad F ε b := by
  obtain ⟨K, hK⟩ := window_card hP
  refine ⟨K, fun ε u hε hεK hε2 => ?_⟩
  obtain ⟨hfin, hcard⟩ := hK (u - 1)
  set Zb : Finset ℂ := hfin.toFinset with hZb
  have hnot : ¬ (Ico u (u + 1) ⊆ ⋃ z ∈ Zb, Ioo (‖z‖ - 2 * ε) (‖z‖ + 2 * ε)) := by
    intro hsub
    have h1 : volume (Ico u (u + 1)) ≤
        volume (⋃ z ∈ Zb, Ioo (‖z‖ - 2 * ε) (‖z‖ + 2 * ε)) := measure_mono hsub
    have h2 := measure_biUnion_finset_le Zb (fun z => Ioo (‖z‖ - 2 * ε) (‖z‖ + 2 * ε))
      (μ := volume)
    simp only [Real.volume_Ioo, Real.volume_Ico] at h1 h2
    have h3 : (Zb.card : ℝ) ≤ K := by
      have : Zb.card = (rz F (u - 1)).ncard := by
        rw [hZb, ← Set.ncard_coe_finset, hfin.coe_toFinset]
      rw [this]; exact_mod_cast hcard
    have h4 : ENNReal.ofReal (u + 1 - u) ≤ ∑ z ∈ Zb, ENNReal.ofReal (‖z‖ + 2 * ε - (‖z‖ - 2 * ε)) :=
      h1.trans h2
    have h5 : ∑ z ∈ Zb, ENNReal.ofReal (‖z‖ + 2 * ε - (‖z‖ - 2 * ε)) =
        ENNReal.ofReal (Zb.card * (4 * ε)) := by
      rw [Finset.sum_congr rfl (fun z _ => by
        rw [show ‖z‖ + 2 * ε - (‖z‖ - 2 * ε) = 4 * ε by ring])]
      rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity)]
      simp
    rw [h5] at h4
    have h6 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h4
    nlinarith
  rw [Set.not_subset] at hnot
  obtain ⟨b, hb, hbn⟩ := hnot
  refine ⟨b, hb, fun z hz hre => ?_⟩
  by_cases hzin : u - 1 < ‖z‖ ∧ ‖z‖ ≤ u + 2
  · have hzmem : z ∈ Zb := (hfin.mem_toFinset).2 ⟨hz, hre, hzin.1, by linarith [hzin.2]⟩
    simp only [mem_iUnion, not_exists] at hbn
    have := hbn z hzmem
    simp only [mem_Ioo, not_and_or, not_lt] at this
    rw [le_abs']
    rcases this with h | h
    · right; linarith
    · left; linarith
  · rw [not_and_or, not_lt, not_le] at hzin
    rw [le_abs']
    rcases hzin with h | h
    · left; have := hb.1; linarith
    · right; have := hb.2; linarith

/-- Далёкий нуль `F + η` лежит в `δ`-окрестности нуля `F`. -/
theorem near_zero (hP : PlanarData F η L) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, ∀ ρ : ℂ, r ≤ ‖ρ‖ → F ρ + η ρ = 0 → ∃ z : ℂ, F z = 0 ∧ ‖ρ - z‖ < δ := by
  obtain ⟨c, hc, hb⟩ := hP.lowb δ hδ
  obtain ⟨r, hr⟩ := hP.small (c / 2) (by positivity)
  refine ⟨r, fun ρ hρ h0 => ?_⟩
  by_contra hcon
  have hall : ∀ z : ℂ, F z = 0 → δ ≤ ‖ρ - z‖ := by
    intro z hz
    by_contra hlt
    exact hcon ⟨z, hz, not_le.1 hlt⟩
  have h1 := hb ρ hall
  have h2 := hr ρ hρ
  have h3 : ‖F ρ‖ = ‖η ρ‖ := by
    rw [eq_neg_of_add_eq_zero_left h0, norm_neg]
  have hexp : Real.exp (-L * |ρ.im|) * Real.exp (L * |ρ.im|) = 1 := by
    rw [← Real.exp_add]; simp
  have h4 : ‖η ρ‖ ≤ c / 2 * Real.exp (L * |ρ.im|) := by
    calc ‖η ρ‖ = ‖η ρ‖ * (Real.exp (-L * |ρ.im|) * Real.exp (L * |ρ.im|)) := by
          rw [hexp, mul_one]
      _ = ‖η ρ‖ * Real.exp (-L * |ρ.im|) * Real.exp (L * |ρ.im|) := by ring
      _ ≤ c / 2 * Real.exp (L * |ρ.im|) := mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  have := Real.exp_pos (L * |ρ.im|)
  nlinarith

/-- Ненулевая кратность в точке аналитичности означает нуль функции. -/
theorem eq_zero_of_mult_ne_zero {f : ℂ → ℂ} {z : ℂ} (hA : AnalyticAt ℂ f z)
    (h : mult f z ≠ 0) : f z = 0 := by
  by_contra hne
  apply h
  unfold mult zeroMult analyticOrderNatAt
  rw [hA.analyticOrderAt_eq_zero.2 hne]
  rfl

end GeneralBC
end Involution
