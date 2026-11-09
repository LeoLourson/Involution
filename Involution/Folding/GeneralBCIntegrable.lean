module

public import Involution.Folding.GeneralBCExternal
public import Involution.Folding.GeneralBCSystem
public import Involution.Setup.IntegralGronwallL1
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Суммируемость подынтегральной функции решения интегрального уравнения

Если `Z x = Z 0 + ∫₀ˣ M Z` при всех `x ∈ [0,1]` (поэлементно, интеграл Лебега равен `0` для
несуммируемой функции) и элементы `M` суммируемы, то элементы `M Z` суммируемы на `[0,1]`.
Непрерывность `Z` не предполагается: поэлементно `Z` непрерывна на отрезке суммируемости и
равна `Z 0` вне него. Границу `T` отрезков суммируемости оценивает неравенство Гронуолла с
весом из `L₁` (`Involution.gronwall_L1_bound`), далее непрерывность справа от `T` даёт
противоречие. -/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology

namespace Involution
namespace GeneralBC

variable {n : ℕ}

/-- Сумма модулей элементов произведения не превосходит произведения сумм. -/
theorem sum_norm_mul_le (A B : Matrix (Fin n) (Fin n) ℂ) :
    ∑ i, ∑ j, ‖(A * B) i j‖ ≤ (∑ i, ∑ k, ‖A i k‖) * ∑ k, ∑ j, ‖B k j‖ := by
  have h1 : ∀ i j, ‖(A * B) i j‖ ≤ ∑ k, ‖A i k‖ * ‖B k j‖ := fun i j => by
    rw [Matrix.mul_apply]
    exact (norm_sum_le _ _).trans (by simp)
  calc ∑ i, ∑ j, ‖(A * B) i j‖ ≤ ∑ i, ∑ j, ∑ k, ‖A i k‖ * ‖B k j‖ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
    _ = ∑ i, ∑ k, ‖A i k‖ * ∑ j, ‖B k j‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
    _ ≤ ∑ i, ∑ k, ‖A i k‖ * ∑ k, ∑ j, ‖B k j‖ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (f := fun k => ∑ j, ‖B k j‖) (fun k _ =>
              Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ k))
            (norm_nonneg _)
    _ = _ := by simp only [← Finset.sum_mul]

/-- Множество `S i j` — точки `t ∈ [0,1]`, где `f` суммируема на `[0,t]`. -/
def intSet (f : ℝ → ℂ) : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧ IntervalIntegrable f volume 0 t}

theorem intSet_mono {f : ℝ → ℂ} {t s : ℝ} (ht : t ∈ intSet f) (hs : s ∈ Icc 0 t) :
    s ∈ intSet f :=
  ⟨⟨hs.1, hs.2.trans ht.1.2⟩, ht.2.mono_set (by
    rw [uIcc_of_le ht.1.1, uIcc_of_le hs.1]; exact Icc_subset_Icc le_rfl hs.2)⟩

theorem intSet_ordConnected (f : ℝ → ℂ) : (intSet f).OrdConnected :=
  ⟨fun _ hx _ hy _ hz => intSet_mono hy ⟨hx.1.1.trans hz.1, hz.2⟩⟩

theorem intSet_zero (f : ℝ → ℂ) : (0 : ℝ) ∈ intSet f :=
  ⟨⟨le_rfl, zero_le_one⟩, by simp⟩

/-- Для `Z x = z + ∫₀ˣ f` непрерывность на отрезке суммируемости. -/
theorem continuousOn_of_mem_intSet {f Z : ℝ → ℂ} {z : ℂ}
    (hZ : ∀ x ∈ Icc (0 : ℝ) 1, Z x = z + ∫ t in (0 : ℝ)..x, f t) {y : ℝ}
    (hy : y ∈ intSet f) : ContinuousOn Z (Icc 0 y) := by
  have hI : IntegrableOn f (uIcc (0 : ℝ) y) volume := by
    rw [uIcc_of_le hy.1.1]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hy.1.1).1 hy.2
  have := (intervalIntegral.continuousOn_primitive_interval hI).const_add z
  rw [uIcc_of_le hy.1.1] at this
  exact this.congr fun x hx => hZ x ⟨hx.1, hx.2.trans hy.1.2⟩

theorem continuousOn_intSet {f Z : ℝ → ℂ} {z : ℂ}
    (hZ : ∀ x ∈ Icc (0 : ℝ) 1, Z x = z + ∫ t in (0 : ℝ)..x, f t) :
    ContinuousOn Z (intSet f) := by
  intro x0 hx0
  by_cases h : ∃ y ∈ intSet f, x0 < y
  · obtain ⟨y, hy, hxy⟩ := h
    refine ((continuousOn_of_mem_intSet hZ hy) x0 ⟨hx0.1.1, hxy.le⟩).mono_of_mem_nhdsWithin ?_
    exact mem_nhdsWithin.2 ⟨Iio y, isOpen_Iio, hxy, fun z hz => ⟨hz.2.1.1, hz.1.le⟩⟩
  · push Not at h
    exact ((continuousOn_of_mem_intSet hZ hx0) x0 ⟨hx0.1.1, le_rfl⟩).mono fun s hs =>
      ⟨hs.1.1, h s hs⟩

theorem eq_of_notMem_intSet {f Z : ℝ → ℂ} {z : ℂ}
    (hZ : ∀ x ∈ Icc (0 : ℝ) 1, Z x = z + ∫ t in (0 : ℝ)..x, f t) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hn : t ∉ intSet f) : Z t = z := by
  rw [hZ t ht, intervalIntegral.integral_undef fun h => hn ⟨ht, h⟩, add_zero]

theorem aestronglyMeasurable_of_integral {f Z : ℝ → ℂ} {z : ℂ}
    (hZ : ∀ x ∈ Icc (0 : ℝ) 1, Z x = z + ∫ t in (0 : ℝ)..x, f t) :
    AEStronglyMeasurable Z (volume.restrict (Ioc 0 1)) := by
  classical
  have hm : Measurable ((intSet f).piecewise Z fun _ => z) :=
    (continuousOn_intSet hZ).measurable_piecewise continuousOn_const
      (intSet_ordConnected f).measurableSet
  refine hm.aestronglyMeasurable.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  by_cases h : t ∈ intSet f
  · rw [piecewise_eq_of_mem _ _ _ h]
  · rw [piecewise_eq_of_notMem _ _ _ h, eq_of_notMem_intSet hZ ⟨ht.1.le, ht.2⟩ h]


section Main

variable {M Z : ℝ → Matrix (Fin n) (Fin n) ℂ}

theorem ii_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} {a b : ℝ}
    (h : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun x => ∑ i ∈ s, f i x) volume a b := by
  have := IntervalIntegrable.sum (ε := ℝ) s h
  convert this using 1
  ext x
  simp

/-- Подынтегральные функции измеримы. -/
theorem aesm_entry
    (hM : ∀ i j, IntervalIntegrable (fun x => M x i j) volume 0 1)
    (hZ : ∀ x ∈ Icc (0 : ℝ) 1, ∀ i j, Z x i j = Z 0 i j + ∫ t in (0 : ℝ)..x, (M t * Z t) i j)
    (i j : Fin n) :
    AEStronglyMeasurable (fun t => (M t * Z t) i j) (volume.restrict (Ioc 0 1)) := by
  simp_rw [Matrix.mul_apply]
  refine Finset.aestronglyMeasurable_fun_sum _ fun k _ => ?_
  exact (hM i k).1.aestronglyMeasurable.mul (aestronglyMeasurable_of_integral
    (f := fun t => (M t * Z t) k j) (z := Z 0 k j) (Z := fun t => Z t k j)
    (fun x hx => hZ x hx k j))

/-- Суммируемость при ограниченности `Z` на `(0,t)`. -/
theorem integrable_of_bound
    (hM : ∀ i j, IntervalIntegrable (fun x => M x i j) volume 0 1)
    (hZ : ∀ x ∈ Icc (0 : ℝ) 1, ∀ i j, Z x i j = Z 0 i j + ∫ t in (0 : ℝ)..x, (M t * Z t) i j)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1) (C : Fin n → Fin n → ℝ)
    (hb : ∀ s ∈ Ioo 0 t, ∀ k l, ‖Z s k l‖ ≤ C k l) (i j : Fin n) :
    IntervalIntegrable (fun x => (M x * Z x) i j) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht0]
  have hsub : Ioo (0 : ℝ) t ⊆ Ioc 0 1 := Ioo_subset_Ioc_self.trans (Ioc_subset_Ioc_right ht)
  have hMi : ∀ i k, IntegrableOn (fun s => M s i k) (Ioo 0 t) := fun i k =>
    (hM i k).1.mono_set hsub
  have hg : Integrable (fun s => ∑ k, ‖M s i k‖ * C k j) (volume.restrict (Ioo 0 t)) :=
    integrable_finsetSum _ fun k _ => (hMi i k).norm.mul_const _
  refine hg.mono' ((aesm_entry hM hZ i j).mono_measure (Measure.restrict_mono hsub le_rfl)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb s hs k j) (norm_nonneg _)

/-- Оценка Гронуолла на отрезках суммируемости, равномерная по отрезку. -/
theorem exists_bound_nu
    (hM : ∀ i j, IntervalIntegrable (fun x => M x i j) volume 0 1)
    (hZ : ∀ x ∈ Icc (0 : ℝ) 1, ∀ i j, Z x i j = Z 0 i j + ∫ t in (0 : ℝ)..x, (M t * Z t) i j) :
    ∃ B : ℝ, ∀ x ∈ Icc (0 : ℝ) 1,
      (∀ i j, IntervalIntegrable (fun s => (M s * Z s) i j) volume 0 x) →
      ∀ t ∈ Icc 0 x, ∑ i, ∑ j, ‖Z t i j‖ ≤ B := by
  set m : ℝ → ℝ := fun t => ∑ i, ∑ k, ‖M t i k‖ with hmdef
  have hm0 : ∀ t, 0 ≤ m t := fun t => Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun k _ => norm_nonneg _
  have hm : IntervalIntegrable m volume 0 1 := by
    refine ii_sum _ fun i _ => ?_
    exact ii_sum _ fun k _ => (hM i k).norm
  obtain ⟨B, hB⟩ := gronwall_L1_bound hm0 hm
    (c := ∑ i, ∑ j, ‖Z 0 i j‖) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      norm_nonneg _)
  refine ⟨B, fun x hx hint => ?_⟩
  have hsubx : ∀ t ∈ Icc (0 : ℝ) x, Icc (0 : ℝ) t ⊆ Icc 0 x := fun t ht =>
    Icc_subset_Icc le_rfl ht.2
  have hcont : ∀ i j, ContinuousOn (fun t => Z t i j) (Icc 0 x) := fun i j =>
    continuousOn_of_mem_intSet (f := fun t => (M t * Z t) i j) (z := Z 0 i j)
      (fun y hy => hZ y hy i j) (y := x) ⟨hx, hint i j⟩
  have hu : ContinuousOn (fun t => ∑ i, ∑ j, ‖Z t i j‖) (Icc 0 x) :=
    continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => (hcont i j).norm
  refine hB x hx _ hu (fun t _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    norm_nonneg _) (fun t ht => ?_)
  have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hx.2⟩
  have hintt : ∀ i j, IntervalIntegrable (fun s => (M s * Z s) i j) volume 0 t := fun i j =>
    (hint i j).mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le hx.1]; exact Icc_subset_Icc le_rfl ht.2)
  have hmt : IntervalIntegrable m volume 0 t := hm.mono_set (by
    rw [uIcc_of_le ht.1, uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl ht1.2)
  have hmu : IntervalIntegrable (fun s => m s * ∑ i, ∑ j, ‖Z s i j‖) volume 0 t :=
    hmt.mul_continuousOn (hu.mono (by rw [uIcc_of_le ht.1]; exact hsubx t ht))
  have h1 : ∀ i j, ‖Z t i j‖ ≤ ‖Z 0 i j‖ + ∫ s in (0 : ℝ)..t, ‖(M s * Z s) i j‖ := fun i j => by
    rw [hZ t ht1 i j]
    have := intervalIntegral.norm_integral_le_integral_norm
      (f := fun s => (M s * Z s) i j) (μ := volume) ht.1
    exact (norm_add_le _ _).trans (by linarith)
  calc ∑ i, ∑ j, ‖Z t i j‖
      ≤ ∑ i, ∑ j, (‖Z 0 i j‖ + ∫ s in (0 : ℝ)..t, ‖(M s * Z s) i j‖) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
    _ = (∑ i, ∑ j, ‖Z 0 i j‖) + ∫ s in (0 : ℝ)..t, ∑ i, ∑ j, ‖(M s * Z s) i j‖ := by
        simp only [Finset.sum_add_distrib]
        congr 1
        rw [intervalIntegral.integral_finsetSum fun i _ =>
          ii_sum _ fun j _ => (hintt i j).norm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [intervalIntegral.integral_finsetSum fun j _ => (hintt i j).norm]
    _ ≤ _ := by
        refine add_le_add_right (intervalIntegral.integral_mono_on ht.1
          (ii_sum _ fun i _ => ii_sum _ fun j _ => (hintt i j).norm) hmu fun s _ => ?_) _
        exact sum_norm_mul_le (M s) (Z s)

/-- Основная лемма: элементы `M Z` суммируемы на `[0,1]` (матрицы `Fin n`). -/
theorem matSol_integrable_gen
    (hM : ∀ i j, IntervalIntegrable (fun x => M x i j) volume 0 1)
    (hZ : ∀ x ∈ Icc (0 : ℝ) 1, ∀ i j, Z x i j = Z 0 i j + ∫ t in (0 : ℝ)..x, (M t * Z t) i j) :
    ∀ i j, IntervalIntegrable (fun x => (M x * Z x) i j) volume 0 1 := by
  classical
  obtain ⟨B, hB⟩ := exists_bound_nu hM hZ
  let S : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧
    ∀ i j, IntervalIntegrable (fun s => (M s * Z s) i j) volume 0 t}
  have hS0 : (0 : ℝ) ∈ S := ⟨⟨le_rfl, zero_le_one⟩, fun i j => by simp⟩
  have hSbdd : BddAbove S := ⟨1, fun t ht => ht.1.2⟩
  have hSmono : ∀ t ∈ S, ∀ s ∈ Icc (0 : ℝ) t, s ∈ S := fun t ht s hs =>
    ⟨⟨hs.1, hs.2.trans ht.1.2⟩, fun i j => (ht.2 i j).mono_set (by
      rw [uIcc_of_le ht.1.1, uIcc_of_le hs.1]; exact Icc_subset_Icc le_rfl hs.2)⟩
  have hT : sSup S ∈ Icc (0 : ℝ) 1 :=
    ⟨le_csSup hSbdd hS0, csSup_le ⟨0, hS0⟩ fun t ht => ht.1.2⟩
  have hlt : ∀ t, 0 ≤ t → t < sSup S → t ∈ S := fun t ht0 h => by
    obtain ⟨s, hs, hts⟩ := exists_lt_of_lt_csSup ⟨0, hS0⟩ h
    exact hSmono s hs t ⟨ht0, hts.le⟩
  have hentry : ∀ t ∈ S, ∀ k l, ‖Z t k l‖ ≤ B := fun t ht k l => by
    have h1 := hB t ht.1 ht.2 t ⟨ht.1.1, le_rfl⟩
    refine le_trans ?_ h1
    refine le_trans (Finset.single_le_sum (f := fun j => ‖Z t k j‖) (fun j _ => norm_nonneg _)
      (Finset.mem_univ l)) ?_
    exact Finset.single_le_sum (f := fun i => ∑ j, ‖Z t i j‖)
      (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ k)
  have hTS : sSup S ∈ S := ⟨hT, fun i j => integrable_of_bound hM hZ hT.1 hT.2 (fun _ _ => B)
    (fun s hs k l => hentry s (hlt s hs.1.le hs.2) k l) i j⟩
  have hle : ∀ s ∈ Icc (0 : ℝ) (sSup S), s ∈ S := hSmono _ hTS
  have hT1 : sSup S = 1 := by
    by_contra hne
    have hT1 : sSup S < 1 := lt_of_le_of_ne hT.2 hne
    have ent : ∀ k l, ∀ᶠ t in 𝓝[>] (sSup S), ∃ C : ℝ, ∀ s ∈ Icc (0 : ℝ) t, ‖Z s k l‖ ≤ C := by
      intro k l
      by_cases h : ∃ t0 ∈ intSet (fun s => (M s * Z s) k l), sSup S < t0
      · obtain ⟨t0, ht0, hTt0⟩ := h
        have hc := continuousOn_of_mem_intSet (Z := fun t => Z t k l) (z := Z 0 k l)
          (fun x hx => hZ x hx k l) ht0
        obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
        filter_upwards [Ioo_mem_nhdsGT hTt0] with t ht
        exact ⟨C, fun s hs => hC s ⟨hs.1, hs.2.trans ht.2.le⟩⟩
      · push Not at h
        filter_upwards [Ioo_mem_nhdsGT hT1] with t ht
        refine ⟨max B ‖Z 0 k l‖, fun s hs => ?_⟩
        by_cases hsT : s ≤ sSup S
        · exact (hentry s (hle s ⟨hs.1, hsT⟩) k l).trans (le_max_left _ _)
        · rw [not_le] at hsT
          have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht.2.le⟩
          have hn : s ∉ intSet (fun s => (M s * Z s) k l) := fun hh =>
            absurd (h s hh) (not_le.2 hsT)
          rw [eq_of_notMem_intSet (Z := fun t => Z t k l) (z := Z 0 k l)
            (fun x hx => hZ x hx k l) hs1 hn]
          exact le_max_right _ _
    have ev : ∀ᶠ t in 𝓝[>] (sSup S), (∀ k l, ∃ C : ℝ, ∀ s ∈ Icc (0 : ℝ) t, ‖Z s k l‖ ≤ C) ∧
        t ∈ Ioo (sSup S) 1 :=
      (Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun l => ent k l).and
        (Ioo_mem_nhdsGT hT1)
    obtain ⟨t, hC, ht⟩ := ev.exists
    choose C hC using hC
    have hq : t ∈ S := ⟨⟨(hT.1.trans ht.1.le), ht.2.le⟩, fun i j =>
      integrable_of_bound hM hZ (hT.1.trans ht.1.le) ht.2.le C
        (fun s hs k l => hC k l s ⟨hs.1.le, hs.2.le⟩) i j⟩
    exact absurd (le_csSup hSbdd hq) (not_le.2 ht.1)
  have := hTS.2
  rwa [hT1] at this

end Main

section Final

/-- Лемма Л1 плана G2: у `IsMatSol` подынтегральная функция суммируема. -/
theorem isMatSol_integrable {M Z : ℝ → Matrix (Fin 4) (Fin 4) ℂ}
    (hM : ∀ i j, IntervalIntegrable (fun x => M x i j) volume 0 1) (hZ : IsMatSol M Z) :
    ∀ i j, IntervalIntegrable (fun x => (M x * Z x) i j) volume 0 1 :=
  matSol_integrable_gen hM hZ

/-- Вариант для `IsSol`: подынтегральная функция `ρ • (K Y)` суммируема, если суммируема `K`. -/
theorem isSol_integrable {a : ℝ → ℝ} {ρ : ℂ} {Y : ℝ → Matrix (Fin 4) (Fin 4) ℂ}
    (hK : ∀ i j, IntervalIntegrable (fun x => Kmat a x i j) volume 0 1) (hY : IsSol a ρ Y) :
    ∀ i j, IntervalIntegrable (fun x => (ρ • (Kmat a x * Y x)) i j) volume 0 1 := by
  have hM : ∀ i j, IntervalIntegrable (fun x => (ρ • Kmat a x) i j) volume 0 1 := fun i j => by
    simpa using (hK i j).const_mul ρ
  have h := matSol_integrable_gen (M := fun x => ρ • Kmat a x) (Z := Y) hM
    (fun x hx i j => by rw [hY x hx i j]; simp)
  simpa [Matrix.smul_mul] using h

end Final

end GeneralBC
end Involution

end
