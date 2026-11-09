module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Ограниченность решений интегрального неравенства с весом из `L₁`

Если `m ≥ 0` суммируема на `[0,1]`, `u ≥ 0` непрерывна на `[0,x]` и
`u t ≤ c + ∫₀ᵗ m u`, то `u ≤ B`, где `B` зависит только от `m` и `c` (не от `x` и `u`).
Доказательство: разбиение `[0,1]` на отрезки длины `h`, на которых `∫ m ≤ 1/2`. -/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Involution

/-- Окно малой массы: `∃ h > 0`, `∫ₐᵇ m ≤ 1/2` при `0 ≤ a ≤ b ≤ 1`, `b − a ≤ h`. -/
theorem exists_small_window {m : ℝ → ℝ} (hm : IntervalIntegrable m volume 0 1) :
    ∃ h : ℝ, 0 < h ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → b - a ≤ h →
      ∫ t in a..b, m t ≤ 1 / 2 := by
  have hc : ContinuousOn (fun x => ∫ t in (0 : ℝ)..x, m t) (Icc 0 1) := by
    have hI : IntegrableOn m (uIcc (0 : ℝ) 1) volume := by
      rw [uIcc_of_le zero_le_one]
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).1 hm
    have := intervalIntegral.continuousOn_primitive_interval hI
    rwa [uIcc_of_le zero_le_one] at this
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hc
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨δ, hδ, hδ'⟩ := hu (1 / 2) (by norm_num)
  refine ⟨δ / 2, by positivity, fun a b ha hab hb hba => ?_⟩
  have h1 := hδ' b ⟨ha.trans hab, hb⟩ a ⟨ha, hab.trans hb⟩
    (by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith)
  rw [Real.dist_eq] at h1
  have hint : ∀ x y, x ∈ Icc (0 : ℝ) 1 → y ∈ Icc (0 : ℝ) 1 →
      IntervalIntegrable m volume x y := fun x y hx hy =>
    hm.mono_set (by rw [uIcc_of_le zero_le_one]; exact uIcc_subset_Icc hx hy)
  have e := intervalIntegral.integral_interval_sub_left (hint 0 b ⟨le_rfl, zero_le_one⟩
    ⟨ha.trans hab, hb⟩) (hint 0 a ⟨le_rfl, zero_le_one⟩ ⟨ha, hab.trans hb⟩)
  rw [e] at h1
  exact (le_abs_self _).trans h1.le

/-- Равномерная оценка по `x` и `u`. -/
theorem gronwall_L1_bound {m : ℝ → ℝ} (hm0 : ∀ t, 0 ≤ m t)
    (hm : IntervalIntegrable m volume 0 1) {c : ℝ} (hc : 0 ≤ c) :
    ∃ B : ℝ, ∀ x ∈ Icc (0 : ℝ) 1, ∀ u : ℝ → ℝ, ContinuousOn u (Icc 0 x) →
      (∀ t ∈ Icc 0 x, 0 ≤ u t) →
      (∀ t ∈ Icc 0 x, u t ≤ c + ∫ s in (0 : ℝ)..t, m s * u s) →
      ∀ t ∈ Icc 0 x, u t ≤ B := by
  obtain ⟨h, hh, hwin⟩ := exists_small_window hm
  set K := ∫ t in (0 : ℝ)..1, m t with hK
  have hK0 : 0 ≤ K := intervalIntegral.integral_nonneg zero_le_one (fun t _ => hm0 t)
  let β : ℕ → ℝ := fun k => Nat.rec c (fun _ b => max b (2 * (c + K * b))) k
  have hβ0 : ∀ k, c ≤ β k := by
    intro k; induction k with
    | zero => exact le_rfl
    | succ k ih => exact ih.trans (le_max_left _ _)
  have hβs : ∀ k, β (k + 1) = max (β k) (2 * (c + K * β k)) := fun k => rfl
  have hint : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a b, a ∈ Icc (0 : ℝ) x → b ∈ Icc (0 : ℝ) x →
      IntervalIntegrable m volume a b := fun x hx a b ha hb =>
    hm.mono_set (by
      rw [uIcc_of_le zero_le_one]
      exact uIcc_subset_Icc ⟨ha.1, ha.2.trans hx.2⟩ ⟨hb.1, hb.2.trans hx.2⟩)
  have key : ∀ k : ℕ, ∀ x ∈ Icc (0 : ℝ) 1, ∀ u : ℝ → ℝ, ContinuousOn u (Icc 0 x) →
      (∀ t ∈ Icc 0 x, 0 ≤ u t) →
      (∀ t ∈ Icc 0 x, u t ≤ c + ∫ s in (0 : ℝ)..t, m s * u s) →
      ∀ t ∈ Icc 0 x, t ≤ k * h → u t ≤ β k := by
    intro k
    induction k with
    | zero =>
      intro x hx u hu hu0 hI t ht htk
      have : t = 0 := le_antisymm (by simpa using htk) ht.1
      subst this
      have := hI 0 ⟨le_rfl, hx.1⟩
      simpa [β] using this
    | succ k ih =>
      intro x hx u hu hu0 hI t ht htk
      set T := min x ((k + 1) * h) with hT
      have hkh : 0 ≤ (k : ℝ) * h := by positivity
      have hTpos : 0 ≤ T := le_min hx.1 (by positivity)
      obtain ⟨t0, ht0, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hTpos)
        (hu.mono (Icc_subset_Icc le_rfl (min_le_left _ _)))
      have htT : t ∈ Icc 0 T := ⟨ht.1, le_min ht.2 (by push_cast at htk; exact htk)⟩
      refine (hmax htT).trans ?_
      have hx0 : t0 ∈ Icc 0 x := ⟨ht0.1, ht0.2.trans (min_le_left _ _)⟩
      by_cases hc0 : t0 ≤ k * h
      · exact (ih x hx u hu hu0 hI t0 hx0 hc0).trans (by rw [hβs]; exact le_max_left _ _)
      · rw [not_le] at hc0
        have hkx : (k : ℝ) * h ∈ Icc (0 : ℝ) x := ⟨hkh, hc0.le.trans hx0.2⟩
        have hmu : ∀ a b, a ∈ Icc (0 : ℝ) x → b ∈ Icc (0 : ℝ) x →
            IntervalIntegrable (fun s => m s * u s) volume a b := by
          intro a b ha hb
          exact (hint x hx a b ha hb).mul_continuousOn (hu.mono (uIcc_subset_Icc ha hb))
        have h0x : (0 : ℝ) ∈ Icc (0 : ℝ) x := ⟨le_rfl, hx.1⟩
        have hsplit := intervalIntegral.integral_add_adjacent_intervals
          (hmu 0 (k * h) h0x hkx) (hmu (k * h) t0 hkx hx0)
        have hb1 : ∫ s in (0 : ℝ)..(k * h), m s * u s ≤ K * β k := by
          have h1 : ∫ s in (0 : ℝ)..(k * h), m s * u s ≤ ∫ s in (0 : ℝ)..(k * h), m s * β k :=
            intervalIntegral.integral_mono_on hkh (hmu 0 (k * h) h0x hkx)
              ((hint x hx 0 (k * h) h0x hkx).mul_const _) (fun s hs =>
                mul_le_mul_of_nonneg_left (ih x hx u hu hu0 hI s ⟨hs.1, hs.2.trans hkx.2⟩ hs.2)
                  (hm0 s))
          rw [intervalIntegral.integral_mul_const] at h1
          have h2 : ∫ s in (0 : ℝ)..(k * h), m s ≤ K := by
            have := intervalIntegral.integral_add_adjacent_intervals
              (hint 1 ⟨zero_le_one, le_rfl⟩ 0 (k * h) ⟨le_rfl, zero_le_one⟩
                ⟨hkh, by linarith [hkx.2, hx.2]⟩ |> fun h => h)
              (hm.mono_set (by
                rw [uIcc_of_le zero_le_one, uIcc_of_le (by linarith [hkx.2, hx.2])]
                exact Icc_subset_Icc (by linarith [hkx.2, hx.2]) le_rfl) :
                IntervalIntegrable m volume (k * h) 1)
            have h3 : 0 ≤ ∫ s in (k * h)..1, m s :=
              intervalIntegral.integral_nonneg (by linarith [hkx.2, hx.2]) (fun s _ => hm0 s)
            linarith
          exact h1.trans (mul_le_mul_of_nonneg_right h2 ((hc.trans (hβ0 k))))
        have hb2 : ∫ s in (k * h)..t0, m s * u s ≤ 1 / 2 * u t0 := by
          have h1 : ∫ s in (k * h)..t0, m s * u s ≤ ∫ s in (k * h)..t0, m s * u t0 :=
            intervalIntegral.integral_mono_on hc0.le (hmu _ _ hkx hx0)
              ((hint x hx _ _ hkx hx0).mul_const _) (fun s hs =>
                mul_le_mul_of_nonneg_left
                  (hmax ⟨hkh.trans hs.1, hs.2.trans ht0.2⟩)
                  (hm0 s))
          rw [intervalIntegral.integral_mul_const] at h1
          have h2 : ∫ s in (k * h)..t0, m s ≤ 1 / 2 :=
            hwin _ _ hkh hc0.le (ht0.2.trans (min_le_left _ _) |>.trans hx.2)
              (by have := ht0.2.trans (min_le_right _ _); linarith)
          exact h1.trans (by nlinarith [hu0 t0 hx0])
        have hI0 := hI t0 hx0
        rw [← hsplit] at hI0
        have hβ' : 2 * (c + K * β k) ≤ β (k + 1) := by rw [hβs]; exact le_max_right _ _
        linarith
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / h)
  refine ⟨β N, fun x hx u hu hu0 hI t ht => key N x hx u hu hu0 hI t ht ?_⟩
  have : 1 ≤ N * h := by rwa [div_le_iff₀ hh] at hN
  linarith [ht.2, hx.2]

end Involution

end
