module

public import Involution.Theorems.GeneralBCEigPlanar
public import Involution.Theorems.GeneralBCEigIsolate

/-! # Сопоставление нулей в кольце: кластеры и теорема Руше (пакет G6, thm:eig (b))

В кольце `R < ‖z‖ ≤ R'` правой полуплоскости (ширины не больше 2, границы — хорошие радиусы)
нули `F` разбиты на классы `cl x`, а нули `F + η` приписаны тем же классам; в каждом классе
поровну нулей с кратностями, а элементы одного класса отстоят друг от друга меньше чем на `2ε`. -/

@[expose] public noncomputable section

open Set Metric

namespace Involution
namespace GeneralBC

variable {F η : ℂ → ℂ} {L : ℝ}

/-- Класс точки `a ∈ A` на масштабе `d₁`. -/
def cl (A : Finset ℂ) (d₁ : ℝ) (a : ℂ) : Finset ℂ := by
  classical exact A.filter (fun z => ‖z - a‖ < d₁)

theorem mem_cl {A : Finset ℂ} {d₁ : ℝ} {a z : ℂ} : z ∈ cl A d₁ a ↔ z ∈ A ∧ ‖z - a‖ < d₁ := by
  classical simp [cl]

theorem cl_eq_of_mem {A : Finset ℂ} {d₀ d₁ : ℝ} (h2 : 2 * d₁ ≤ d₀)
    (hiso : ∀ a ∈ A, ∀ a' ∈ A, ¬ (d₁ ≤ ‖a - a'‖ ∧ ‖a - a'‖ < d₀)) {a a' : ℂ} (ha : a ∈ A)
    (ha' : a' ∈ A) (h : ‖a' - a‖ < d₁) : cl A d₁ a' = cl A d₁ a := by
  ext z
  rw [mem_cl, mem_cl]
  constructor
  · rintro ⟨hz, h1⟩
    refine ⟨hz, ?_⟩
    by_contra hge
    rw [not_lt] at hge
    refine hiso z hz a ha ⟨hge, ?_⟩
    have := norm_sub_le_norm_sub_add_norm_sub z a' a
    linarith
  · rintro ⟨hz, h1⟩
    refine ⟨hz, ?_⟩
    by_contra hge
    rw [not_lt] at hge
    refine hiso z hz a' ha' ⟨hge, ?_⟩
    have := norm_sub_le_norm_sub_add_norm_sub z a a'
    rw [norm_sub_rev a a'] at this
    linarith

theorem iso_dich {A : Finset ℂ} {d₀ d₁ : ℝ}
    (hiso : ∀ a ∈ A, ∀ a' ∈ A, ¬ (d₁ ≤ ‖a - a'‖ ∧ ‖a - a'‖ < d₀)) {x z : ℂ} (hx : x ∈ A)
    (hz : z ∈ A) : ‖z - x‖ < d₁ ∨ d₀ ≤ ‖z - x‖ := by
  by_contra h
  rw [not_or, not_lt, not_le] at h
  exact hiso z hz x hx h

/-- Точка кольца `R < ‖x‖ ≤ R'` правой полуплоскости. -/
def InWin (R R' : ℝ) (x : ℂ) : Prop := R < ‖x‖ ∧ ‖x‖ ≤ R' ∧ 0 < x.re

theorem window_lemma (hP : PlanarData F η L) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ T : ℝ, ∀ R R' : ℝ, T ≤ R → R < R' →
      R' ≤ R + 2 → GoodRad F ε R → GoodRad F ε R' →
      ∃ lF lΨ : ℂ → Finset ℂ,
        (∀ t, {x | lF x = t ∧ InWin R R' x ∧ mult F x ≠ 0}.Finite) ∧
        (∀ t, {x | lΨ x = t ∧ InWin R R' x ∧ mult (fun w => F w + η w) x ≠ 0}.Finite) ∧
        (∀ t, ∑ᶠ x ∈ {x | lF x = t ∧ InWin R R' x}, mult F x =
          ∑ᶠ x ∈ {x | lΨ x = t ∧ InWin R R' x}, mult (fun w => F w + η w) x) ∧
        (∀ x y, InWin R R' x → InWin R R' y → mult F x ≠ 0 →
          mult (fun w => F w + η w) y ≠ 0 → lF x = lΨ y → ‖x - y‖ < 2 * ε) ∧
        {y | InWin R R' y ∧ mult (fun w => F w + η w) y ≠ 0}.Finite := by
  classical
  obtain ⟨h₀, N₀, hstrip, -⟩ := hP.count
  obtain ⟨K, hK⟩ := window_card hP
  refine ⟨1 / 2, by norm_num, fun ε hε hε2 => ?_⟩
  set δL : ℝ := ε / 4 ^ (K * K + 1) with hδL
  have hδL0 : 0 < δL := by positivity
  obtain ⟨rL, hrL⟩ := near_zero hP hδL0
  obtain ⟨rR, hrR⟩ := rouche_disc hP hδL0
  refine ⟨max (max rL rR) 0 + |h₀| + 2, fun R R' hT hRR' hR2 hgR hgR' => ?_⟩
  have hM1 := le_max_left rL rR
  have hM2 := le_max_right rL rR
  have hM3 := le_max_left (max rL rR) 0
  have hM4 := le_max_right (max rL rR) 0
  have hh0 := abs_nonneg h₀
  have hRrL : rL + |h₀| + 2 ≤ R := by linarith
  have hRrR : rR + |h₀| + 2 ≤ R := by linarith
  set Ψ : ℂ → ℂ := fun w => F w + η w with hΨdef
  -- множество `A` нулей в окне
  have hrz : {z : ℂ | F z = 0 ∧ InWin R R' z} ⊆ rz F R := fun z hz =>
    ⟨hz.1, hz.2.2.2, hz.2.1, by linarith [hz.2.2.1]⟩
  obtain ⟨hfinR, hcardR⟩ := hK R
  have hAfin : {z : ℂ | F z = 0 ∧ InWin R R' z}.Finite := hfinR.subset hrz
  set A : Finset ℂ := hAfin.toFinset with hAdef
  have hmemA : ∀ z, z ∈ A ↔ F z = 0 ∧ InWin R R' z := fun z => by simp [hAdef]
  have hAcard : A.card ≤ K := by
    have h1 := Set.ncard_le_ncard hrz hfinR
    have h2 : A.card = {z : ℂ | F z = 0 ∧ InWin R R' z}.ncard := by
      rw [← Set.ncard_coe_finset, hAdef, hAfin.coe_toFinset]
    omega
  obtain ⟨i, hi, hiso⟩ := exists_isolating_scale A K hAcard ε hε
  set d₀ : ℝ := ε / 4 ^ i with hd₀
  set d₁ : ℝ := ε / 4 ^ (i + 1) with hd₁
  have hd₀pos : 0 < d₀ := by positivity
  have hd₁eq : d₁ = d₀ / 4 := by
    rw [hd₀, hd₁, pow_succ]; field_simp
  have hd₀le : d₀ ≤ ε := by
    rw [hd₀]; exact div_le_self hε.le (one_le_pow₀ (by norm_num))
  have hδLd₁ : δL ≤ d₁ := by
    rw [hδL, hd₁]
    exact div_le_div_of_nonneg_left hε.le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by omega))
  have h2d : 2 * d₁ ≤ d₀ := by rw [hd₁eq]; linarith
  set s : ℝ := (d₀ + d₁) / 2 with hs
  have hspos : 0 < s := by rw [hs, hd₁eq]; linarith
  -- свойства точек `A`
  have hxA : ∀ x ∈ A, F x = 0 ∧ R + 2 * ε ≤ ‖x‖ ∧ ‖x‖ ≤ R' - 2 * ε ∧ 2 ≤ x.re ∧ 0 < x.re := by
    intro x hx
    obtain ⟨hF, h1, h2, h3⟩ := (hmemA x).1 hx
    have g1 := hgR x hF h3
    have g2 := hgR' x hF h3
    rw [abs_of_pos (by linarith)] at g1
    have g2' : 2 * ε ≤ R' - ‖x‖ := by
      rcases le_abs'.1 g2 with h | h <;> linarith
    have hn : ‖x‖ ≤ |x.re| + |x.im| := Complex.norm_le_abs_re_add_abs_im x
    rw [abs_of_pos h3] at hn
    have him := hstrip x hF
    refine ⟨hF, by linarith, by linarith, ?_, h3⟩
    have : |h₀| ≥ h₀ := le_abs_self h₀
    linarith
  -- нуль вне `A` далёк от точки `A`
  have outA : ∀ x ∈ A, ∀ z, F z = 0 → z ∉ A → d₀ ≤ ‖z - x‖ := by
    intro x hx z hz hzA
    obtain ⟨hFx, hx1, hx2, hx3, hx4⟩ := hxA x hx
    by_cases hre : 0 < z.re
    · have g1 := hgR z hz hre
      have g2 := hgR' z hz hre
      have hnot : ¬ (R < ‖z‖ ∧ ‖z‖ ≤ R') := fun h => hzA ((hmemA z).2 ⟨hz, h.1, h.2, hre⟩)
      have hnrm := norm_sub_norm_le x z
      rw [norm_sub_rev] at hnrm
      by_cases hc : ‖z‖ ≤ R
      · rw [abs_of_nonpos (by linarith)] at g1
        linarith
      · have hc' : R' < ‖z‖ := by
          by_contra hh
          exact hnot ⟨lt_of_not_ge hc, not_lt.1 hh⟩
        rw [abs_of_pos (by linarith)] at g2
        have := norm_sub_norm_le z x
        linarith
    · have h1 : |(z - x).re| ≤ ‖z - x‖ := Complex.abs_re_le_norm _
      have h2 : (z - x).re = z.re - x.re := by simp
      rw [h2] at h1
      have := neg_le_abs (z.re - x.re)
      push Not at hre
      linarith
  have dich : ∀ x ∈ A, ∀ z, F z = 0 → ‖z - x‖ < d₁ ∨ d₀ ≤ ‖z - x‖ := by
    intro x hx z hz
    by_cases hzA : z ∈ A
    · exact iso_dich hiso hx hzA
    · exact Or.inr (outA x hx z hz hzA)
  have hsd : s < d₀ := by rw [hs, hd₁eq]; linarith
  have hd₁s : d₁ < s := by rw [hs, hd₁eq]; linarith
  have hsε : s ≤ ε := by linarith
  have hxr : ∀ x ∈ A, rR + s ≤ ‖x‖ := by
    intro x hx
    obtain ⟨-, h1, -, -, -⟩ := hxA x hx
    linarith
  have rc : ∀ x ∈ A, zeroCount F x s = zeroCount Ψ x s ∧
      (ball x s ∩ Function.support (zeroMult Ψ)).Finite := by
    intro x hx
    refine hrR x s hspos (hxr x hx) (fun z hz => ?_)
    rcases dich x hx z hz with h | h
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_nonneg (by linarith)]
      linarith
  have zball : ∀ x ∈ A, ∀ z, F z = 0 → (z ∈ ball x s ↔ z ∈ cl A d₁ x) := by
    intro x hx z hz
    rw [mem_cl, mem_ball, dist_eq_norm]
    constructor
    · intro h
      have hzA : z ∈ A := by
        by_contra hzA
        have := outA x hx z hz hzA
        linarith
      refine ⟨hzA, ?_⟩
      rcases dich x hx z hz with h1 | h1
      · exact h1
      · linarith
    · rintro ⟨-, h⟩; linarith
  have hΨan : ∀ y : ℂ, 0 < y.re → AnalyticAt ℂ Ψ y := by
    intro y hy
    have hy0 : y ≠ 0 := fun h => by rw [h] at hy; simp at hy
    have h2 : AnalyticAt ℂ η y :=
      hP.eta_diff.analyticAt (isOpen_compl_singleton.mem_nhds (by simpa using hy0))
    exact (hP.entire.analyticAt y).add h2
  let aa : ℂ → ℂ := fun y => if h : ∃ z, F z = 0 ∧ ‖y - z‖ < δL then h.choose else 0
  have aa_spec : ∀ y, (∃ z, F z = 0 ∧ ‖y - z‖ < δL) → F (aa y) = 0 ∧ ‖y - aa y‖ < δL := by
    intro y h
    simp only [aa, h, ↓reduceDIte]
    exact h.choose_spec
  have hΨy : ∀ y, InWin R R' y → mult Ψ y ≠ 0 → F (aa y) = 0 ∧ ‖y - aa y‖ < δL ∧ Ψ y = 0 := by
    intro y hy hm
    have h0 := eq_zero_of_mult_ne_zero (hΨan y hy.2.2) hm
    have hnr : rL ≤ ‖y‖ := by have := hy.1; linarith
    obtain ⟨z, hz, hzd⟩ := hrL y hnr h0
    obtain ⟨h1, h2⟩ := aa_spec y ⟨z, hz, hzd⟩
    exact ⟨h1, h2, h0⟩
  have hδLε : δL ≤ ε := by linarith
  have aa_mem : ∀ y, InWin R R' y → mult Ψ y ≠ 0 → aa y ∈ A := by
    intro y hy hm
    obtain ⟨hF, hd, -⟩ := hΨy y hy hm
    have hstr := hstrip _ hF
    rw [hmemA]
    refine ⟨hF, ?_⟩
    have hn1 : ‖y‖ - δL ≤ ‖aa y‖ := by
      have := norm_sub_norm_le y (aa y); linarith
    have hn2 : ‖aa y‖ ≤ ‖y‖ + δL := by
      have := norm_sub_norm_le (aa y) y
      rw [norm_sub_rev] at this; linarith
    have hre : 0 < (aa y).re := by
      have h1 : |(y - aa y).re| ≤ ‖y - aa y‖ := Complex.abs_re_le_norm _
      have h2 : (y - aa y).re = y.re - (aa y).re := by simp
      have hn : ‖aa y‖ ≤ |(aa y).re| + |(aa y).im| := Complex.norm_le_abs_re_add_abs_im _
      by_contra hneg
      rw [not_lt] at hneg
      rw [abs_of_nonpos hneg] at hn
      have h3 := le_abs_self h₀
      rw [h2] at h1
      have h4 := le_abs_self (y.re - (aa y).re)
      have := hy.2.2
      have := hy.1
      linarith
    have g1 := hgR (aa y) hF hre
    have g2 := hgR' (aa y) hF hre
    refine ⟨?_, ?_, hre⟩
    · by_contra hh
      rw [not_lt] at hh
      rw [abs_of_nonpos (by linarith)] at g1
      linarith [hy.1]
    · by_contra hh
      rw [not_le] at hh
      rw [abs_of_pos (by linarith)] at g2
      linarith [hy.2.1]
  let lF : ℂ → Finset ℂ := fun x => if x ∈ A then cl A d₁ x else ∅
  let lΨ : ℂ → Finset ℂ := fun y => lF (aa y)
  have lF_mem : ∀ x ∈ A, lF x = cl A d₁ x := fun x hx => by simp [lF, hx]
  have self_mem : ∀ x ∈ A, x ∈ cl A d₁ x := fun x hx => by
    rw [mem_cl]; refine ⟨hx, ?_⟩; simp only [sub_self, norm_zero]; rw [hd₁eq]; linarith
  have mF_A : ∀ w, InWin R R' w → mult F w ≠ 0 → w ∈ A := fun w hw hm =>
    (hmemA w).2 ⟨eq_zero_of_mult_ne_zero (hP.entire.analyticAt w) hm, hw⟩
  have fibF : ∀ x ∈ A, ∀ w, InWin R R' w → mult F w ≠ 0 →
      (lF w = cl A d₁ x ↔ w ∈ ball x s) := by
    intro x hx w hw hm
    have hwA := mF_A w hw hm
    have hF := ((hmemA w).1 hwA).1
    rw [lF_mem w hwA, zball x hx w hF]
    constructor
    · intro h; rw [← h]; exact self_mem w hwA
    · intro h; exact cl_eq_of_mem h2d hiso hx hwA ((mem_cl.1 h).2)
  have fibΨ : ∀ x ∈ A, ∀ y, InWin R R' y → mult Ψ y ≠ 0 →
      (lΨ y = cl A d₁ x ↔ y ∈ ball x s) := by
    intro x hx y hy hm
    obtain ⟨hF, hd, -⟩ := hΨy y hy hm
    have haA := aa_mem y hy hm
    change lF (aa y) = _ ↔ _
    rw [lF_mem _ haA, mem_ball, dist_eq_norm]
    constructor
    · intro h
      have : aa y ∈ cl A d₁ x := by rw [← h]; exact self_mem _ haA
      have h1 := (mem_cl.1 this).2
      have := norm_sub_le_norm_sub_add_norm_sub y (aa y) x
      linarith
    · intro h
      have h1 : ‖aa y - x‖ < d₁ := by
        rcases dich x hx (aa y) hF with h1 | h1
        · exact h1
        · exfalso
          have := norm_sub_le_norm_sub_add_norm_sub (aa y) y x
          rw [norm_sub_rev (aa y) y] at this
          linarith
      exact cl_eq_of_mem h2d hiso hx haA h1
  have ballΨ : ∀ x ∈ A, ∀ y, y ∈ ball x s → InWin R R' y := by
    intro x hx y hy
    obtain ⟨-, h1, h2, h3, -⟩ := hxA x hx
    rw [mem_ball, dist_eq_norm] at hy
    have e1 := norm_sub_norm_le y x
    have e2 := norm_sub_norm_le x y
    rw [norm_sub_rev] at e2
    have e3 : |(y - x).re| ≤ ‖y - x‖ := Complex.abs_re_le_norm _
    have e4 : (y - x).re = y.re - x.re := by simp
    rw [e4] at e3
    have e5 := neg_abs_le (y.re - x.re)
    refine ⟨by linarith, by linarith, by linarith⟩
  have supF : ∀ x ∈ A, {w | lF w = cl A d₁ x ∧ InWin R R' w} ∩ Function.support (mult F) =
      ball x s ∩ Function.support (mult F) := by
    intro x hx
    ext w
    simp only [mem_inter_iff, mem_ofPred_eq, Function.mem_support]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨(fibF x hx w h2 h3).1 h1, h3⟩
    · rintro ⟨h1, h3⟩
      have hF := eq_zero_of_mult_ne_zero (hP.entire.analyticAt w) h3
      have hwA : w ∈ A := (mem_cl.1 ((zball x hx w hF).1 h1)).1
      have h2 := ((hmemA w).1 hwA).2
      exact ⟨⟨(fibF x hx w h2 h3).2 h1, h2⟩, h3⟩
  have supΨ : ∀ x ∈ A, {w | lΨ w = cl A d₁ x ∧ InWin R R' w} ∩ Function.support (mult Ψ) =
      ball x s ∩ Function.support (mult Ψ) := by
    intro x hx
    ext w
    simp only [mem_inter_iff, mem_ofPred_eq, Function.mem_support]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨(fibΨ x hx w h2 h3).1 h1, h3⟩
    · rintro ⟨h1, h3⟩
      have h2 := ballΨ x hx w h1
      exact ⟨⟨(fibΨ x hx w h2 h3).2 h1, h2⟩, h3⟩
  have noclass : ∀ t, (¬ ∃ x ∈ A, t = cl A d₁ x) →
      {w | lF w = t ∧ InWin R R' w} ∩ Function.support (mult F) = ∅ ∧
      {w | lΨ w = t ∧ InWin R R' w} ∩ Function.support (mult Ψ) = ∅ := by
    intro t ht
    constructor
    · refine Set.eq_empty_of_forall_notMem (fun w hw => ?_)
      obtain ⟨⟨h1, h2⟩, h3⟩ := hw
      have h3' : mult F w ≠ 0 := h3
      exact ht ⟨w, mF_A w h2 h3', by rw [← h1, lF_mem _ (mF_A w h2 h3')]⟩
    · refine Set.eq_empty_of_forall_notMem (fun w hw => ?_)
      obtain ⟨⟨h1, h2⟩, h3⟩ := hw
      have h3' : mult Ψ w ≠ 0 := h3
      have haA := aa_mem w h2 h3'
      exact ht ⟨aa w, haA, by rw [← h1]; exact lF_mem _ haA⟩
  have congr_supp : ∀ {f : ℂ → ℕ} {S T : Set ℂ},
      S ∩ Function.support f = T ∩ Function.support f → ∑ᶠ x ∈ S, f x = ∑ᶠ x ∈ T, f x := by
    intro f S T h
    rw [← finsum_mem_inter_support f S, h, finsum_mem_inter_support]
  refine ⟨lF, lΨ, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    exact (A.finite_toSet).subset (fun x hx => mF_A x hx.2.1 hx.2.2)
  · intro t
    by_cases ht : ∃ x ∈ A, t = cl A d₁ x
    · obtain ⟨x, hx, rfl⟩ := ht
      refine ((rc x hx).2).subset (fun y hy => ?_)
      obtain ⟨h1, h2, h3⟩ := hy
      exact ⟨(fibΨ x hx y h2 h3).1 h1, h3⟩
    · have := (noclass t ht).2
      refine Set.Finite.subset (Set.finite_empty) (fun y hy => ?_)
      have h : y ∈ {w | lΨ w = t ∧ InWin R R' w} ∩ Function.support (mult Ψ) :=
        ⟨⟨hy.1, hy.2.1⟩, hy.2.2⟩
      rw [this] at h
      exact h
  · intro t
    by_cases ht : ∃ x ∈ A, t = cl A d₁ x
    · obtain ⟨x, hx, rfl⟩ := ht
      rw [congr_supp (supF x hx), congr_supp (supΨ x hx)]
      exact (rc x hx).1
    · obtain ⟨h1, h2⟩ := noclass t ht
      have e1 : ∑ᶠ x ∈ {w | lF w = t ∧ InWin R R' w}, mult F x = 0 := by
        rw [congr_supp (f := mult F) (S := {w | lF w = t ∧ InWin R R' w}) (T := ∅)
          (by rw [h1]; simp)]
        simp
      have e2 : ∑ᶠ x ∈ {w | lΨ w = t ∧ InWin R R' w}, mult Ψ x = 0 := by
        rw [congr_supp (f := mult Ψ) (S := {w | lΨ w = t ∧ InWin R R' w}) (T := ∅)
          (by rw [h2]; simp)]
        simp
      rw [e1, e2]
  · intro x y hx hy hmx hmy hl
    have hxA' := mF_A x hx hmx
    have haA := aa_mem y hy hmy
    obtain ⟨-, hd, -⟩ := hΨy y hy hmy
    have h1 : lF x = cl A d₁ x := lF_mem x hxA'
    have h2 : lΨ y = cl A d₁ (aa y) := lF_mem _ haA
    have : x ∈ cl A d₁ (aa y) := by
      rw [← h2, ← hl, h1]; exact self_mem x hxA'
    have h3 := (mem_cl.1 this).2
    have := norm_sub_le_norm_sub_add_norm_sub x (aa y) y
    rw [norm_sub_rev (aa y) y] at this
    linarith
  · refine (A.finite_toSet.biUnion (fun x hx => (rc x hx).2)).subset (fun y hy => ?_)
    obtain ⟨h1, h2⟩ := hy
    have haA := aa_mem y h1 h2
    obtain ⟨-, hd, -⟩ := hΨy y h1 h2
    simp only [mem_iUnion]
    refine ⟨aa y, haA, ?_, h2⟩
    rw [mem_ball, dist_eq_norm]
    linarith

end GeneralBC
end Involution
