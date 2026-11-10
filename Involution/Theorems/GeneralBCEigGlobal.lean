module

public import Involution.Theorems.GeneralBCEigWindow
public import Involution.Theorems.GeneralBCEigLevels

/-! # Глобальная разметка нулей по слоям (пакет G6, thm:eig (b))

Слои `(b n, b (n+1)]` с хорошими радиусами `b n` и масштабами `e n → 0`; метка нуля —
пара (номер слоя, класс в слое). В каждом блоке поровну нулей `F` и `F + η` с кратностями,
а нули одного блока, достаточно далёкие, отстоят меньше чем на заданное `ε'`. -/

@[expose] public noncomputable section

open Set

namespace Involution
namespace GeneralBC

variable {F η : ℂ → ℂ} {L : ℝ}

theorem GoodRad.mono {ε ε' b : ℝ} (h : GoodRad F ε b) (hle : ε' ≤ ε) : GoodRad F ε' b :=
  fun z hz hre => le_trans (by linarith) (h z hz hre)

theorem global_labels (hP : PlanarData F η L) (Bf : ℝ → ℝ) :
    ∃ (b₀ ε₀' : ℝ) (πF πΨ : ℂ → ℕ × Finset ℂ), 0 ≤ b₀ ∧ Bf ε₀' ≤ b₀ ∧ 0 < ε₀' ∧ ε₀' ≤ 1 / 8 ∧
      GoodRad F ε₀' b₀ ∧
      (∀ τ, {x | πF x = τ ∧ b₀ < ‖x‖ ∧ 0 < x.re ∧ mult F x ≠ 0}.Finite) ∧
      (∀ τ, {x | πΨ x = τ ∧ b₀ < ‖x‖ ∧ 0 < x.re ∧ mult (fun w => F w + η w) x ≠ 0}.Finite) ∧
      (∀ τ, ∑ᶠ x ∈ {x | πF x = τ ∧ b₀ < ‖x‖ ∧ 0 < x.re}, mult F x =
        ∑ᶠ x ∈ {x | πΨ x = τ ∧ b₀ < ‖x‖ ∧ 0 < x.re}, mult (fun w => F w + η w) x) ∧
      (∀ ε' > 0, ∃ R' : ℝ, ∀ x y : ℂ, b₀ < ‖x‖ → 0 < x.re → b₀ < ‖y‖ → 0 < y.re →
        mult F y ≠ 0 → mult (fun w => F w + η w) x ≠ 0 → R' ≤ ‖x‖ → πF y = πΨ x →
        ‖x - y‖ < ε') ∧
      (∀ R : ℝ, {x | b₀ < ‖x‖ ∧ 0 < x.re ∧ mult (fun w => F w + η w) x ≠ 0 ∧ ‖x‖ ≤ R}.Finite) := by
  classical
  obtain ⟨ε₀, hε₀, hw⟩ := window_lemma hP
  obtain ⟨K₁, hK₁⟩ := exists_good_radius hP
  set ε₁ : ℝ := min ε₀ (1 / (8 * ((K₁ : ℝ) + 1))) with hε₁
  have hKpos : (0 : ℝ) < 8 * ((K₁ : ℝ) + 1) := by positivity
  have hε₁pos : 0 < ε₁ := lt_min hε₀ (by positivity)
  have hε₁a : ε₁ ≤ ε₀ := min_le_left _ _
  have hε₁b : ε₁ ≤ 1 / (8 * ((K₁ : ℝ) + 1)) := min_le_right _ _
  have hε₁c : ε₁ ≤ 1 / 8 := by
    refine hε₁b.trans ?_
    rw [div_le_div_iff₀ hKpos (by norm_num)]
    have : (0 : ℝ) ≤ K₁ := Nat.cast_nonneg K₁
    nlinarith
  choose! Tf hTf using hw
  obtain ⟨N, e, hN0, he, hanti, hlim, hTe'⟩ :=
    exists_levels (fun ε => max (Tf ε) (Bf ε)) hε₁pos 0
  have hTe : ∀ n : ℕ, Tf (e n) ≤ N + n := fun n => (le_max_left _ _).trans (hTe' n)
  have hb : ∀ n : ℕ, ∃ b ∈ Ico (N + n) (N + n + 1), GoodRad F (e (n - 1)) b := by
    intro n
    refine hK₁ (e (n - 1)) (N + n) (he _).1 ?_ ?_
    · have h1 := (he (n - 1)).2.trans hε₁b
      have h2 : 4 * e (n - 1) * K₁ ≤ 4 * (1 / (8 * ((K₁ : ℝ) + 1))) * K₁ := by
        have : (0 : ℝ) ≤ K₁ := Nat.cast_nonneg K₁
        nlinarith [(he (n - 1)).1]
      refine lt_of_le_of_lt h2 ?_
      rw [show 4 * (1 / (8 * ((K₁ : ℝ) + 1))) * K₁ = K₁ / (2 * ((K₁ : ℝ) + 1)) by
        field_simp; ring]
      rw [div_lt_one (by positivity)]
      linarith [(Nat.cast_nonneg K₁ : (0 : ℝ) ≤ K₁)]
    · linarith [(he (n - 1)).2, hε₁c]
  choose b hbI hbG using hb
  have hbmono : ∀ n, b n < b (n + 1) := fun n => by
    have h1 := (hbI n).2
    have h2 := (hbI (n + 1)).1
    push_cast at h2
    linarith
  have hbstep : ∀ n, b (n + 1) ≤ b n + 2 := fun n => by
    have h1 := (hbI n).1
    have h2 := (hbI (n + 1)).2
    push_cast at h2
    linarith
  have hbmono' : Monotone b := monotone_nat_of_le_succ (fun n => (hbmono n).le)
  have hbN : ∀ n : ℕ, N + n ≤ b n := fun n => (hbI n).1
  have hshell : ∀ n : ℕ, ∃ lF lΨ : ℂ → Finset ℂ,
      (∀ t, {x | lF x = t ∧ InWin (b n) (b (n + 1)) x ∧ mult F x ≠ 0}.Finite) ∧
      (∀ t, {x | lΨ x = t ∧ InWin (b n) (b (n + 1)) x ∧
        mult (fun w => F w + η w) x ≠ 0}.Finite) ∧
      (∀ t, ∑ᶠ x ∈ {x | lF x = t ∧ InWin (b n) (b (n + 1)) x}, mult F x =
        ∑ᶠ x ∈ {x | lΨ x = t ∧ InWin (b n) (b (n + 1)) x}, mult (fun w => F w + η w) x) ∧
      (∀ x y, InWin (b n) (b (n + 1)) x → InWin (b n) (b (n + 1)) y → mult F x ≠ 0 →
        mult (fun w => F w + η w) y ≠ 0 → lF x = lΨ y → ‖x - y‖ < 2 * e n) ∧
      {y | InWin (b n) (b (n + 1)) y ∧ mult (fun w => F w + η w) y ≠ 0}.Finite := by
    intro n
    refine hTf (e n) (he n).1 ((he n).2.trans hε₁a) (b n) (b (n + 1)) ?_ (hbmono n) (hbstep n)
      ?_ ?_
    · exact (hTe n).trans (hbN n)
    · refine (hbG n).mono ?_
      exact hanti (Nat.sub_le n 1)
    · have := hbG (n + 1)
      simpa using this
  choose lF lΨ h1 h2 h3 h4 h5 using hshell
  -- номер слоя
  have hex : ∀ x : ℂ, ∃ n : ℕ, ‖x‖ ≤ b (n + 1) := by
    intro x
    refine ⟨⌈‖x‖⌉₊, ?_⟩
    have := hbN (⌈‖x‖⌉₊ + 1)
    push_cast at this
    have := Nat.le_ceil ‖x‖
    linarith
  let nn : ℂ → ℕ := fun x => Nat.find (hex x)
  have shell_iff : ∀ x : ℂ, b 0 < ‖x‖ → ∀ n, (b n < ‖x‖ ∧ ‖x‖ ≤ b (n + 1)) ↔ n = nn x := by
    intro x hx n
    have hspec : ‖x‖ ≤ b (nn x + 1) := Nat.find_spec (hex x)
    constructor
    · rintro ⟨h1, h2⟩
      have hle : nn x ≤ n := Nat.find_min' (hex x) h2
      by_contra hne
      have hlt : nn x < n := lt_of_le_of_ne hle (Ne.symm hne)
      have := hbmono' (show nn x + 1 ≤ n from hlt)
      linarith
    · rintro rfl
      refine ⟨?_, hspec⟩
      rcases Nat.eq_zero_or_pos (nn x) with h0 | hpos
      · rw [h0]; exact hx
      · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
        have := Nat.find_min (hex x) (show k < nn x by omega)
        rw [hk]
        exact not_le.1 this
  have hFib : ∀ (lab : ℕ → ℂ → Finset ℂ) (n : ℕ) (t : Finset ℂ),
      {x : ℂ | (nn x, lab (nn x) x) = (n, t) ∧ b 0 < ‖x‖ ∧ 0 < x.re} =
        {x | lab n x = t ∧ InWin (b n) (b (n + 1)) x} := by
    intro lab n t
    ext x
    simp only [mem_ofPred_eq, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hn, hl⟩, hb0, hre⟩
      subst hn
      exact ⟨hl, ((shell_iff x hb0 (nn x)).2 rfl).1, ((shell_iff x hb0 (nn x)).2 rfl).2, hre⟩
    · rintro ⟨hl, hw1, hw2, hre⟩
      have hb0 : b 0 < ‖x‖ := lt_of_le_of_lt (hbmono' (Nat.zero_le n)) hw1
      have hn : n = nn x := (shell_iff x hb0 n).1 ⟨hw1, hw2⟩
      subst hn
      exact ⟨⟨rfl, hl⟩, hb0, hre⟩
  refine ⟨b 0, e 0, fun x => (nn x, lF (nn x) x), fun x => (nn x, lΨ (nn x) x),
    le_trans hN0 (by simpa using hbN 0),
    ((le_max_right _ _).trans (hTe' 0)).trans (by simpa using hbN 0), (he 0).1,
    (he 0).2.trans hε₁c, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hbG 0
  · rintro ⟨n, t⟩
    refine (h1 n t).subset (fun x hx => ?_)
    obtain ⟨hπ, hb0, hre, hm⟩ := hx
    have := (Set.ext_iff.1 (hFib lF n t) x).1 ⟨hπ, hb0, hre⟩
    exact ⟨this.1, this.2, hm⟩
  · rintro ⟨n, t⟩
    refine (h2 n t).subset (fun x hx => ?_)
    obtain ⟨hπ, hb0, hre, hm⟩ := hx
    have := (Set.ext_iff.1 (hFib lΨ n t) x).1 ⟨hπ, hb0, hre⟩
    exact ⟨this.1, this.2, hm⟩
  · rintro ⟨n, t⟩
    change ∑ᶠ x ∈ {x : ℂ | (nn x, lF (nn x) x) = (n, t) ∧ b 0 < ‖x‖ ∧ 0 < x.re}, mult F x =
      ∑ᶠ x ∈ {x : ℂ | (nn x, lΨ (nn x) x) = (n, t) ∧ b 0 < ‖x‖ ∧ 0 < x.re},
        mult (fun w => F w + η w) x
    rw [hFib lF n t, hFib lΨ n t]
    exact h3 n t
  · intro ε' hε'
    obtain ⟨n₀, hn₀⟩ := hlim (ε' / 2) (by positivity)
    refine ⟨b n₀ + 1, fun x y hbx hrx hby hry hmy hmx hR hlab => ?_⟩
    change (nn y, lF (nn y) y) = (nn x, lΨ (nn x) x) at hlab
    rw [Prod.mk.injEq] at hlab
    obtain ⟨hn, hl⟩ := hlab
    have hx1 := (shell_iff x hbx (nn x)).2 rfl
    have hy1 := (shell_iff y hby (nn y)).2 rfl
    have hn₀le : n₀ ≤ nn x := by
      by_contra hlt
      rw [not_le] at hlt
      have := hbmono' (show nn x + 1 ≤ n₀ by omega)
      linarith [hx1.2]
    have hcl := h4 (nn x) y x (by rw [← hn]; exact ⟨hy1.1, hy1.2, hry⟩)
      ⟨hx1.1, hx1.2, hrx⟩ hmy hmx (by rw [← hn] at *; simpa [hn] using hl)
    have := hn₀ (nn x) hn₀le
    rw [norm_sub_rev] at hcl
    linarith
  · intro R
    refine Set.Finite.subset ((Finset.range (⌈R⌉₊ + 1)).finite_toSet.biUnion
      (fun n _ => h5 n)) (fun x hx => ?_)
    obtain ⟨hb0, hre, hm, hR⟩ := hx
    have hx1 := (shell_iff x hb0 (nn x)).2 rfl
    simp only [Finset.coe_range, mem_Iio, mem_iUnion]
    refine ⟨nn x, ?_, ⟨hx1.1, hx1.2, hre⟩, hm⟩
    by_contra hge
    rw [not_lt] at hge
    have h6 := hbmono' hge
    have h7 := hbN (⌈R⌉₊ + 1)
    push_cast at h7
    have := Nat.le_ceil R
    linarith [hx1.1]

end GeneralBC
end Involution
