module

public import Involution.Setup.LinearCauchyOperator

/-! Ряд Пикара `Ψ(λ) = ∑ₖ (K₀ + λ K₁)ᵏ 1`: сходимость, целость по `λ`, интегральное
уравнение `Ψ = 1 + (K₀ + λ K₁) Ψ`. -/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Involution
namespace LinearCauchy

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

/-- Оператор `K_a : f ↦ ∫₀ˣ a f`. -/
def mulVolterra (a : C(Icc (0 : ℝ) 1, 𝔸)) : C(Icc (0 : ℝ) 1, 𝔸) →L[ℂ] C(Icc (0 : ℝ) 1, 𝔸) :=
  volterra.comp (ContinuousLinearMap.mul ℂ C(Icc (0 : ℝ) 1, 𝔸) a)

/-- `K_λ = K_{a₀} + λ K_{a₁}`. -/
def Kop (a₀ a₁ : C(Icc (0 : ℝ) 1, 𝔸)) (l : ℂ) :
    C(Icc (0 : ℝ) 1, 𝔸) →L[ℂ] C(Icc (0 : ℝ) 1, 𝔸) :=
  mulVolterra a₀ + l • mulVolterra a₁

omit [CompleteSpace 𝔸] in
lemma Kop_apply (a₀ a₁ : C(Icc (0 : ℝ) 1, 𝔸)) (l : ℂ) (f : C(Icc (0 : ℝ) 1, 𝔸))
    (x : Icc (0 : ℝ) 1) :
    Kop a₀ a₁ l f x = ∫ t in (0 : ℝ)..x, (ext a₀ t + l • ext a₁ t) * ext f t := by
  have h : ∀ t, ext ((a₀ + l • a₁) * f) t = (ext a₀ t + l • ext a₁ t) * ext f t := fun t => rfl
  have h2 : Kop a₀ a₁ l f = volterra ((a₀ + l • a₁) * f) := by
    simp [Kop, mulVolterra, add_mul]
  rw [h2, volterra_apply]
  simp only [h]

omit [CompleteSpace 𝔸] in
/-- Оценка итераций: `‖(K_λ)ᵏ f (x)‖ ≤ ‖f‖ (M x)ᵏ / k!`. -/
lemma norm_Kop_pow_le (a₀ a₁ : C(Icc (0 : ℝ) 1, 𝔸)) (l : ℂ) {M : ℝ}
    (hM : ‖a₀‖ + ‖l‖ * ‖a₁‖ ≤ M) (k : ℕ) (f : C(Icc (0 : ℝ) 1, 𝔸)) (x : Icc (0 : ℝ) 1) :
    ‖((Kop a₀ a₁ l) ^ k) f x‖ ≤ ‖f‖ * (M * x) ^ k / k.factorial := by
  induction k generalizing x with
  | zero => simpa using f.norm_coe_le_norm x
  | succ k ih =>
    rw [pow_succ']
    change ‖Kop a₀ a₁ l (((Kop a₀ a₁ l) ^ k) f) x‖ ≤ _
    rw [Kop_apply]
    have hx := x.2
    have hb : ∀ t ∈ Icc (0 : ℝ) x, ‖(ext a₀ t + l • ext a₁ t) * ext (((Kop a₀ a₁ l) ^ k) f) t‖
        ≤ (M * ‖f‖) * (M * t) ^ k / k.factorial := by
      intro t ht
      have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hx.2⟩
      rw [ext_of_mem (((Kop a₀ a₁ l) ^ k) f) ht1]
      have h1 := ih ⟨t, ht1⟩
      have h2 : ‖ext a₀ t + l • ext a₁ t‖ ≤ M := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul]
        nlinarith [norm_ext_le a₀ t, norm_ext_le a₁ t, norm_nonneg l, norm_nonneg (ext a₁ t),
          norm_nonneg a₁]
      calc _ ≤ ‖ext a₀ t + l • ext a₁ t‖ * ‖((Kop a₀ a₁ l) ^ k) f ⟨t, ht1⟩‖ :=
            norm_mul_le _ _
        _ ≤ M * (‖f‖ * (M * t) ^ k / k.factorial) :=
            mul_le_mul h2 h1 (norm_nonneg _) ((norm_nonneg _).trans h2)
        _ = (M * ‖f‖) * (M * t) ^ k / k.factorial := by ring
    have := norm_integral_le_poly (V := 𝔸) (M := M) (k := k) (C := M * ‖f‖) hx.1 hb
    refine this.trans (le_of_eq ?_)
    rw [Nat.factorial_succ]
    push_cast
    have : (k.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-- Сумма ряда Пикара. -/
def psi (a₀ a₁ : C(Icc (0 : ℝ) 1, 𝔸)) (l : ℂ) : C(Icc (0 : ℝ) 1, 𝔸) :=
  ∑' k : ℕ, ((Kop a₀ a₁ l) ^ k) 1

omit [CompleteSpace 𝔸] in
lemma norm_Kop_pow_one_le (a₀ a₁ : C(Icc (0 : ℝ) 1, 𝔸)) (l : ℂ) {M : ℝ}
    (hM : ‖a₀‖ + ‖l‖ * ‖a₁‖ ≤ M) (k : ℕ) :
    ‖((Kop a₀ a₁ l) ^ k) 1‖ ≤ ‖(1 : C(Icc (0 : ℝ) 1, 𝔸))‖ * M ^ k / k.factorial := by
  have hM0 : 0 ≤ M := (add_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _)
    (norm_nonneg _))).trans hM
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro x
  refine (norm_Kop_pow_le a₀ a₁ l hM k 1 x).trans ?_
  have hx := x.2
  have : (M * x) ^ k ≤ M ^ k := by
    rw [mul_pow]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ hx.1 hx.2)
  gcongr

lemma summable_Kop_pow (a₀ a₁ : C(Icc (0 : ℝ) 1, 𝔸)) (l : ℂ) :
    Summable fun k : ℕ => ((Kop a₀ a₁ l) ^ k) 1 := by
  refine Summable.of_norm_bounded
    ((Real.summable_pow_div_factorial (‖a₀‖ + ‖l‖ * ‖a₁‖)).mul_left
      ‖(1 : C(Icc (0 : ℝ) 1, 𝔸))‖) (fun k => ?_)
  have := norm_Kop_pow_one_le a₀ a₁ l le_rfl k
  rwa [mul_div_assoc] at this

omit [CompleteSpace 𝔸] in
lemma differentiable_Kop (a₀ a₁ : C(Icc (0 : ℝ) 1, 𝔸)) :
    Differentiable ℂ (Kop a₀ a₁) := by
  unfold Kop
  fun_prop

omit [CompleteSpace 𝔸] in
lemma differentiable_Kop_pow (a₀ a₁ : C(Icc (0 : ℝ) 1, 𝔸)) (k : ℕ) :
    Differentiable ℂ fun l => ((Kop a₀ a₁ l) ^ k) 1 := by
  have h : Differentiable ℂ fun l => (Kop a₀ a₁ l) ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      simp only [pow_succ]
      exact ih.mul (differentiable_Kop a₀ a₁)
  exact h.clm_apply (differentiable_const _)

/-- Целость суммы ряда Пикара по параметру. -/
theorem differentiable_psi (a₀ a₁ : C(Icc (0 : ℝ) 1, 𝔸)) :
    Differentiable ℂ (psi a₀ a₁) := by
  intro l
  set R : ℝ := ‖l‖ + 1 with hR
  have hU : DifferentiableOn ℂ (fun w => ∑' k : ℕ, ((Kop a₀ a₁ w) ^ k) 1) (Metric.ball 0 R) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := fun k : ℕ => ‖(1 : C(Icc (0 : ℝ) 1, 𝔸))‖ * ((‖a₀‖ + R * ‖a₁‖) ^ k / k.factorial))
      ((Real.summable_pow_div_factorial _).mul_left _)
      (fun k => (differentiable_Kop_pow a₀ a₁ k).differentiableOn) Metric.isOpen_ball
      (fun k w hw => ?_)
    have hw' : ‖w‖ ≤ R := by simpa using hw.out.le
    have := norm_Kop_pow_one_le a₀ a₁ w (M := ‖a₀‖ + R * ‖a₁‖)
      (by gcongr) k
    rwa [mul_div_assoc] at this
  have hmem : Metric.ball (0 : ℂ) R ∈ nhds l := Metric.isOpen_ball.mem_nhds (by
    simp [hR])
  exact (hU.differentiableAt hmem)

/-- Целость значений: `λ ↦ φ (Ψ(λ)(x))` для непрерывного линейного `φ`. -/
theorem differentiable_psi_apply (a₀ a₁ : C(Icc (0 : ℝ) 1, 𝔸)) {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℂ G] (φ : 𝔸 →L[ℂ] G) (x : Icc (0 : ℝ) 1) :
    Differentiable ℂ fun l => φ (psi a₀ a₁ l x) := by
  let hev := φ.comp (ContinuousMap.evalCLM ℂ x)
  have e : (fun l => φ (psi a₀ a₁ l x)) = ⇑hev ∘ psi a₀ a₁ := by
    ext l; rfl
  rw [e]
  exact hev.differentiable.comp (differentiable_psi a₀ a₁)

/-- Интегральное уравнение `Ψ = 1 + K_λ Ψ`. -/
theorem psi_eq (a₀ a₁ : C(Icc (0 : ℝ) 1, 𝔸)) (l : ℂ) :
    psi a₀ a₁ l = 1 + Kop a₀ a₁ l (psi a₀ a₁ l) := by
  have hs := summable_Kop_pow a₀ a₁ l
  have h1 : psi a₀ a₁ l = ((Kop a₀ a₁ l) ^ 0) 1 + ∑' k : ℕ, ((Kop a₀ a₁ l) ^ (k + 1)) 1 :=
    hs.tsum_eq_zero_add
  have h2 : Kop a₀ a₁ l (psi a₀ a₁ l) = ∑' k : ℕ, ((Kop a₀ a₁ l) ^ (k + 1)) 1 := by
    unfold psi
    rw [(Kop a₀ a₁ l).map_tsum hs]
    congr 1
    ext1 k
    rw [pow_succ']
    rfl
  rw [h2]
  simpa using h1

/-- Значение интегрального уравнения в точке отрезка. -/
theorem psi_apply (a₀ a₁ : C(Icc (0 : ℝ) 1, 𝔸)) (l : ℂ) (x : Icc (0 : ℝ) 1) :
    psi a₀ a₁ l x
      = 1 + ∫ t in (0 : ℝ)..x, (ext a₀ t + l • ext a₁ t) * ext (psi a₀ a₁ l) t := by
  conv_lhs => rw [psi_eq a₀ a₁ l]
  rw [ContinuousMap.add_apply, Kop_apply]
  rfl

end LinearCauchy
end Involution

end
