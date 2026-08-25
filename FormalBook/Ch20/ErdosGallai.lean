import FormalBook.Mathlib.EdgeFinset
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

open Real
open BigOperators
open Classical

section ErdosGallai

open Finset

/-! ### Algebraic layer: HM-GM inequality -/

/-- The harmonic mean of two positive reals is at most their geometric mean.
    More precisely, if a, b > 0, then 2ab/(a+b) ≤ √(ab).
    Equivalently, 4a²b² ≤ ab(a+b)², which simplifies to 0 ≤ ab(a-b)². -/
theorem hm_le_gm (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    2 * a * b / (a + b) ≤ Real.sqrt (a * b) := by
  have hab : 0 < a + b := by linarith
  rw [div_le_iff₀ hab]
  have hsqa := Real.mul_self_sqrt ha.le
  have hsqb := Real.mul_self_sqrt hb.le
  have hsqab : Real.sqrt (a * b) * Real.sqrt (a * b) = a * b := Real.mul_self_sqrt (mul_nonneg ha.le hb.le)
  have hsqab' : Real.sqrt a * Real.sqrt b = Real.sqrt (a * b) := (Real.sqrt_mul ha.le b).symm
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg (a * b)]

/-- Product identity:
    ∏ᵢ (αᵢ - 1) · ∏ᵢ (αᵢ + 1) = ∏ᵢ (αᵢ² - 1). -/
theorem prod_sub_one_mul_prod_add_one {n : ℕ} (α : Fin n → ℝ) :
    (∏ i, (α i - 1)) * (∏ i, (α i + 1)) = ∏ i, (α i ^ 2 - 1) := by
  rw [← Finset.prod_mul_distrib]
  congr 1
  ext i
  ring

/-! ### Definitions for the Erdős–Gallai setting -/

/-- f'(1) for our polynomial, up to sign:
    f'(1) = -2 · ∏ᵢ(αᵢ - 1) · ∏ⱼ(βⱼ + 1). -/
noncomputable def erdos_gallai_deriv_at_one {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ) : ℝ :=
  -2 * (∏ i, (α i - 1)) * (∏ j, (β j + 1))

/-- f'(-1) for our polynomial:
    f'(-1) = 2 · ∏ᵢ(αᵢ + 1) · ∏ⱼ(βⱼ - 1). -/
noncomputable def erdos_gallai_deriv_at_neg_one {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ) : ℝ :=
  2 * (∏ i, (α i + 1)) * (∏ j, (β j - 1))

/-- C² = ∏ᵢ(αᵢ² - 1) · ∏ⱼ(βⱼ² - 1). -/
noncomputable def erdos_gallai_C_sq {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ) : ℝ :=
  (∏ i, (α i ^ 2 - 1)) * (∏ j, (β j ^ 2 - 1))

/-- Key identity: -f'(1)·f'(-1) = 4·C².
    That is, -(-2∏(αᵢ-1)∏(βⱼ+1))·(2∏(αᵢ+1)∏(βⱼ-1)) = 4·∏(αᵢ²-1)·∏(βⱼ²-1). -/
theorem erdos_gallai_deriv_product {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ) :
    -(erdos_gallai_deriv_at_one α β) * (erdos_gallai_deriv_at_neg_one α β) =
    4 * erdos_gallai_C_sq α β := by
  simp only [erdos_gallai_deriv_at_one, erdos_gallai_deriv_at_neg_one, erdos_gallai_C_sq]
  rw [← prod_sub_one_mul_prod_add_one α, ← prod_sub_one_mul_prod_add_one β]
  ring

/-- The tangential trapezoid:
    T = -2 f'(1) f'(-1) / (f'(1) - f'(-1)).

    When f'(1) < 0 and f'(-1) > 0 (normal case), this equals
    2·|f'(1)|·|f'(-1)| / (|f'(1)| + |f'(-1)|), the harmonic mean. -/
noncomputable def erdos_gallai_T {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ) : ℝ :=
  -2 * (erdos_gallai_deriv_at_one α β) * (erdos_gallai_deriv_at_neg_one α β) /
    (erdos_gallai_deriv_at_one α β - erdos_gallai_deriv_at_neg_one α β)

/-! ### Integral layer: f(x), area A, and the bound A ≥ (4/3)C -/

open MeasureTheory intervalIntegral

/-- f(x) = (1 - x²) · ∏ᵢ (αᵢ - x) · ∏ⱼ (βⱼ + x). -/
noncomputable def erdos_gallai_f {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ) (x : ℝ) : ℝ :=
  (1 - x ^ 2) * (∏ i, (α i - x)) * (∏ j, (β j + x))

/-- The area A = ∫₋₁¹ f(x) dx. -/
noncomputable def erdos_gallai_area {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, erdos_gallai_f α β x

/-- f is continuous (finite product of continuous functions). -/
theorem erdos_gallai_f_continuous {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ) :
    Continuous (erdos_gallai_f α β) := by
  unfold erdos_gallai_f
  apply Continuous.mul
  · apply Continuous.mul
    · exact continuous_const.sub (continuous_pow 2)
    · exact continuous_finset_prod _ fun i _ =>
        continuous_const.sub continuous_id
  · exact continuous_finset_prod _ fun j _ =>
      continuous_const.add continuous_id

/-- f is interval-integrable on [-1, 1]. -/
theorem erdos_gallai_f_integrable {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ) :
    IntervalIntegrable (erdos_gallai_f α β) MeasureTheory.volume (-1) 1 :=
  (erdos_gallai_f_continuous α β).intervalIntegrable (-1) 1

/-- f(x) · f(-x) = (1 - x²)² · ∏ᵢ (αᵢ² - x²) · ∏ⱼ (βⱼ² - x²). -/
theorem erdos_gallai_f_mul_neg {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ) (x : ℝ) :
    erdos_gallai_f α β x * erdos_gallai_f α β (-x) =
    (1 - x ^ 2) ^ 2 * (∏ i, (α i ^ 2 - x ^ 2)) * (∏ j, (β j ^ 2 - x ^ 2)) := by
  unfold erdos_gallai_f
  simp only [neg_sq]
  have h1 : (∏ i : Fin m, (α i - x)) * (∏ i : Fin m, (α i + x)) =
      ∏ i : Fin m, (α i ^ 2 - x ^ 2) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro i _; ring
  have h2 : (∏ j : Fin n, (β j + x)) * (∏ j : Fin n, (β j + -x)) =
      ∏ j : Fin n, (β j ^ 2 - x ^ 2) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro j _; ring
  calc ((1 - x ^ 2) * ∏ i, (α i - x)) * (∏ j, (β j + x)) *
      (((1 - x ^ 2) * ∏ i, (α i - -x)) * (∏ j, (β j + -x)))
      = (1 - x ^ 2) ^ 2 * ((∏ i, (α i - x)) * (∏ i, (α i - -x))) *
        ((∏ j, (β j + x)) * (∏ j, (β j + -x))) := by ring
    _ = (1 - x ^ 2) ^ 2 * ((∏ i, (α i - x)) * (∏ i, (α i + x))) *
        ((∏ j, (β j + x)) * (∏ j, (β j + -x))) := by simp [sub_neg_eq_add]
    _ = (1 - x ^ 2) ^ 2 * (∏ i, (α i ^ 2 - x ^ 2)) *
        (∏ j, (β j ^ 2 - x ^ 2)) := by rw [h1, h2]

/-- C² ≥ 0 when all αᵢ, βⱼ ≥ 1. -/
theorem erdos_gallai_C_sq_nonneg {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ)
    (hα : ∀ i, 1 ≤ α i) (hβ : ∀ j, 1 ≤ β j) :
    0 ≤ erdos_gallai_C_sq α β := by
  unfold erdos_gallai_C_sq
  apply mul_nonneg
  · exact Finset.prod_nonneg fun i _ => by nlinarith [hα i]
  · exact Finset.prod_nonneg fun j _ => by nlinarith [hβ j]

/-- Symmetrization: ∫₋₁¹ f(-x) dx = ∫₋₁¹ f(x) dx.
    By the substitution x ↦ -x, and using neg_neg on the bounds. -/
theorem erdos_gallai_integral_neg_eq {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ) :
    ∫ x in (-1 : ℝ)..1, erdos_gallai_f α β (-x) =
    ∫ x in (-1 : ℝ)..1, erdos_gallai_f α β x := by
  rw [intervalIntegral.integral_comp_neg]
  simp

/-- f(x) ≥ 0 for x ∈ [-1, 1] when αᵢ, βⱼ ≥ 1. -/
theorem erdos_gallai_f_nonneg {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ)
    (hα : ∀ i, 1 ≤ α i) (hβ : ∀ j, 1 ≤ β j)
    (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ erdos_gallai_f α β x := by
  unfold erdos_gallai_f
  apply mul_nonneg
  · apply mul_nonneg
    · nlinarith [hx.1, hx.2]
    · exact Finset.prod_nonneg fun i _ => by nlinarith [hα i, hx.2]
  · exact Finset.prod_nonneg fun j _ => by nlinarith [hβ j, hx.1]

/-- For x ∈ [-1, 1]: a² - x² ≥ a² - 1. The hypothesis a ≥ 1 from the tex is not needed. -/
theorem sq_sub_sq_ge {a x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    a ^ 2 - 1 ≤ a ^ 2 - x ^ 2 := by
  nlinarith [hx.1, hx.2]

/-- f(x)·f(-x) ≥ (1 - x²)² · C² for x ∈ [-1,1], αᵢ,βⱼ ≥ 1. -/
theorem erdos_gallai_f_mul_neg_ge {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ)
    (hα : ∀ i, 1 ≤ α i) (hβ : ∀ j, 1 ≤ β j)
    (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (1 - x ^ 2) ^ 2 * erdos_gallai_C_sq α β ≤
    erdos_gallai_f α β x * erdos_gallai_f α β (-x) := by
  rw [erdos_gallai_f_mul_neg]
  unfold erdos_gallai_C_sq
  -- Goal: (1-x²)² * (∏(αᵢ²-1) * ∏(βⱼ²-1)) ≤ (1-x²)² * ∏(αᵢ²-x²) * ∏(βⱼ²-x²)
  rw [show (1 - x ^ 2) ^ 2 * ((∏ i, (α i ^ 2 - 1)) * (∏ j, (β j ^ 2 - 1))) =
    (1 - x ^ 2) ^ 2 * (∏ i, (α i ^ 2 - 1)) * (∏ j, (β j ^ 2 - 1)) from by ring]
  apply mul_le_mul
  · apply mul_le_mul_of_nonneg_left
    · apply Finset.prod_le_prod
      · intro i _; nlinarith [hα i]
      · intro i _; exact sq_sub_sq_ge hx
    · exact sq_nonneg _
  · apply Finset.prod_le_prod
    · intro j _; nlinarith [hβ j]
    · intro j _; exact sq_sub_sq_ge hx
  · exact Finset.prod_nonneg fun j _ => by nlinarith [hβ j]
  · apply mul_nonneg (sq_nonneg _)
    exact Finset.prod_nonneg fun i _ => by nlinarith [hα i, hx.1, hx.2]

/-- AM-GM for square roots: 2√(ab) ≤ a + b for a, b ≥ 0. -/
theorem am_gm_sqrt (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * Real.sqrt (a * b) ≤ a + b := by
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hab : Real.sqrt a * Real.sqrt b = Real.sqrt (a * b) := (Real.sqrt_mul ha b).symm
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sqrt_nonneg a, Real.sqrt_nonneg b,
    Real.mul_self_sqrt (mul_nonneg ha hb)]

/-- ∫₋₁¹ (1-x²) dx = 4/3. -/
theorem integral_one_sub_sq : ∫ x in (-1:ℝ)..1, (1 - x ^ 2) = 4 / 3 := by
  have hderiv : ∀ x ∈ Set.uIcc (-1:ℝ) 1,
      HasDerivAt (fun x => x - x ^ 3 / 3) (1 - x ^ 2) x := by
    intro x _
    have h1 := hasDerivAt_id (𝕜 := ℝ) x
    have h3 : HasDerivAt (fun x => x ^ 3 / 3) (x ^ 2) x := by
      have := (hasDerivAt_pow 3 x).div_const (3 : ℝ)
      convert this using 1
      push_cast; ring
    convert h1.sub h3 using 1
  have hint : IntervalIntegrable (fun x => (1:ℝ) - x ^ 2) volume (-1) 1 :=
    (continuous_const.sub (continuous_pow 2)).intervalIntegrable _ _
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  norm_num

/-- The area A ≥ (4/3) · √(C²).
    This is the integral layer of the Erdős–Gallai proof.
    By AM-GM, (f(x) + f(-x))/2 ≥ √(f(x)·f(-x)) ≥ (1-x²)·C.
    Integrating gives A ≥ (4/3)·C. -/
theorem erdos_gallai_integral_bound {m n : ℕ}
    (α : Fin m → ℝ) (β : Fin n → ℝ)
    (hα : ∀ i, 1 ≤ α i) (hβ : ∀ j, 1 ≤ β j) :
    erdos_gallai_area α β ≥ 4 / 3 * Real.sqrt (erdos_gallai_C_sq α β) := by
  unfold erdos_gallai_area
  -- Step 1: A = (1/2)(∫f(x) + ∫f(-x)) = (1/2)∫(f(x)+f(-x))
  have hsym := erdos_gallai_integral_neg_eq α β
  have hfi := erdos_gallai_f_integrable α β
  have hfi_neg : IntervalIntegrable (fun x => erdos_gallai_f α β (-x)) volume (-1) 1 := by
    exact (erdos_gallai_f_continuous α β).comp continuous_neg |>.intervalIntegrable _ _
  -- ∫f(x) = (1/2)(∫f(x) + ∫f(-x)) = (1/2)∫(f(x)+f(-x))
  have hA_eq : ∫ x in (-1:ℝ)..1, erdos_gallai_f α β x =
      (1/2) * ∫ x in (-1:ℝ)..1, (erdos_gallai_f α β x + erdos_gallai_f α β (-x)) := by
    rw [integral_add hfi hfi_neg, hsym]
    ring
  rw [hA_eq]
  -- Step 2: Pointwise bound: f(x)+f(-x) ≥ 2(1-x²)√C² for x ∈ [-1,1]
  -- By AM-GM: a+b ≥ 2√(ab), and ab ≥ (1-x²)²C²
  -- So a+b ≥ 2√((1-x²)²C²) = 2(1-x²)√C²
  have hC_nn := erdos_gallai_C_sq_nonneg α β hα hβ
  -- Step 3: Use integral monotonicity
  have hg_int : IntervalIntegrable (fun x => 2 * (1 - x ^ 2) * Real.sqrt (erdos_gallai_C_sq α β))
      volume (-1) 1 := by
    apply IntervalIntegrable.mul_const
    exact (continuous_const.mul (continuous_const.sub (continuous_pow 2))).intervalIntegrable _ _
  have hfg_int : IntervalIntegrable (fun x => erdos_gallai_f α β x + erdos_gallai_f α β (-x))
      volume (-1) 1 := hfi.add hfi_neg
  have hle : ∀ x ∈ Set.Icc (-1:ℝ) 1,
      2 * (1 - x ^ 2) * Real.sqrt (erdos_gallai_C_sq α β) ≤
      erdos_gallai_f α β x + erdos_gallai_f α β (-x) := by
    intro x hx
    have hfx := erdos_gallai_f_nonneg α β hα hβ x hx
    have hfnx : 0 ≤ erdos_gallai_f α β (-x) := by
      apply erdos_gallai_f_nonneg α β hα hβ
      constructor <;> nlinarith [hx.1, hx.2]
    have hprod := erdos_gallai_f_mul_neg_ge α β hα hβ x hx
    -- AM-GM: f(x) + f(-x) ≥ 2√(f(x)·f(-x))
    have hamgm := am_gm_sqrt (erdos_gallai_f α β x) (erdos_gallai_f α β (-x)) hfx hfnx
    -- √(f(x)·f(-x)) ≥ √((1-x²)²·C²) = (1-x²)·√C²
    have h1x : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    have hsqrt_mono := Real.sqrt_le_sqrt hprod
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h1x] at hsqrt_mono
    linarith
  -- Apply integral monotonicity
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (-1:ℝ) ≤ 1) hg_int hfg_int hle
  -- Simplify the LHS integral
  have hint_calc : ∫ x in (-1:ℝ)..1, 2 * (1 - x ^ 2) * Real.sqrt (erdos_gallai_C_sq α β) =
      2 * Real.sqrt (erdos_gallai_C_sq α β) * (4/3) := by
    rw [show (fun x => 2 * (1 - x ^ 2) * Real.sqrt (erdos_gallai_C_sq α β)) =
        fun x => (2 * Real.sqrt (erdos_gallai_C_sq α β)) * (1 - x ^ 2) from by ext; ring]
    rw [intervalIntegral.integral_const_mul, integral_one_sub_sq]
  linarith


end ErdosGallai
