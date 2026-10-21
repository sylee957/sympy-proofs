module

public import Mathlib

/-!
# Gosper's equation and summation certificates

R. W. Gosper, *Decision procedure for indefinite hypergeometric summation*,
PNAS 75 (1978), 40–42, DOI: 10.1073/pnas.75.1.40.

We retain the paper's backward-difference convention: `a(n) = S(n) - S(n-1)`.
Natural-number statements use `n+1` in place of `n` to avoid truncated subtraction.
Polynomial translation is Mathlib's `Polynomial.taylor`.
-/

@[expose] public section
noncomputable section

namespace Gosper

open Polynomial

variable {K : Type*} [Field K]

/-- Equation (6), expressed without a choice of gcd normalization. -/
def ShiftCoprime (q r : K[X]) : Prop :=
  ∀ j : ℕ, IsCoprime q (taylor (j : K) r)

/-- The polynomial operator in equation (8). -/
def operator (q r : K[X]) : K[X] →ₗ[K] K[X] where
  toFun f := taylor 1 q * f - r * taylor (-1) f
  map_add' f g := by simp only [map_add]; ring
  map_smul' c f := by
    simp only [RingHom.id_apply, smul_eq_C_mul, taylor_mul, taylor_C]
    ring

@[simp] theorem operator_apply (q r f : K[X]) :
    operator q r f = taylor 1 q * f - r * taylor (-1) f := rfl

@[simp] theorem eval_operator (q r f : K[X]) (x : K) :
    (operator q r f).eval x = q.eval (x + 1) * f.eval x -
      r.eval x * f.eval (x - 1) := by
  simp [operator, taylor_eval, sub_eq_add_neg]

/-- An indefinite sum, equation (1). -/
def IsAntidifference (a S : ℕ → K) : Prop :=
  ∀ n, S (n + 1) - S n = a (n + 1)

/-- Equations (0) and (1) are equivalent. -/
theorem isAntidifference_iff_sum (a S : ℕ → K) :
    IsAntidifference a S ↔
      ∀ m, ∑ n ∈ Finset.range m, a (n + 1) = S m - S 0 := by
  constructor
  · intro h m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih, ← h m]; ring
  · intro h n
    have hn := h n
    have hs := h (n + 1)
    rw [Finset.sum_range_succ, hn] at hs
    linear_combination -hs

/-- Indefinite sums differ by an additive constant. -/
theorem antidifference_unique (a S T : ℕ → K)
    (hS : IsAntidifference a S) (hT : IsAntidifference a T) (n : ℕ) :
    S n - T n = S 0 - T 0 := by
  have hs := (isAntidifference_iff_sum a S).mp hS n
  have ht := (isAntidifference_iff_sum a T).mp hT n
  linear_combination ht - hs

/-- Equation (7), the sum reconstructed from a polynomial certificate. -/
def certificateSum (a : ℕ → K) (p q f : K[X]) (n : ℕ) : K :=
  q.eval ((n : K) + 1) * f.eval (n : K) * a n / p.eval (n : K)

/-- Equations (5) and (8) imply equation (1). All divisions have explicit
nonvanishing hypotheses; no assumption on the values of `q` is needed. -/
theorem certificate_antidifference (a : ℕ → K) (p q r f : K[X])
    (hp : ∀ n : ℕ, p.eval (n : K) ≠ 0)
    (hratio : ∀ n : ℕ,
      a (n + 1) * p.eval (n : K) * r.eval ((n : K) + 1) =
        a n * p.eval ((n : K) + 1) * q.eval ((n : K) + 1))
    (hf : operator q r f = p) :
    IsAntidifference a (certificateSum a p q f) := by
  intro n
  have he := congrArg (fun P : K[X] => P.eval ((n : K) + 1)) hf
  simp only [eval_operator] at he
  have hn := hp n
  have hn1 := hp (n + 1)
  simp only [Nat.cast_add, Nat.cast_one] at hn1
  dsimp [certificateSum]
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp
  have he' : q.eval ((n : K) + 1 + 1) * f.eval ((n : K) + 1) -
      r.eval ((n : K) + 1) * f.eval (n : K) = p.eval ((n : K) + 1) := by
    simpa using he
  linear_combination a (n + 1) * p.eval (n : K) * he' + f.eval (n : K) * hratio n

theorem certificate_sum (a : ℕ → K) (p q r f : K[X])
    (hp : ∀ n : ℕ, p.eval (n : K) ≠ 0)
    (hratio : ∀ n : ℕ,
      a (n + 1) * p.eval (n : K) * r.eval ((n : K) + 1) =
        a n * p.eval ((n : K) + 1) * q.eval ((n : K) + 1))
    (hf : operator q r f = p) (m : ℕ) :
    ∑ n ∈ Finset.range m, a (n + 1) =
      certificateSum a p q f m - certificateSum a p q f 0 :=
  (isAntidifference_iff_sum _ _).mp
    (certificate_antidifference a p q r f hp hratio hf) m

end Gosper
