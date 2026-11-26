module

public import SympyProofs.Calculus.Antiderivative.Algebra.Rat
public import SympyProofs.Calculus.Antiderivative.Spec.NatBound
public import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The two bounds of the rational numbers are bounds: `LawfulNatBound ℚ`.

`natBound` is exact: it returns the natural number itself. `natRootBound` is Cauchy's
estimate: if `m ≥ 1` is a root of a polynomial with leading coefficient `l` and lower
coefficients `c₀, …, cₙ₋₁`, then `|l| mⁿ = |c₀ + … + cₙ₋₁ mⁿ⁻¹| ≤ (|c₀| + … + |cₙ₋₁|) mⁿ⁻¹`,
so `m ≤ (|c₀| + … + |cₙ₋₁|) / |l|`.

The estimate is proved for lists of coefficients (`le_radius`), with the value of a list by
Horner's rule, `Poly.Raw.eval`; the instance applies it to the trimmed list of coefficients
of a polynomial, whose last element is not zero. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Rational

/-! ### Cauchy's estimate -/

/-- `absQ` is the absolute value. -/
theorem absQ_eq (q : ℚ) : absQ q = |q| := by
  rw [absQ]
  split
  · rename_i h
    exact (abs_of_neg (show q < 0 from h)).symm
  · rename_i h
    exact (abs_of_nonneg (not_lt.mp (show ¬ q < 0 from h))).symm

/-- The value of a list with one more coefficient at the end. -/
theorem eval_append (init : List ℚ) (l x : ℚ) :
    Poly.Raw.eval x (init ++ [l]) = Poly.Raw.eval x init + x ^ init.length * l := by
  induction init with
  | nil => simp [Poly.Raw.eval]
  | cons c cs ih =>
    simp only [List.cons_append, Poly.Raw.eval, ih, List.length_cons, pow_succ]
    ring

/-- At a point `x ≥ 1` the value of a polynomial is bounded by the sum of the absolute values
of its coefficients times a power of `x`. -/
theorem abs_eval_mul_le {x : ℚ} (hx : 1 ≤ x) : ∀ cs : List ℚ,
    |Poly.Raw.eval x cs| * x ≤ (cs.map absQ).sum * x ^ cs.length
  | [] => by simp [Poly.Raw.eval]
  | c :: cs => by
    have ih := abs_eval_mul_le hx cs
    have x0 : 0 ≤ x := le_trans zero_le_one hx
    have h1 : |c + x * Poly.Raw.eval x cs| ≤ |c| + x * |Poly.Raw.eval x cs| := by
      calc
        _ ≤ |c| + |x * Poly.Raw.eval x cs| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_of_nonneg x0]
    have h2 : |c| * x ≤ |c| * x ^ (cs.length + 1) :=
      mul_le_mul_of_nonneg_left (le_self_pow₀ hx (Nat.succ_ne_zero _)) (abs_nonneg c)
    simp only [Poly.Raw.eval, List.map_cons, List.sum_cons, List.length_cons, absQ_eq]
    calc
      _ ≤ (|c| + x * |Poly.Raw.eval x cs|) * x := mul_le_mul_of_nonneg_right h1 x0
      _ = |c| * x + x * (|Poly.Raw.eval x cs| * x) := by ring
      _ ≤ |c| * x ^ (cs.length + 1) + x * ((cs.map absQ).sum * x ^ cs.length) :=
        add_le_add h2 (mul_le_mul_of_nonneg_left ih x0)
      _ = _ := by ring

/-- What `radius` computes for a list with a last coefficient. -/
theorem radius_append (init : List ℚ) (l : ℚ) :
    radius (init ++ [l]) = (1 + (init.map absQ).sum / absQ l).ceil.toNat := by
  simp [radius, List.sum_eq_foldl, List.foldl_map]

/-- Cauchy's estimate: a natural number that is a root of a rational polynomial whose leading
coefficient `l` is not zero is at most `radius` of its list of coefficients. -/
theorem le_radius {init : List ℚ} {l : ℚ} (hl : l ≠ 0) {m : ℕ}
    (hm : Poly.Raw.eval (m : ℚ) (init ++ [l]) = 0) : m ≤ radius (init ++ [l]) := by
  rcases Nat.eq_zero_or_pos m with rfl | pos
  · exact Nat.zero_le _
  have hl : 0 < |l| := abs_pos.mpr hl
  have hx : (1 : ℚ) ≤ m := by exact_mod_cast pos
  have xpos : (0 : ℚ) < (m : ℚ) ^ init.length := pow_pos (lt_of_lt_of_le zero_lt_one hx) _
  have root : Poly.Raw.eval (m : ℚ) init + (m : ℚ) ^ init.length * l = 0 := by
    rw [← eval_append]
    exact hm
  have habs : |Poly.Raw.eval (m : ℚ) init| = (m : ℚ) ^ init.length * |l| := by
    rw [eq_neg_of_add_eq_zero_left root, abs_neg, abs_mul, abs_of_pos xpos]
  have bound := abs_eval_mul_le hx init
  rw [habs] at bound
  have le : |l| * (m : ℚ) ≤ (init.map absQ).sum := by
    apply le_of_mul_le_mul_right _ xpos
    calc
      _ = (m : ℚ) ^ init.length * |l| * m := by ring
      _ ≤ _ := bound
  have key : (m : ℚ) ≤ 1 + (init.map absQ).sum / absQ l := by
    rw [absQ_eq]
    have : (m : ℚ) ≤ (init.map absQ).sum / |l| := (le_div_iff₀ hl).mpr (by linarith)
    linarith
  rw [radius_append]
  have cast : ((m : ℤ) : ℚ) ≤ ((1 + (init.map absQ).sum / absQ l).ceil : ℚ) := by
    push_cast
    exact key.trans Rat.le_ceil
  have : (m : ℤ) ≤ (1 + (init.map absQ).sum / absQ l).ceil := by exact_mod_cast cast
  omega

/-- The bound of a natural number is the number itself. -/
theorem natBound_natCast (m : ℕ) : natBound (m : ℚ) = m := by
  simp [natBound]

/-! ### The instance -/

/-- The two bounds of the rational numbers are bounds: a natural number is its own bound, and
Cauchy's estimate bounds the natural numbers that are roots of a nonzero polynomial. -/
instance lawfulNatBoundRat : LawfulNatBound ℚ where
  natBound_spec c m h := by
    subst h
    exact (natBound_natCast m).ge
  natRootBound_spec p m hp hroot := by
    change m ≤ radius p.coeffs
    rw [Poly.eval_eq_eval_coeffs] at hroot
    rcases List.eq_nil_or_concat p.coeffs with e | ⟨init, l, e⟩
    · exact (hp (Poly.coeffs_eq_nil.mp e)).elim
    rw [List.concat_eq_append] at e
    have hl : l ≠ 0 := by
      intro l0
      apply Poly.getLast?_coeffs p
      rw [e, l0, List.getLast?_concat]
    rw [e] at hroot ⊢
    exact le_radius hl hroot

end SympyProofs.Calculus.Antiderivative.Rational
