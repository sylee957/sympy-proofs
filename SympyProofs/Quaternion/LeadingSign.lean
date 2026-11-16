module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Sign
public import Mathlib.Tactic

/-!
# The sign of the first nonzero entry of a list

`leadingSign xs` is the sign of the first nonzero entry of `xs`, and `1` if there is none.
It replaces the plain `sign` of SymPy's `Quaternion.from_rotation_matrix`, which returns
`0` and so loses a component whenever its argument vanishes.

* `leadingSign_nil`, `leadingSign_cons`, `leadingSign_cons_zero`,
  `leadingSign_cons_of_ne_zero`: how the value is computed from the front of the list.
* `half_sqrt_mul_leadingSign_eq`: the four components of a quaternion whose first nonzero
  component is positive are recovered from its ten products `4 qᵢ qⱼ`. Both conversion
  formulas of this directory are instances of this statement.
-/

@[expose] public section

namespace SympyQuaternion

/-- The sign of the first nonzero entry of a list, and `1` if there is none.

The entries are visited from the last to the first. At each step the running value is kept
when the entry is zero and replaced by the sign of the entry otherwise, by arithmetic on
`Real.sign x ∈ {-1, 0, 1}` and with no comparison with zero. An earlier nonzero entry
therefore overrides everything after it. -/
noncomputable def leadingSign (xs : List ℝ) : ℝ := Id.run do
  let mut result := 1
  for x in xs.reverse do
    result := Real.sign x + (1 - Real.sign x ^ 2) * result
  return result

theorem leadingSign_eq_foldr (xs : List ℝ) :
    leadingSign xs = xs.foldr (fun x result => Real.sign x + (1 - Real.sign x ^ 2) * result) 1 := by
  simp [leadingSign]

@[simp]
theorem leadingSign_nil : leadingSign [] = 1 := by
  simp [leadingSign]

theorem leadingSign_cons (x : ℝ) (xs : List ℝ) :
    leadingSign (x :: xs) = Real.sign x + (1 - Real.sign x ^ 2) * leadingSign xs := by
  simp [leadingSign_eq_foldr]

/-- A leading zero is skipped. -/
@[simp]
theorem leadingSign_cons_zero (xs : List ℝ) : leadingSign (0 :: xs) = leadingSign xs := by
  simp [leadingSign_cons]

/-- A nonzero first entry decides the sign. -/
theorem leadingSign_cons_of_ne_zero {x : ℝ} (hx : x ≠ 0) (xs : List ℝ) :
    leadingSign (x :: xs) = Real.sign x := by
  rcases Real.sign_apply_eq_of_ne_zero x hx with h | h <;> simp [leadingSign_cons, h]

private theorem half_sqrt_four_mul_self (x : ℝ) : √(4 * (x * x)) / 2 = |x| := by
  rw [show 4 * (x * x) = (2 * x) * (2 * x) by ring, Real.sqrt_mul_self_eq_abs, abs_mul,
    abs_two]
  ring

private theorem abs_mul_leadingSign_cons_of_pos {a : ℝ} (ha : 0 < a) (b : ℝ) (xs : List ℝ) :
    |b| * leadingSign (4 * (a * b) :: xs) = b := by
  rcases lt_trichotomy b 0 with hb | rfl | hb
  · have h : 4 * (a * b) < 0 := by nlinarith
    rw [leadingSign_cons_of_ne_zero h.ne, Real.sign_of_neg h, abs_of_neg hb]
    ring
  · simp
  · have h : 0 < 4 * (a * b) := by positivity
    rw [leadingSign_cons_of_ne_zero h.ne', Real.sign_of_pos h, abs_of_pos hb]
    ring

/-- Four numbers `a`, `b`, `c`, `d` whose first nonzero one is positive are recovered from
their ten products: the squares `4a²`, `4b²`, `4c²`, `4d²` give the absolute values, and
each sign is the sign of the first nonzero product with an earlier number. -/
theorem half_sqrt_mul_leadingSign_eq {a b c d t0 t1 t2 t3 u01 u02 u03 u12 u13 u23 : ℝ}
    (h0 : t0 = 4 * (a * a)) (h1 : t1 = 4 * (b * b)) (h2 : t2 = 4 * (c * c))
    (h3 : t3 = 4 * (d * d)) (h01 : u01 = 4 * (a * b)) (h02 : u02 = 4 * (a * c))
    (h03 : u03 = 4 * (a * d)) (h12 : u12 = 4 * (b * c)) (h13 : u13 = 4 * (b * d))
    (h23 : u23 = 4 * (c * d))
    (n : 0 < a ∨ a = 0 ∧ (0 < b ∨ b = 0 ∧ (0 < c ∨ c = 0 ∧ 0 < d))) :
    √t0 / 2 = a ∧ √t1 / 2 * leadingSign [u01] = b ∧
      √t2 / 2 * leadingSign [u02, u12] = c ∧
      √t3 / 2 * leadingSign [u03, u13, u23] = d := by
  subst h0 h1 h2 h3 h01 h02 h03 h12 h13 h23
  simp only [half_sqrt_four_mul_self]
  rcases n with ha | ⟨rfl, hb | ⟨rfl, hc | ⟨rfl, hd⟩⟩⟩
  · exact ⟨abs_of_pos ha, abs_mul_leadingSign_cons_of_pos ha _ _,
      abs_mul_leadingSign_cons_of_pos ha _ _, abs_mul_leadingSign_cons_of_pos ha _ _⟩
  · refine ⟨by simp, ?_, ?_, ?_⟩
    · rw [zero_mul, mul_zero, leadingSign_cons_zero, leadingSign_nil, mul_one, abs_of_pos hb]
    · rw [zero_mul, mul_zero, leadingSign_cons_zero]
      exact abs_mul_leadingSign_cons_of_pos hb _ _
    · rw [zero_mul, mul_zero, leadingSign_cons_zero]
      exact abs_mul_leadingSign_cons_of_pos hb _ _
  · refine ⟨by simp, by simp, ?_, ?_⟩
    · simp [abs_of_pos hc]
    · rw [zero_mul, mul_zero, leadingSign_cons_zero, leadingSign_cons_zero]
      exact abs_mul_leadingSign_cons_of_pos hc _ _
  · exact ⟨by simp, by simp, by simp, by simp [abs_of_pos hd]⟩

end SympyQuaternion
