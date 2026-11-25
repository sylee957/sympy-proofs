module

public import SympyProofs.LinearAlgebra.Diagonalization.ClosedForm.Quadratic
public import SympyProofs.LinearAlgebra.Diagonalization.ClosedForm.Direct
public import SympyProofs.CubicEquation.Meadow.Monic

/-!
# Diagonalization of 4 × 4 matrices by radicals

Ferrari's cubic resolvent splits the depressed characteristic quartic into two
monic quadratics. When its chosen root vanishes, the same expression splits
the biquadratic. Each label determines one basis vector from the reduced columns of its projector.
-/

@[expose] public section

noncomputable section

namespace SympyProofs.Diagonalization4

open Diagonalization Matrix CubicEquation.CardanoComplex

/-- A Cardano root of the monic resolvent, with an everywhere defined reciprocal. -/
def resolventRoot (a b c : ℂ) : ℂ :=
  monicLabels a b c 0

theorem resolventRoot_spec (a b c : ℂ) :
    let z := resolventRoot a b c
    z ^ 3 + a * z ^ 2 + b * z + c = 0 := by
  dsimp only
  rw [← monicLabels_factor]
  exact Finset.prod_eq_zero (Finset.mem_univ 0) (sub_self _)

/-- Ferrari's two quadratic factors, including the biquadratic case at s = 0. -/
def depressedQuarticLabels (p q r : ℂ) : Fin 4 → ℂ :=
  let z := resolventRoot (2 * p) (p ^ 2 - 4 * r) (-(q ^ 2))
  let s := z.sqrt
  let w := (p ^ 2 - 4 * r).sqrt
  let t := w + (q - s * w) / s
  let f := quadraticLabels s ((p + z - t) / 2)
  let g := quadraticLabels (-s) ((p + z + t) / 2)
  ![f 0, f 1, g 0, g 1]

theorem depressedQuarticLabels_factor (p q r x : ℂ) :
    ∏ j, (x - depressedQuarticLabels p q r j) = x ^ 4 + p * x ^ 2 + q * x + r := by
  let z := resolventRoot (2 * p) (p ^ 2 - 4 * r) (-(q ^ 2))
  let s := z.sqrt
  let w := (p ^ 2 - 4 * r).sqrt
  let t := w + (q - s * w) / s
  have hz : z ^ 3 + 2 * p * z ^ 2 + (p ^ 2 - 4 * r) * z + -(q ^ 2) = 0 :=
    resolventRoot_spec _ _ _
  have hs : s ^ 2 = z := sqrt_sq _
  have hpair : s * t = q ∧ t ^ 2 = (p + z) ^ 2 - 4 * r := by
    by_cases h : s = 0
    · have hz₀ : z = 0 := by simpa [h] using hs.symm
      have hq : q = 0 := by simpa [hz₀] using hz
      simp [t, w, h, hz₀, hq]
    · have ht : t = q / s := by
        dsimp [t]
        field_simp
        ring
      rw [ht]
      constructor
      · field_simp
      · field_simp
        linear_combination -hz - ((p + z) ^ 2 - 4 * r) * hs
  let u := (p + z - t) / 2
  let v := (p + z + t) / 2
  have hf : x ^ 4 + p * x ^ 2 + q * x + r =
      (x ^ 2 + s * x + u) * (x ^ 2 + (-s) * x + v) := by
    dsimp only [u, v]
    linear_combination x ^ 2 * hs - x * hpair.1 + hpair.2 / 4
  rw [Fin.prod_univ_four, hf]
  change (x - quadraticLabels s u 0) * (x - quadraticLabels s u 1) *
    (x - quadraticLabels (-s) v 0) * (x - quadraticLabels (-s) v 1) = _
  rw [mul_assoc _ _ (x - quadraticLabels (-s) v 1), quadraticLabels_factor, quadraticLabels_factor]

def depressedQuarticRoots (p q r : ℂ) : List ℂ := List.ofFn (depressedQuarticLabels p q r)

theorem mem_depressedQuarticRoots (p q r x : ℂ) :
    x ∈ depressedQuarticRoots p q r ↔ x ^ 4 + p * x ^ 2 + q * x + r = 0 := by
  rw [depressedQuarticRoots, Meadow.mem_labels_iff, depressedQuarticLabels_factor]

/-- Shift the four radical roots back to the original quartic. -/
def quarticLabels (a b c d : ℂ) : Fin 4 → ℂ :=
  let p := b - 3 * a ^ 2 / 8
  let q := a ^ 3 / 8 - a * b / 2 + c
  let r := -3 * a ^ 4 / 256 + a ^ 2 * b / 16 - a * c / 4 + d
  fun i => depressedQuarticLabels p q r i - a / 4

theorem quarticLabels_factor (a b c d x : ℂ) :
    ∏ j, (x - quarticLabels a b c d j) = x ^ 4 + a * x ^ 3 + b * x ^ 2 + c * x + d := by
  unfold quarticLabels
  simp_rw [show ∀ y : ℂ, x - (y - a / 4) = (x + a / 4) - y by intro y; ring]
  rw [depressedQuarticLabels_factor]
  ring

def quarticRoots (a b c d : ℂ) : List ℂ := List.ofFn (quarticLabels a b c d)

theorem mem_quarticRoots (a b c d x : ℂ) :
    x ∈ quarticRoots a b c d ↔ x ^ 4 + a * x ^ 3 + b * x ^ 2 + c * x + d = 0 := by
  rw [quarticRoots, Meadow.mem_labels_iff, quarticLabels_factor]

/-- Sum of principal minors of order k. The index sets depend only on k. -/
def principalMinorSum (A : Matrix (Fin 4) (Fin 4) ℂ) (k : ℕ) : ℂ :=
  ∑ s ∈ (Finset.univ : Finset (Fin 4)).powersetCard k,
    (A.submatrix (Subtype.val : s → Fin 4) Subtype.val).det

/-- Four characteristic roots as expressions in the sixteen matrix entries. -/
def labels (A : Matrix (Fin 4) (Fin 4) ℂ) : Fin 4 → ℂ :=
  quarticLabels (-A.trace) (principalMinorSum A 2) (-principalMinorSum A 3) A.det

def radicalRoots (A : Matrix (Fin 4) (Fin 4) ℂ) : List ℂ := List.ofFn (labels A)

theorem labels_charpoly (A : Matrix (Fin 4) (Fin 4) ℂ) :
    A.charpoly = (diagonal (labels A)).charpoly := by
  apply Polynomial.funext
  intro x
  have h₄ : A.charpoly.coeff 4 = 1 := by simpa using A.charpoly_monic.coeff_natDegree
  have h₃ : A.trace = -A.charpoly.coeff 3 := A.trace_eq_neg_charpoly_coeff
  have h₂ : A.charpoly.coeff 2 = principalMinorSum A 2 := by
    simpa [principalMinorSum] using A.charpoly_coeff_eq_sum_minors 2 (by decide)
  have h₁ : A.charpoly.coeff 1 = -principalMinorSum A 3 := by
    simpa [principalMinorSum, pow_succ] using A.charpoly_coeff_eq_sum_minors 3 (by decide)
  have h₀ : A.det = A.charpoly.coeff 0 := by simpa [pow_succ] using A.det_eq_sign_charpoly_coeff
  rw [charpoly_diagonal, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, labels, quarticLabels_factor]
  rw [Polynomial.eval_eq_sum_range]
  simp [Finset.sum_range_succ, h₄, h₃, h₂, h₁, h₀, add_comm, add_left_comm, add_assoc]

theorem mem_radicalRoots (A : Matrix (Fin 4) (Fin 4) ℂ) (x : ℂ) :
    x ∈ radicalRoots A ↔ A.charpoly.eval x = 0 := by
  simp only [radicalRoots, Meadow.mem_labels_iff, labels_charpoly, charpoly_diagonal,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

def complexPair (A : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ × (Fin 4 → ℂ) :=
  let d := labels A
  (Meadow.basisMatrix A d, d)

def realPair (A : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ × (Fin 4 → ℝ) :=
  let d := fun i => (labels (A.map Complex.ofRealHom) i).re
  (Meadow.basisMatrix A d, d)

theorem complexPair_correct (A : Matrix (Fin 4) (Fin 4) ℂ) (h : ∃ P d, IsDiagonalization A P d) :
    IsDiagonalization A (complexPair A).1 (complexPair A).2 := by
  obtain ⟨Q, e, he⟩ := h
  apply Meadow.basisMatrix_correct Meadow.goodWeights_four he
  rw [← Meadow.roots_diagonal, ← labels_charpoly, Meadow.charpoly_eq he, Meadow.roots_diagonal]

theorem realPair_correct (A : Matrix (Fin 4) (Fin 4) ℝ) (h : ∃ P d, IsDiagonalization A P d) :
    IsDiagonalization A (realPair A).1 (realPair A).2 := by
  obtain ⟨Q, e, he⟩ := h
  exact Meadow.basisMatrix_correct Meadow.goodWeights_four he
    (Meadow.real_spectrum he (labels_charpoly _))

/-- Return the direct complex eigenbasis when its certificate succeeds. -/
def diagonalizeComplex (A : Matrix (Fin 4) (Fin 4) ℂ) :=
  Meadow.asOption (Meadow.certify A (complexPair A))

theorem diagonalizeComplex_sound {A P : Matrix (Fin 4) (Fin 4) ℂ} {d : Fin 4 → ℂ}
    (h : diagonalizeComplex A = some (P, d)) : IsDiagonalization A P d :=
  Meadow.asOption_sound h

theorem diagonalizeComplex_isSome_iff (A : Matrix (Fin 4) (Fin 4) ℂ) :
    (diagonalizeComplex A).isSome ↔ ∃ P d, IsDiagonalization A P d :=
  Meadow.asOption_isSome (complexPair_correct A)

/-- Return the direct real eigenbasis when its certificate succeeds. -/
def diagonalizeReal (A : Matrix (Fin 4) (Fin 4) ℝ) :=
  Meadow.asOption (Meadow.certify A (realPair A))

theorem diagonalizeReal_sound {A P : Matrix (Fin 4) (Fin 4) ℝ} {d : Fin 4 → ℝ}
    (h : diagonalizeReal A = some (P, d)) : IsDiagonalization A P d :=
  Meadow.asOption_sound h

theorem diagonalizeReal_isSome_iff (A : Matrix (Fin 4) (Fin 4) ℝ) :
    (diagonalizeReal A).isSome ↔ ∃ P d, IsDiagonalization A P d :=
  Meadow.asOption_isSome (realPair_correct A)

namespace StraightLine

/-- The direct complex diagonalization, with the zero pair encoding failure. -/
def formula (A : Matrix (Fin 4) (Fin 4) ℂ) := Meadow.certify A (complexPair A)

theorem formula_eq (A : Matrix (Fin 4) (Fin 4) ℂ) : formula A = (diagonalizeComplex A).getD 0 :=
  (Meadow.asOption_getD _ _).symm

theorem formula_correct (A : Matrix (Fin 4) (Fin 4) ℂ) (h : ∃ P d, IsDiagonalization A P d) :
    IsDiagonalization A (formula A).1 (formula A).2 :=
  Meadow.certify_correct (complexPair_correct A h)

theorem formula_eq_zero_of_defective (A : Matrix (Fin 4) (Fin 4) ℂ)
    (h : ¬ ∃ P d, IsDiagonalization A P d) : formula A = 0 :=
  Meadow.certify_eq_zero _ h

/-- The direct real diagonalization, with the zero pair encoding failure. -/
def realFormula (A : Matrix (Fin 4) (Fin 4) ℝ) := Meadow.certify A (realPair A)

theorem realFormula_eq (A : Matrix (Fin 4) (Fin 4) ℝ) :
    realFormula A = (diagonalizeReal A).getD 0 :=
  (Meadow.asOption_getD _ _).symm

theorem realFormula_correct (A : Matrix (Fin 4) (Fin 4) ℝ) (h : ∃ P d, IsDiagonalization A P d) :
    IsDiagonalization A (realFormula A).1 (realFormula A).2 :=
  Meadow.certify_correct (realPair_correct A h)

theorem realFormula_eq_zero_of_no_real_basis (A : Matrix (Fin 4) (Fin 4) ℝ)
    (h : ¬ ∃ P d, IsDiagonalization A P d) : realFormula A = 0 :=
  Meadow.certify_eq_zero _ h

end StraightLine

end SympyProofs.Diagonalization4
