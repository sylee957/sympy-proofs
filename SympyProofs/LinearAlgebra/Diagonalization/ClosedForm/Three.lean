module

public import SympyProofs.CubicEquation.Meadow.Monic
public import SympyProofs.LinearAlgebra.Diagonalization.ClosedForm.Direct
public import SympyProofs.LinearAlgebra.Diagonalization.ClosedForm.StraightLine

/-!
# Diagonalization of 3 × 3 matrices by radicals

`diagonalizeComplex` returns a basis matrix and the three diagonal entries, or
`none` if the matrix is defective. `diagonalizeReal` uses the same complex
radicals for the characteristic cubic and returns a real diagonalization exactly
when one exists over ℝ.

The characteristic coefficients feed the monic Cardano formula. Equal labels
use different fixed weighted combinations of the reduced projector columns.
-/

@[expose] public section

noncomputable section

namespace SympyProofs.Diagonalization3

open Diagonalization

export Diagonalization (diagonalizeWith_sound diagonalizeWith_isSome diagonalizeWith_complete)

open Matrix Polynomial Lagrange
open CubicEquation.CardanoComplex

/-- Sum of the three principal 2 × 2 minors. -/
def principalMinorSum (A : Matrix (Fin 3) (Fin 3) ℂ) : ℂ :=
  (A 0 0 * A 1 1 - A 0 1 * A 1 0) + (A 0 0 * A 2 2 - A 0 2 * A 2 0) +
    (A 1 1 * A 2 2 - A 1 2 * A 2 1)

/-- Ordered roots of the characteristic cubic, including repeated labels. -/
def labels (A : Matrix (Fin 3) (Fin 3) ℂ) : Fin 3 → ℂ :=
  monicLabels (-A.trace) (principalMinorSum A) (-A.det)

def radicalRoots (A : Matrix (Fin 3) (Fin 3) ℂ) : List ℂ := List.ofFn (labels A)

theorem eval_charpoly_three (A : Matrix (Fin 3) (Fin 3) ℂ) (x : ℂ) :
    A.charpoly.eval x = x ^ 3 - A.trace * x ^ 2 + principalMinorSum A * x - A.det := by
  rw [eval_charpoly]
  simp [det_fin_three, principalMinorSum, trace, Fin.sum_univ_three, scalar_apply]
  ring

theorem labels_charpoly (A : Matrix (Fin 3) (Fin 3) ℂ) :
    A.charpoly = (diagonal (labels A)).charpoly := by
  apply Polynomial.funext
  intro x
  rw [eval_charpoly_three, charpoly_diagonal, eval_prod]
  simp only [eval_sub, eval_X, eval_C, labels, monicLabels_factor]
  ring

theorem mem_radicalRoots (A : Matrix (Fin 3) (Fin 3) ℂ) (x : ℂ) :
    x ∈ radicalRoots A ↔ A.charpoly.eval x = 0 := by
  simp only [radicalRoots, Meadow.mem_labels_iff, labels_charpoly, charpoly_diagonal, eval_prod,
    eval_sub, eval_X, eval_C]

/-- The real roots are selected after evaluating the radicals in ℂ. -/
noncomputable def realRadicalRoots (A : Matrix (Fin 3) (Fin 3) ℝ) : List ℝ :=
  ((radicalRoots (A.map Complex.ofRealHom)).filter fun z => z.im = 0).map Complex.re

theorem mem_realRadicalRoots (A : Matrix (Fin 3) (Fin 3) ℝ) (x : ℝ) :
    x ∈ realRadicalRoots A ↔ A.charpoly.eval x = 0 := by
  have hcast : (x : ℂ) ∈ radicalRoots (A.map Complex.ofRealHom) ↔ A.charpoly.eval x = 0 := by
    rw [mem_radicalRoots, charpoly_map]
    change (A.charpoly.map Complex.ofRealHom).eval (Complex.ofRealHom x) = 0 ↔ _
    rw [Polynomial.eval_map_apply]
    exact Complex.ofReal_eq_zero
  rw [← hcast]
  simp only [realRadicalRoots, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨z, ⟨hz, him⟩, rfl⟩
    have he : (z.re : ℂ) = z := Complex.ext rfl (by simpa using him.symm)
    rwa [he]
  · intro hx
    exact ⟨x, ⟨hx, rfl⟩, rfl⟩

def complexPair (A : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ × (Fin 3 → ℂ) :=
  let d := labels A
  (Meadow.basisMatrix A d, d)

def realPair (A : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ) :=
  let d := fun i => (labels (A.map Complex.ofRealHom) i).re
  (Meadow.basisMatrix A d, d)

theorem complexPair_correct (A : Matrix (Fin 3) (Fin 3) ℂ) (h : ∃ P d, IsDiagonalization A P d) :
    IsDiagonalization A (complexPair A).1 (complexPair A).2 := by
  obtain ⟨Q, e, he⟩ := h
  apply Meadow.basisMatrix_correct Meadow.goodWeights_three he
  rw [← Meadow.roots_diagonal, ← labels_charpoly, Meadow.charpoly_eq he, Meadow.roots_diagonal]

theorem realPair_correct (A : Matrix (Fin 3) (Fin 3) ℝ) (h : ∃ P d, IsDiagonalization A P d) :
    IsDiagonalization A (realPair A).1 (realPair A).2 := by
  obtain ⟨Q, e, he⟩ := h
  exact Meadow.basisMatrix_correct Meadow.goodWeights_three he
    (Meadow.real_spectrum he (labels_charpoly _))

/-- Return the direct complex eigenbasis when its certificate succeeds. -/
def diagonalizeComplex (A : Matrix (Fin 3) (Fin 3) ℂ) :=
  Meadow.asOption (Meadow.certify A (complexPair A))

theorem diagonalizeComplex_sound {A P : Matrix (Fin 3) (Fin 3) ℂ} {d : Fin 3 → ℂ}
    (h : diagonalizeComplex A = some (P, d)) : IsDiagonalization A P d :=
  Meadow.asOption_sound h

theorem diagonalizeComplex_isSome_iff (A : Matrix (Fin 3) (Fin 3) ℂ) :
    (diagonalizeComplex A).isSome ↔ ∃ P d, IsDiagonalization A P d :=
  Meadow.asOption_isSome (complexPair_correct A)

/-- Return the direct real eigenbasis when its certificate succeeds. -/
def diagonalizeReal (A : Matrix (Fin 3) (Fin 3) ℝ) :=
  Meadow.asOption (Meadow.certify A (realPair A))

theorem diagonalizeReal_sound {A P : Matrix (Fin 3) (Fin 3) ℝ} {d : Fin 3 → ℝ}
    (h : diagonalizeReal A = some (P, d)) : IsDiagonalization A P d :=
  Meadow.asOption_sound h

theorem diagonalizeReal_isSome_iff (A : Matrix (Fin 3) (Fin 3) ℝ) :
    (diagonalizeReal A).isSome ↔ ∃ P d, IsDiagonalization A P d :=
  Meadow.asOption_isSome (realPair_correct A)

/-- For three distinct Cardano roots, Cayley–Hamilton guarantees success. -/
theorem diagonalizeComplex_of_distinct (A : Matrix (Fin 3) (Fin 3) ℂ) (h : (radicalRoots A).Nodup) :
    (diagonalizeComplex A).isSome := by
  let s := (radicalRoots A).toFinset
  have hc : s.card = 3 := (List.toFinset_card_of_nodup h).trans (by simp [radicalRoots])
  have hp : nodal s id = A.charpoly := by
    apply eq_of_degree_le_of_eval_finset_eq s
    · rw [degree_nodal]
    · simp [degree_nodal, hc, Matrix.charpoly_degree_eq_dim]
    · exact nodal_monic.trans A.charpoly_monic.symm
    · intro x hx
      exact (eval_nodal_at_node (v := id) hx).trans
        ((mem_radicalRoots A x).mp (List.mem_toFinset.mp hx)).symm
  apply (diagonalizeComplex_isSome_iff A).mpr
  apply (Diagonalization.diagonalizeWith_isSome_iff A (fun x => (mem_radicalRoots A x).mpr)).mp
  apply diagonalizeWith_isSome.mpr
  change aeval A (nodal s id) = 0
  rw [hp, aeval_self_charpoly]

namespace StraightLine

open Complex

export SympyProofs.Diagonalization.StraightLine
  (zeroIndicator zeroIndicator_eq reciprocal denominator_ne_zero reciprocal_eq absent factorProduct
    projector candidate selectBasis zeroMatrixIndicator fromRoots)

/-- Substituting y = U + V and imposing UV = -p/3 determines the radicands.
Completing the square in the quadratic for U³ gives these two values. -/
theorem derive_cube_radicands (p q U V : ℂ)
    (hy : (U + V) ^ 3 + p * (U + V) + q = 0) (huv : U * V = -p / 3) :
    U ^ 3 = -q / 2 + (q ^ 2 / 4 + p ^ 3 / 27).sqrt ∨
    U ^ 3 = -q / 2 - (q ^ 2 / 4 + p ^ 3 / 27).sqrt := by
  have hsum : U ^ 3 + V ^ 3 = -q := by linear_combination hy - 3 * (U + V) * huv
  have hprod : U ^ 3 * V ^ 3 = (-p / 3) ^ 3 := by rw [← mul_pow, huv]
  let Δ := q ^ 2 / 4 + p ^ 3 / 27
  have hsq : (U ^ 3 + q / 2) ^ 2 = Δ.sqrt ^ 2 := by
    rw [sqrt_sq]
    dsimp [Δ]
    linear_combination U ^ 3 * hsum - hprod
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with h | h
  · left; linear_combination h
  · right; linear_combination h

def realLabels (A : Matrix (Fin 3) (Fin 3) ℝ) : List ℝ :=
  (radicalRoots (A.map Complex.ofRealHom)).map Complex.re

/-- The direct complex diagonalization, with the zero pair encoding failure. -/
def formula (A : Matrix (Fin 3) (Fin 3) ℂ) := Meadow.certify A (complexPair A)

theorem formula_eq (A : Matrix (Fin 3) (Fin 3) ℂ) : formula A = (diagonalizeComplex A).getD 0 :=
  (Meadow.asOption_getD _ _).symm

theorem formula_correct (A : Matrix (Fin 3) (Fin 3) ℂ) (h : ∃ P d, IsDiagonalization A P d) :
    IsDiagonalization A (formula A).1 (formula A).2 :=
  Meadow.certify_correct (complexPair_correct A h)

theorem formula_eq_zero_of_defective (A : Matrix (Fin 3) (Fin 3) ℂ)
    (h : ¬ ∃ P d, IsDiagonalization A P d) : formula A = 0 :=
  Meadow.certify_eq_zero _ h

/-- The direct real diagonalization, with the zero pair encoding failure. -/
def realFormula (A : Matrix (Fin 3) (Fin 3) ℝ) := Meadow.certify A (realPair A)

theorem realFormula_eq (A : Matrix (Fin 3) (Fin 3) ℝ) :
    realFormula A = (diagonalizeReal A).getD 0 :=
  (Meadow.asOption_getD _ _).symm

theorem realFormula_correct (A : Matrix (Fin 3) (Fin 3) ℝ) (h : ∃ P d, IsDiagonalization A P d) :
    IsDiagonalization A (realFormula A).1 (realFormula A).2 :=
  Meadow.certify_correct (realPair_correct A h)

theorem realFormula_eq_zero_of_no_real_basis (A : Matrix (Fin 3) (Fin 3) ℝ)
    (h : ¬ ∃ P d, IsDiagonalization A P d) : realFormula A = 0 :=
  Meadow.certify_eq_zero _ h

end StraightLine

end SympyProofs.Diagonalization3
