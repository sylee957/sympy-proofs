import SympyProofs.JordanKrylov.Mathematics.Existence
import Mathlib.Algebra.Polynomial.Eval.Coeff
import SympyProofs.JordanKrylov.Mathematics.VectorPolynomial

/-!
# The definition following the existence statement

Section 2 of Tajima, Ohara, Terui, arXiv:2209.04807v5.
We represent K[μ,λ] as K[λ][μ]: the outer variable is μ, and the inner
variable is λ. The result p(λ,w) is one polynomial with coefficients in Kⁿ.
-/

namespace SympyProofs.JordanKrylov

open Polynomial Matrix

/-- The divided difference ψ_f(μ,λ), written as the exact polynomial quotient
(f(μ)-f(λ))/(μ-λ). The divisor μ-λ is monic in μ. -/
noncomputable def ψ (K : Subfield ℂ) (f : K[X]) : Polynomial K[X] :=
  (f.map C - C f) /ₘ (X - C (X : K[X]))

/-- The denominator-free polynomial identity defining ψ_f. -/
theorem ψ_identity (K : Subfield ℂ) (f : K[X]) :
    (X - C (X : K[X])) * ψ K f = f.map C - C f := by
  apply mul_divByMonic_eq_iff_isRoot.mpr
  simp [IsRoot, eval_map, eval₂_C_X]

/-- Evaluate both variables of ψ_f at complex values: inner λ, then outer μ. -/
noncomputable def ψAt (K : Subfield ℂ) (f : K[X]) (μ lam : ℂ) : ℂ :=
  (ψ K f).eval₂ (eval₂RingHom K.subtype lam) μ

/-- The evaluated identity, valid also when μ=λ. -/
theorem ψAt_identity (K : Subfield ℂ) (f : K[X]) (μ lam : ℂ) :
    (μ - lam) * ψAt K f μ lam = f.eval₂ K.subtype μ - f.eval₂ K.subtype lam := by
  have h := congrArg (fun q : Polynomial K[X] =>
    q.eval₂ (eval₂RingHom K.subtype lam) μ) (ψ_identity K f)
  simpa [ψAt, eval₂_mul, eval₂_sub, eval₂_map] using h

/-- After evaluating at distinct values, the divided difference is an ordinary field quotient. -/
theorem ψAt_eq_quotient (K : Subfield ℂ) (f : K[X]) (μ lam : ℂ) (h : μ ≠ lam) :
    ψAt K f μ lam = (f.eval₂ K.subtype μ - f.eval₂ K.subtype lam) / (μ - lam) := by
  apply (eq_div_iff (sub_ne_zero.mpr h)).mpr
  simpa only [mul_comm] using ψAt_identity K f μ lam

/-- p(λ,w) = ψ_f(A,λ E)w. The coefficient homomorphism sends each
polynomial in λ to its scalar matrix; μ is evaluated at the constant matrix A.
This definition accepts any w. Nonvanishing and annihilation are hypotheses
for the lemmas about the chosen w, rather than inputs to the definition. -/
noncomputable def pCoordinates (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (w : Fin n → K) :
    Fin n → K[X] :=
  (ψ K f).eval₂ (Matrix.scalar (Fin n)) (A.map C) *ᵥ (fun i => C (w i))

/-- p(λ,w), as one polynomial in the scalar λ with vector coefficients in Kⁿ. -/
noncomputable def p (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (w : Fin n → K) :
    PolynomialModule K (Fin n → K) :=
  PolynomialModule.ofCoordinates (pCoordinates K A f w)

@[simp] theorem p_coeff_apply (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (w : Fin n → K) (k : ℕ) (i : Fin n) :
    (p K A f w).coeff k i = (pCoordinates K A f w i).coeff k := by
  simp [p]

/-- Evaluate p at a complex scalar after extending its vector coefficients to ℂⁿ. -/
noncomputable def pAt (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) («λ» : ℂ) (w : Fin n → K) :
    Fin n → ℂ :=
  PolynomialModule.eval «λ»
    (PolynomialModule.map ℂ (PolynomialModule.mapVector ℂ) (p K A f w))

theorem pAt_eq_coordinates (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) («λ» : ℂ) (w : Fin n → K) :
    pAt K A f «λ» w = fun i => (pCoordinates K A f w i).eval₂ K.subtype «λ» := by
  funext i
  exact PolynomialModule.eval_ofCoordinates ℂ (pCoordinates K A f w) «λ» i

/-- Substitute matrices for μ and λ, evaluating the inner variable λ first.
For the paper's substitution A and λ E, the two matrices commute. -/
noncomputable def bivariateMatrix (K : Subfield ℂ) {n : ℕ} (q : Polynomial K[X])
    (μ «λ» : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  q.eval₂
    (eval₂RingHom' ((Matrix.scalar (Fin n)).comp K.subtype) «λ»
      (fun a => Matrix.scalar_commute (K.subtype a) (fun _ => Commute.all _ _) «λ»)) μ

/-- Evaluating a polynomial matrix action commutes with scalar extension to ℂ. -/
theorem bivariate_mulVec_eval (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (q : Polynomial K[X]) («λ» : ℂ) (w : Fin n → K) :
    (fun i => ((q.eval₂ (Matrix.scalar (Fin n)) (A.map C) *ᵥ
      (fun j => C (w j))) i).eval₂ K.subtype «λ») =
      bivariateMatrix K q (A.map K.subtype) («λ» • 1) *ᵥ (fun i => K.subtype (w i)) := by
  let e := eval₂RingHom K.subtype «λ»
  have hscalar : Matrix.scalar (Fin n) «λ» =
      «λ» • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.scalar, Matrix.diagonal, h]
  have hcoeff : e.mapMatrix.comp (Matrix.scalar (Fin n)) =
      eval₂RingHom' ((Matrix.scalar (Fin n)).comp K.subtype) («λ» • 1)
        (fun a => Matrix.scalar_commute (K.subtype a)
          (fun _ => Commute.all _ _) («λ» • 1)) := by
    apply RingHom.ext
    intro q
    ext i j
    have h := Polynomial.hom_eval₂ q K.subtype (Matrix.scalar (Fin n)) «λ»
    rw [hscalar] at h
    change ((Matrix.scalar (Fin n) q).map e) i j =
      (q.eval₂ ((Matrix.scalar (Fin n)).comp K.subtype) («λ» • 1)) i j
    rw [← h]
    by_cases hij : i = j <;>
      simp [Matrix.scalar, Matrix.diagonal, Matrix.map_apply, hij, e]
  have hA : e.mapMatrix (A.map C) = A.map K.subtype := by
    ext i j
    simp [e]
  have hψ := Polynomial.hom_eval₂ q (Matrix.scalar (Fin n)) e.mapMatrix (A.map C)
  rw [hcoeff, hA] at hψ
  ext i
  change e ((_ *ᵥ _) i) = _
  rw [RingHom.map_mulVec]
  rw [show (q.eval₂ (Matrix.scalar (Fin n)) (A.map C)).map e =
      bivariateMatrix K q (A.map K.subtype) («λ» • 1) from hψ]
  simp [e, Function.comp_def]

/-- Matrix substitution into the divided difference ψ_f. -/
noncomputable def ψMatrix (K : Subfield ℂ) {n : ℕ} (f : K[X])
    (μ «λ» : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  bivariateMatrix K (ψ K f) μ «λ»

/-- The paper's formula p(λ,w) = ψ_f(A,λ E)w, after extending A and w to ℂ. -/
theorem pAt_eq_ψMatrix_mulVec (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) («λ» : ℂ) (w : Fin n → K) :
    pAt K A f «λ» w =
      ψMatrix K f (A.map K.subtype) («λ» • 1) *ᵥ (fun i => K.subtype (w i)) := by
  rw [pAt_eq_coordinates]
  exact bivariate_mulVec_eval K A (ψ K f) «λ» w

end SympyProofs.JordanKrylov
