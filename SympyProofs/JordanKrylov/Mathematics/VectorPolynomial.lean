import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

/-! Small bridges between mathlib's polynomial module and coordinate polynomials. -/

namespace PolynomialModule

open Polynomial

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Assemble coordinate polynomials into one polynomial with vector coefficients. -/
noncomputable def ofCoordinates (v : Fin n → R[X]) : PolynomialModule R (Fin n → R) :=
  ∑ i, v i • single R 0 (Pi.single i 1)

@[simp] theorem coeff_ofCoordinates (v : Fin n → R[X]) (k : ℕ) (i : Fin n) :
    (ofCoordinates v).coeff k i = (v i).coeff k := by
  classical
  simp [ofCoordinates, coeff_sum, Finsupp.finsetSum_apply, smul_single_apply,
    Finset.sum_apply, Pi.single_apply]

/-- Extend a coordinate vector from R to an R-algebra S. -/
def mapVector (S : Type*) [CommRing S] [Algebra R S] : (Fin n → R) →ₗ[R] (Fin n → S) :=
  LinearMap.pi fun i => (Algebra.linearMap R S).comp (LinearMap.proj i)

@[simp] theorem mapVector_apply (S : Type*) [CommRing S] [Algebra R S]
    (v : Fin n → R) (i : Fin n) : mapVector S v i = algebraMap R S (v i) := rfl

/-- Evaluation after extending vector coefficients to S agrees with coordinate evaluation. -/
theorem eval_ofCoordinates (S : Type*) [CommRing S] [Algebra R S]
    (v : Fin n → R[X]) (a : S) (i : Fin n) :
    eval a (map S (mapVector S) (ofCoordinates v)) i =
      (v i).eval₂ (algebraMap R S) a := by
  classical
  simp [ofCoordinates, map_smul, eval_smul, Finset.sum_apply, Pi.single_apply,
    Polynomial.eval_map]

/-- The degree of a module-valued polynomial: the largest exponent with a
nonzero coefficient vector. The zero polynomial has degree ⊥. -/
noncomputable def degree {M : Type*} [AddCommGroup M] [Module R M]
    (q : PolynomialModule R M) : WithBot ℕ :=
  q.coeff.support.sup fun k => (k : WithBot ℕ)

end PolynomialModule
