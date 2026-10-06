import SympyProofs.ComplexRouthHurwitz.Exact.Denotation
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! Gaussian integer coefficients with their complex denotation.
Integer real parts supply pivot comparisons; the Gaussian ring is not ordered.
The runner and its capstones are in `Exact.Basic` and `Exact.Correctness`. -/
namespace RouthHurwitz.ComplexRouth.Exact.Gaussian
open Polynomial

/-- Interpret the input only for semantic statements about complex roots. -/
noncomputable def denote (p : Polynomial GaussianInt) : Polynomial ℂ :=
  p.map GaussianInt.toComplex

theorem denote_ne_zero (p : Polynomial GaussianInt) (hp : p ≠ 0) : denote p ≠ 0 := by
  exact (Polynomial.map_ne_zero_iff GaussianInt.toComplex_injective).mpr hp

theorem denote_natDegree (p : Polynomial GaussianInt) : (denote p).natDegree = p.natDegree :=
  Polynomial.natDegree_map_eq_of_injective GaussianInt.toComplex_injective p

/-- Conjugate normalization is performed in the Gaussian ring. -/
theorem denote_conjugate_product (a b : GaussianInt) :
    GaussianInt.toComplex (a * star b) =
      GaussianInt.toComplex a * star (GaussianInt.toComplex b) :=
  map_conjugate_product GaussianInt.toComplex GaussianInt.toComplex_star a b

/-- Only the real component of a pivot is compared. -/
theorem negative_iff (a : GaussianInt) : a.re < 0 ↔ (GaussianInt.toComplex a).re < 0 := by
  rw [← GaussianInt.intCast_re]
  exact_mod_cast (Iff.rfl : a.re < 0 ↔ a.re < 0)

theorem zero_real_iff (a : GaussianInt) : a.re = 0 ↔ (GaussianInt.toComplex a).re = 0 := by
  rw [← GaussianInt.intCast_re]
  exact_mod_cast (Iff.rfl : a.re = 0 ↔ a.re = 0)

/-- Use the standard Gaussian Euclidean quotient after proving divisibility. -/
theorem denote_exact_quotient (a d : GaussianInt) (hd : d ≠ 0) (ha : d ∣ a) :
    GaussianInt.toComplex (a / d) = GaussianInt.toComplex a / GaussianInt.toComplex d :=
  RouthHurwitz.Exact.map_quotient GaussianInt.toComplex GaussianInt.toComplex_injective a d hd ha

end RouthHurwitz.ComplexRouth.Exact.Gaussian
