module

public import SympyProofs.Sum.Gosper.Algorithm.Algorithm

/-! Correctness of coefficient descent to a nominated coefficient ring. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial

variable {K L : Type} [CommRing K] [CommRing L]

private theorem descendPolynomial_eq_foldlM (descendCoeff : L → Option K) (p : L[X]) :
    descendPolynomial descendCoeff p =
      p.support.toList.foldlM
        (fun q n => (fun a => q + monomial n a) <$> descendCoeff (p.coeff n)) 0 := by
  simp only [descendPolynomial, bind_pure_comp, List.forIn_yield_eq_foldlM, bind_pure]

private theorem descent_fold_sound [Algebra K L] (descendCoeff : L → Option K)
    (hdesc : CoefficientDescentValid descendCoeff) (p : L[X]) (ns : List ℕ)
    (q r : K[X])
    (h : ns.foldlM
      (fun q n => (fun a => q + monomial n a) <$> descendCoeff (p.coeff n)) q = some r) :
    r.map (algebraMap K L) = q.map (algebraMap K L) +
      (ns.map (fun n => monomial n (p.coeff n))).sum := by
  induction ns generalizing q with
  | nil =>
      simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
      simpa using congrArg (Polynomial.map (algebraMap K L)) h.symm
  | cons n ns ih =>
      cases hd : descendCoeff (p.coeff n) with
      | none => simp [List.foldlM_cons, hd] at h
      | some a =>
          have ha := (hdesc (p.coeff n) a).mp hd
          have ht : ns.foldlM
              (fun q n => (fun a => q + monomial n a) <$> descendCoeff (p.coeff n))
              (q + monomial n a) = some r := by
            simpa [List.foldlM_cons, hd] using h
          rw [ih _ ht]
          simp only [Polynomial.map_add, map_monomial, ha, List.map_cons, List.sum_cons,
            add_assoc]

/-- Every successful descent maps back to the original polynomial. -/
theorem descendPolynomial_sound [Algebra K L] (descendCoeff : L → Option K)
    (hdesc : CoefficientDescentValid descendCoeff) (p : L[X]) (q : K[X])
    (h : descendPolynomial descendCoeff p = some q) :
    q.map (algebraMap K L) = p := by
  rw [descendPolynomial_eq_foldlM] at h
  have hs := descent_fold_sound descendCoeff hdesc p p.support.toList 0 q h
  simpa only [Polynomial.map_zero, zero_add, Finset.sum_map_toList, ← as_sum_support] using hs

/-- A polynomial over the smaller coefficient ring is recovered exactly. -/
theorem descendPolynomial_map [Algebra K L] (descendCoeff : L → Option K)
    (hdesc : CoefficientDescentValid descendCoeff) (q : K[X]) :
    descendPolynomial descendCoeff (q.map (algebraMap K L)) = some q := by
  have hcoeff (a : K) : descendCoeff (algebraMap K L a) = some a :=
    (hdesc _ _).mpr rfl
  rw [descendPolynomial_eq_foldlM, support_map_of_injective q hdesc.injective]
  simp only [coeff_map, hcoeff, Option.map_eq_map, Option.map_some]
  rw [show (fun (p : K[X]) (n : ℕ) => some (p + monomial n (q.coeff n))) =
      (fun p n => (pure (p + monomial n (q.coeff n)) : Option K[X])) from rfl,
    List.foldlM_pure, ← List.foldl_map, ← List.sum_eq_foldl, Finset.sum_map_toList,
    ← as_sum_support]
  rfl

/-- Success is equivalent to being the polynomial's preimage under the coefficient embedding. -/
theorem descendPolynomial_eq_some_iff [Algebra K L] (descendCoeff : L → Option K)
    (hdesc : CoefficientDescentValid descendCoeff) (p : L[X]) (q : K[X]) :
    descendPolynomial descendCoeff p = some q ↔ q.map (algebraMap K L) = p := by
  constructor
  · exact descendPolynomial_sound descendCoeff hdesc p q
  · intro h
    rw [← h]
    exact descendPolynomial_map descendCoeff hdesc q

/-- Descent succeeds exactly when every coefficient belongs to the smaller coefficient ring. -/
theorem descendPolynomial_exists_iff [Algebra K L] (descendCoeff : L → Option K)
    (hdesc : CoefficientDescentValid descendCoeff) (p : L[X]) :
    (∃ q, descendPolynomial descendCoeff p = some q) ↔
      p ∈ Polynomial.lifts (algebraMap K L) := by
  simp only [descendPolynomial_eq_some_iff descendCoeff hdesc, Polynomial.mem_lifts]

/-- Failure means there is no polynomial over the nominated coefficient ring mapping to the input. -/
theorem descendPolynomial_eq_none_iff [Algebra K L] (descendCoeff : L → Option K)
    (hdesc : CoefficientDescentValid descendCoeff) (p : L[X]) :
    descendPolynomial descendCoeff p = none ↔
      ¬ ∃ q : K[X], q.map (algebraMap K L) = p := by
  rw [← not_iff_not, not_not]
  simp only [← descendPolynomial_eq_some_iff descendCoeff hdesc, Option.ne_none_iff_exists']

/-- Identity conversion succeeds without changing any coefficient. -/
@[simp] theorem descendPolynomial_self {F : Type} [CommRing F] (p : F[X]) :
    descendPolynomial (some : F → Option F) p = some p := by
  exact (descendPolynomial_eq_some_iff some coefficientDescentValid_self p p).mpr (by simp)

attribute [local instance 2000] Ring.toIntAlgebra

/-- Over the same field, identity descent always succeeds. -/
theorem gosperTerm_self {F : Type} [Field F] [CharZero F] [DecidableEq F]
    [DecidablePred (IsLocalization.IsInteger ℤ : F → Prop)]
    (backend : Backend F) (P Q : F[X]) :
    gosperTerm (TermBackend.self backend) P Q = .ok (
      let normal := gosperNormal backend.toNormalization P Q
      gosperSolve backend.toLinear normal.1 (taylor (-1) normal.2.1) normal.2.2) := by
  simp only [gosperTerm, TermBackend.self, descendPolynomial_self]
  generalize gosperSolve (L := F) backend.toLinear _ _ _ = result
  cases result <;> rfl

end Gosper.Algorithm
