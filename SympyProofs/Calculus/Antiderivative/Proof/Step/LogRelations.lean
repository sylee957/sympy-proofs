module

public import SympyProofs.Calculus.Antiderivative.Program.Step.LogRelations
public import SympyProofs.Calculus.Antiderivative.Proof.Linear
public import SympyProofs.Calculus.Antiderivative.Spec.IntegerRelations
public import Mathlib.Algebra.Polynomial.RingDivision

/-! Divisibility certificates for saturated rational logarithmic residues. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

namespace Linear

private theorem dot_swap (xs ys : List ℚ) : dot xs ys = dot ys xs := by
  induction xs generalizing ys with
  | nil => simp [dot]
  | cons x xs ih =>
    cases ys with
    | nil => simp [dot]
    | cons y ys => simpa [dot, mul_comm] using congrArg (y * x + ·) (ih ys)

/-- The rational dot product restricted to the given number of coordinates. -/
private def atWidth (m : ℕ) (q r : List ℚ) : ℚ :=
  functional (RingHom.id ℚ) m r (vector (RingHom.id ℚ) m q)

private theorem dot_vector (q r : List ℚ) :
    dot q r = atWidth q.length q r := by
  rw [dot_swap]
  exact map_dot (RingHom.id ℚ) r q

/-- Elimination removes exactly one existential rational coefficient from a list of rows. -/
theorem eliminate_dot_iff {m : ℕ} (rows : List (List ℚ)) (q : List ℚ) (hq : q.length = m) :
    (∀ r ∈ eliminate m rows, dot q r = 0) ↔ ∃ a : ℚ, ∀ r ∈ rows, dot (q ++ [a]) r = 0 := by
  simp only [dot_vector, List.length_append, List.length_singleton, hq]
  unfold atWidth
  rw [eliminate_spec]
  simp [vector_append _ _ hq]

end Linear

namespace Step

open scoped Polynomial

variable {F : Type} [Field F] [DecidableEq F]

/-- The model polynomial of a rational linear combination of numerators. -/
noncomputable def rationalPolynomial : List ℚ → List (Poly F) → F[X]
  | c :: cs, a :: as => Polynomial.C (c : F) * Poly.equiv a + rationalPolynomial cs as
  | _, _ => 0

omit [DecidableEq F] in
theorem scalar_mod (c : F) (a p : F[X]) :
    Polynomial.C c * a % p = Polynomial.C c * (a % p) := by
  simp only [Polynomial.mod_def, ← Polynomial.smul_eq_C_mul, Polynomial.smul_modByMonic]

private theorem coeff_remainder (q : List ℚ) (as : List (Poly F)) (p : Poly F) (j : ℕ) :
    (rationalPolynomial q as % Poly.equiv p).coeff j =
      rationalCombination q ((as.map (· % p)).map (·.coeff j)) := by
  induction q generalizing as with
  | nil => simp [rationalPolynomial, rationalCombination]
  | cons c q ih =>
    cases as with
    | nil => simp [rationalPolynomial, rationalCombination]
    | cons a as =>
      simpa [rationalPolynomial, rationalCombination, Polynomial.add_mod, scalar_mod,
        ← Poly.equiv_mod] using congrArg ((c : F) * (a % p).coeff j + ·) (ih as)

private theorem rationalPolynomial_append (q : List ℚ) (as : List (Poly F)) (r : ℚ) (ds : Poly F)
    (hq : q.length = as.length) :
    rationalPolynomial (q ++ [r]) (as ++ [-ds]) =
      rationalPolynomial q as - Polynomial.C (r : F) * Poly.equiv ds := by
  induction q generalizing as with
  | nil =>
    obtain rfl : as = [] := List.length_eq_zero_iff.mp hq.symm
    simp [rationalPolynomial]
  | cons c q ih =>
    cases as with
    | nil => simp at hq
    | cons a as =>
      simp only [List.length_cons, Nat.succ.injEq] at hq
      simp [rationalPolynomial, ih as hq, add_sub_assoc]

/-- The extended system cuts out the condition that the rational residue at this factor
equals the supplied rational number. -/
theorem residueEquations_spec (relations : List F → List (List ℚ))
    (hrel : ∀ xs q, (∀ r ∈ relations xs, Linear.dot q r = 0) ↔ rationalCombination q xs = 0)
    (p ds : Poly F) (as : List (Poly F)) (q : List ℚ) (u : ℚ)
    (hp : p.natDegree ≠ 0) (hlen : q.length = as.length) :
    (∀ r ∈ residueEquations relations p ds as, Linear.dot (q ++ [u]) r = 0) ↔
      Poly.equiv p ∣ rationalPolynomial q as - Polynomial.C (u : F) * Poly.equiv ds := by
  simp only [residueEquations, List.forall_mem_flatMap, List.mem_range, hrel, ← coeff_remainder,
    rationalPolynomial_append q as u ds hlen, ← EuclideanDomain.mod_eq_zero]
  constructor
  · intro h
    ext i
    by_cases hi : i < p.natDegree
    · simpa using h i hi
    · exact (Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le
        (Polynomial.natDegree_mod_lt _ (by simpa using hp))
        (by simpa using Nat.le_of_not_lt hi))).trans
          (Polynomial.coeff_zero _).symm
  · intro h
    simp [h]

/-- The factored rows hold exactly when every supplied factor admits a rational residue.
For an irreducible normal factor of a squarefree denominator, the residue is unique. -/
theorem factoredResidueRows_spec (relations : List F → List (List ℚ))
    (hrel : ∀ xs q, (∀ r ∈ relations xs, Linear.dot q r = 0) ↔ rationalCombination q xs = 0)
    (factors : List (Poly F)) (ds : Poly F) (as : List (Poly F)) (q : List ℚ)
    (hp : ∀ p ∈ factors, p.natDegree ≠ 0) (hlen : q.length = as.length) :
    (∀ r ∈ factoredResidueRows relations factors ds as, Linear.dot q r = 0) ↔
      ∀ p ∈ factors, ∃ u : ℚ, Poly.equiv p ∣
        rationalPolynomial q as - Polynomial.C (u : F) * Poly.equiv ds := by
  simp only [factoredResidueRows, List.forall_mem_flatMap]
  exact forall_congr' fun p => forall_congr' fun h =>
    (Linear.eliminate_dot_iff _ _ hlen).trans (exists_congr fun u =>
      residueEquations_spec relations hrel p ds as q u (hp p h) hlen)

end Step

end SympyProofs.Calculus.Antiderivative
