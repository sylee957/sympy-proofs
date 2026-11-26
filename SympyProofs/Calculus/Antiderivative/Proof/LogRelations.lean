module

public import SympyProofs.Calculus.Antiderivative.Program.LogRelations
public import SympyProofs.Calculus.Antiderivative.Proof.Coefficients
public import SympyProofs.Calculus.Antiderivative.Proof.Step.LogRelations

/-! Rational combination rows for the tower and for a list of normal denominator factors. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [IntegerRelations (K R 0)] [LawfulIntegerRelations (K R 0)] {n : ℕ}

omit [IntegerRelations (K R 0)] [LawfulIntegerRelations (K R 0)] in
private theorem rationalCombination_model (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k]
    (q : List ℚ) (xs : List (K R n)) :
    Model.linearCombination k (q.map (fun c => (c : k))) xs = val k (rationalCombination q xs) := by
  induction q generalizing xs with
  | nil => simp [Model.linearCombination, rationalCombination]
  | cons c q ih => cases xs with
    | nil => simp [Model.linearCombination, rationalCombination]
    | cons x xs =>
      simpa [Model.linearCombination, rationalCombination] using
        (congrArg (fun z => (c : M k n) * val k x + z) (ih xs))

/-- Splitting polynomial coefficients down the tower and reducing the constant rows to
rational coordinates gives exactly the rational-linear relations between the inputs. -/
theorem rationalRows_spec (xs : List (K R n)) (q : List ℚ) :
    (∀ r ∈ rationalRows xs, Linear.dot q r = 0) ↔ rationalCombination q xs = 0 := by
  let k := FractionRing R
  have h := rowsOf_spec k xs (q.map fun c => (c : k))
  simp only [Model.rowHolds, rationalCombination_model] at h
  simp only [map_eq_zero_iff _ (val_injective k)] at h
  simpa only [rationalRows, List.forall_mem_flatMap, LawfulIntegerRelations.kernel] using h

/-- At each normal irreducible factor, the computed rows require a rational multiple of
the denominator derivative to agree with the combined numerator modulo that factor. -/
theorem factoredResidues_spec (factors : List (Poly (K R n))) (ds : Poly (K R n))
    (as : List (Poly (K R n))) (q : List ℚ)
    (hp : ∀ p ∈ factors, p.natDegree ≠ 0) (hlen : q.length = as.length) :
    (∀ r ∈ factoredResidues factors ds as, Linear.dot q r = 0) ↔
      ∀ p ∈ factors, ∃ u : ℚ, Poly.equiv p ∣
        Step.rationalPolynomial q as - Polynomial.C (u : K R n) * Poly.equiv ds :=
  Step.factoredResidueRows_spec rationalRows rationalRows_spec factors ds as q hp hlen

/-- The primitive step enforces the pole equations, all rational residues at the supplied
factors, and the lower-field logarithmic condition on the constant polynomial part. -/
theorem factoredLogStep_prim (t : Tower R n) (b : K R n)
    (lower : List (K R n) → List (List ℚ))
    (data : LogPoleData (K R n)) (factors : List (Poly (K R n))) (q : List ℚ)
    (hp : ∀ p ∈ factors, p.natDegree ≠ 0) (hlen : q.length = data.numerators.length) :
    (∀ r ∈ factoredLogStep t.D (.prim b) lower data factors, Linear.dot q r = 0) ↔
      (∀ row ∈ data.poleRows, rationalCombination q row = 0) ∧
        (∀ p ∈ factors, ∃ u : ℚ, Poly.equiv p ∣ Step.rationalPolynomial q data.numerators -
          Polynomial.C (u : K R n) * Poly.equiv (Step.polyDer t.D (Poly.C b) data.normalDen)) ∧
        ∀ r ∈ lower data.constants, Linear.dot q r = 0 := by
  simp only [factoredLogStep, List.forall_mem_append, List.forall_mem_flatMap,
    rationalRows_spec, factoredResidues_spec _ _ _ _ hp hlen, and_assoc]

/-- In an exponential step the lower-level condition allows a rational multiple of the
logarithmic derivative of the special generator. -/
theorem factoredLogStep_exp (t : Tower R n) (u : K R n) (lower : List (K R n) → List (List ℚ))
    (data : LogPoleData (K R n)) (factors : List (Poly (K R n))) (q : List ℚ)
    (hp : ∀ p ∈ factors, p.natDegree ≠ 0) (hn : q.length = data.numerators.length)
    (hc : q.length = data.constants.length) :
    (∀ r ∈ factoredLogStep t.D (.exp u) lower data factors, Linear.dot q r = 0) ↔
      (∀ row ∈ data.poleRows, rationalCombination q row = 0) ∧
        (∀ p ∈ factors, ∃ e : ℚ, Poly.equiv p ∣ Step.rationalPolynomial q data.numerators -
          Polynomial.C (e : K R n) *
            Poly.equiv (Step.polyDer t.D (Poly.C (t.D u) * Poly.X) data.normalDen)) ∧
        ∃ e : ℚ, ∀ r ∈ lower (data.constants ++ [t.D u]), Linear.dot (q ++ [e]) r = 0 := by
  simp only [factoredLogStep, List.forall_mem_append, List.forall_mem_flatMap,
    rationalRows_spec, factoredResidues_spec _ _ _ _ hp hn, Linear.eliminate_dot_iff _ _ hc,
    and_assoc]

end SympyProofs.Calculus.Antiderivative
