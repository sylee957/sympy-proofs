module

public import SympyProofs.Calculus.Antiderivative.Spec.Value
public import SympyProofs.Calculus.Antiderivative.Program.Tower

/-! The model derivation is determined by the constant field and the velocities of the variables. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable (k : Type) [Field k] {n : ℕ}

private theorem val_self [DecidableEq k] (x : K k n) : val k x = K.equiv x := by
  obtain ⟨a, b, _, hx⟩ := IsFractionRing.div_surjective (MPoly n k) x
  change K.ofPoly a / K.ofPoly b = x at hx
  rw [← hx]
  simp [map_div₀, MvPolynomial.map_id]

namespace Model

/-- A derivation of a field over the integers, using its canonical integer action. -/
abbrev Der (F : Type*) [Field F] := Derivation ℤ F F

/-- Transport a field derivation across a ring isomorphism. -/
def transport {F G : Type*} [Field F] [Field G] (e : F ≃+* G) (D : Der F) : Der G :=
  let f := e.toAddMonoidHom.toIntLinearMap ∘ₗ D.toLinearMap ∘ₗ e.symm.toAddMonoidHom.toIntLinearMap
  Derivation.mk' f fun x y => by
    change e (D (e.symm (x * y))) = x * e (D (e.symm y)) + y * e (D (e.symm x))
    simp [Derivation.leibniz]

/-- The model derivative, bundled with its additive and Leibniz laws. -/
noncomputable def derivation (v : List (M k n)) : Der (M k n) := by
  classical
  let e : K k n ≃+* M k n := K.equiv
  exact transport e (K.derivation (v.map e.symm))

/-- Bundling the model derivative preserves its weighted quotient-rule formula. -/
theorem derivation_apply (v : List (M k n)) (x : M k n) :
    derivation k v x = der k v x := by
  classical
  let e : K k n ≃+* M k n := K.equiv
  change e (K.der (v.map e.symm) (e.symm x)) = _
  rw [← val_self k, val_der]
  simp [val_self, List.map_map, e, Function.comp_def]

/-- The value of a polynomial in the model field. -/
noncomputable abbrev polynomial (p : MvPolynomial (Fin n) k) : M k n := algebraMap _ _ p

/-- The model derivative on a polynomial agrees with formal partial differentiation. -/
theorem pderiv_polynomial (i : Fin n) (p : MvPolynomial (Fin n) k) :
    pderiv k i (polynomial k p) = polynomial k (MvPolynomial.pderiv i p) := by
  simpa [K.quotientRule, polynomial] using pderiv_div k i p 1

private theorem partial_C (i : ℕ) (a : k) :
    pderiv k i (polynomial k (MvPolynomial.C a) : M k n) = 0 := by
  by_cases h : i < n
  · rw [pderiv_polynomial k (⟨i, h⟩ : Fin n)]
    simp
  · simp [pderiv, h]

/-- The model derivative vanishes on coefficients. -/
@[simp] theorem derivation_C (v : List (M k n)) (a : k) :
    derivation k v (polynomial k (MvPolynomial.C a)) = 0 := by
  rw [derivation_apply, der]
  generalize v.take n = w
  suffices ∀ i, weightedPartials k (polynomial k (MvPolynomial.C a)) i w = 0 from this 0
  induction w with
  | nil => simp [weightedPartials]
  | cons b bs ih => simp [weightedPartials, partial_C, ih]

private theorem partial_X (i : ℕ) (j : Fin n) :
    pderiv k i (polynomial k (MvPolynomial.X j)) = if i = j.val then 1 else 0 := by
  by_cases h : i < n
  · let l : Fin n := ⟨i, h⟩
    rw [pderiv_polynomial k l, MvPolynomial.pderiv_X]
    by_cases e : i = j.val
    · have eq : l = j := Fin.ext e
      simp [eq, e, polynomial]
    · have ne : l ≠ j := fun h => e (congrArg Fin.val h)
      simp [Ne.symm ne, e, polynomial]
  · have ne : i ≠ j.val := fun h' => h (h' ▸ j.isLt)
    simp [pderiv, h, ne]

/-- The derivative of a generator is its prescribed velocity, or zero for a missing entry. -/
theorem derivation_X (v : List (M k n)) (j : Fin n) :
    derivation k v (polynomial k (MvPolynomial.X j)) = v.getD j 0 := by
  have hw (w : List (M k n)) (i : ℕ) :
      weightedPartials k (polynomial k (MvPolynomial.X j)) i w =
        if i ≤ j.val then w.getD (j.val - i) 0 else 0 := by
    induction w generalizing i with
    | nil => simp [weightedPartials]
    | cons a w ih =>
      rw [weightedPartials, partial_X, ih]
      by_cases he : i = j.val
      · simp [he]
      · by_cases hl : i < j.val
        · have e : j.val - i = (j.val - (i + 1)) + 1 := by omega
          simp [he, hl.le, Nat.succ_le_of_lt hl, e]
        · simp [he, show ¬ i ≤ j.val by omega, show ¬ i + 1 ≤ j.val by omega]
  simp [derivation_apply, der, hw, List.getD, j.isLt]

end Model

end SympyProofs.Calculus.Antiderivative

namespace SympyProofs.Calculus.Antiderivative.Tower

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

/-- The derivation of a tower in a model with larger coefficients. -/
noncomputable def modelD (t : Tower R n) : Model.Der (M k n) :=
  Model.derivation k (t.gens.map (val k))

/-- Interpreting a computed tower derivative gives the corresponding model derivative. -/
@[simp] theorem val_D (t : Tower R n) (x : K R n) :
    val k (t.D x) = t.modelD k (val k x) := by
  rw [modelD, Model.derivation_apply]
  exact val_der k t.gens x

/-- The polynomial velocity of the newest generator in the last-variable presentation. -/
noncomputable def modelVelocity (t : Tower R n) : Gen (K R n) → Polynomial (M k n)
  | .prim b => Polynomial.C (val k b)
  | .exp u => Polynomial.C (val k (t.D u)) * Polynomial.X
  | .tan u => Polynomial.C (val k (t.D u)) * (1 + Polynomial.X ^ 2)

end SympyProofs.Calculus.Antiderivative.Tower
