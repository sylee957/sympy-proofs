module

public import SympyProofs.Calculus.Antiderivative.Spec.Derivation
public import SympyProofs.Calculus.Antiderivative.Proof.Tower
public import SympyProofs.Calculus.Antiderivative.Extension.Derivation

/-! In the last-variable presentation, the tower derivative is the ordinary extension of the
derivative below by the polynomial velocity of the newest generator. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Model

variable {F : Type} [Field F]

/-- Extend a field derivation to rational functions by specifying the derivative of `X`. -/
noncomputable def extendVariable (D : Der F) (v : Polynomial F) : Der (RatFunc F) :=
  letI : Differential F := ⟨D⟩
  Extension.extend (Differential.implicitDeriv v)

@[simp] theorem extendVariable_C (D : Der F) (v : Polynomial F) (a : F) :
    extendVariable D v (RatFunc.C a) = RatFunc.C (D a) := by
  let _ : Differential F := ⟨D⟩
  rw [extendVariable, ← RatFunc.algebraMap_C, Extension.extend_poly, Differential.implicitDeriv_C,
    RatFunc.algebraMap_C]
  rfl

@[simp] theorem extendVariable_X (D : Der F) (v : Polynomial F) :
    extendVariable D v RatFunc.X = algebraMap _ _ v := by
  let _ : Differential F := ⟨D⟩
  rw [extendVariable, ← RatFunc.algebraMap_X, Extension.extend_poly, Differential.implicitDeriv_X]

variable (k : Type) [Field k] {n : ℕ}

/-- A field map preserves derivatives if it does so on the coefficients and generators. -/
theorem map_derivation (h : M k n →+* F) (v : List (M k n)) (E : Der F)
    (hC : ∀ c, E (h (polynomial k (MvPolynomial.C c))) = 0)
    (hX : ∀ j : Fin n, E (h (polynomial k (MvPolynomial.X j))) = h (v.getD j 0))
    (x : M k n) : E (h x) = h (derivation k v x) := by
  have hp (p : MvPolynomial (Fin n) k) :
      E (h (polynomial k p)) = h (derivation k v (polynomial k p)) := by
    induction p using MvPolynomial.induction_on with
    | C a => rw [hC, derivation_C, map_zero]
    | add a b ha hb => simp only [polynomial, map_add] at *; rw [ha, hb]
    | mul_X a j ha =>
      have hj := hX j
      rw [← derivation_X] at hj
      simp only [polynomial, map_mul, Derivation.leibniz, smul_eq_mul, map_add] at *
      rw [ha, hj]
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin n) k) x
  simp only [map_div₀, Derivation.leibniz_div, smul_eq_mul, map_mul, map_sub, map_pow, map_inv₀]
  rw [hp a, hp b]

/-- Old variables become constants under the last-variable presentation. -/
theorem stepEquiv_includeVars (x : M k n) :
    stepEquiv k n (includeVars (Nat.le_succ n) x) = RatFunc.C x := by
  classical
  obtain ⟨y, rfl⟩ := (K.equiv (R := k) (n := n)).surjective x
  rw [← K.equiv_lift, K.stepEquiv_lift]

private theorem stepEquiv_constant (a : k) :
    stepEquiv k n (polynomial k (MvPolynomial.C a)) =
      RatFunc.C (polynomial k (MvPolynomial.C a)) := by
  rw [← stepEquiv_includeVars]
  congr 1
  simp [polynomial]

/-- Adjoining one variable gives the rational-function derivative with the chosen velocity. -/
theorem stepEquiv_derivation (v : List (M k n)) (hv : v.length = n) (w : M k (n + 1))
    (u : Polynomial (M k n)) (hu : stepEquiv k n w = algebraMap _ _ u) (x : M k (n + 1)) :
    stepEquiv k n (derivation k (v.map (includeVars (Nat.le_succ n)) ++ [w]) x) =
      extendVariable (derivation k v) u (stepEquiv k n x) := by
  symm
  apply map_derivation k (stepEquiv k n).toRingHom
  · intro a
    simp [stepEquiv_constant]
  · intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [polynomial, List.getD, hv, hu]
    · simp [polynomial, derivation_X, List.getD, hv, stepEquiv_includeVars]

end SympyProofs.Calculus.Antiderivative.Model

namespace SympyProofs.Calculus.Antiderivative.Tower

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

/-- In the one-variable field a tower step extends the lower derivation by its generator law. -/
theorem stepEquiv_modelD (t : Tower R n) (g : Gen (K R n))
    (x : M k (n + 1)) :
    Model.stepEquiv k n ((t.step g).modelD k x) =
      Model.extendVariable (t.modelD k) (t.modelVelocity k g) (Model.stepEquiv k n x) := by
  let v := t.gens.map (val k)
  let w := val k ((t.step g).D K.gen)
  have hvel : (t.step g).gens.map (val k) =
      v.map (Model.includeVars (Nat.le_succ n)) ++ [w] := by
    cases g <;> simp only [gens, v, w, D_gen_prim, D_gen_exp, D_gen_tan, List.map_append,
      List.map_cons, List.map_nil, List.map_map, Function.comp_def, val_lift] <;> rfl
  rw [modelD, hvel]
  apply Model.stepEquiv_derivation k v (by simp [v]) w
  cases g <;> simp [w, modelVelocity, -val_D, Model.stepEquiv_includeVars]

end SympyProofs.Calculus.Antiderivative.Tower
