module

public import SympyProofs.Calculus.Antiderivative.Program.Level
public import SympyProofs.Calculus.Antiderivative.Spec.Derivation
public import SympyProofs.Calculus.Antiderivative.Algebra.K.Constants
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.Pi

/-! Semantics of returned primitives and linear descriptions of the parametric equation. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

/-- Embed a coefficient of the model in its rational function field. -/
noncomputable def Model.C (n : ℕ) : k →+* M k n :=
  (algebraMap (MvPolynomial (Fin n) k) _).comp MvPolynomial.C

/-- Interpret the computable constant field in the scalar field of the model. -/
noncomputable def Model.constantHom : K R 0 →+* k :=
  (K.modelConstantsEquiv (R := k) k).toRingHom.comp (val k)

/-- The height-zero model isomorphism recovers a scalar from its constant polynomial. -/
@[simp] theorem Model.modelConstantsEquiv_C (c : k) :
    K.modelConstantsEquiv (R := k) k (Model.C k 0 c) = c := by
  change K.modelConstantsEquiv (R := k) k (algebraMap (MvPolynomial (Fin 0) k) _
    (MvPolynomial.C c)) = _
  rw [K.modelConstantsEquiv, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simp only [← MvPolynomial.isEmptyRingEquiv_symm_apply, RingEquiv.apply_symm_apply,
    Algebra.algebraMap_self_apply]

@[simp] theorem Model.includeVars_C {m : ℕ} (h : n ≤ m) (c : k) :
    includeVars h (C k n c) = C k m c := by simp [C]

/-- Reading a constant as a scalar and including it at height zero recovers its model value. -/
theorem Model.C_zero_constantHom (c : K R 0) : C k 0 (constantHom k c) = val k c :=
  (K.modelConstantsEquiv (R := k) k).injective (modelConstantsEquiv_C k _)

/-- Scalar inclusion and the tower's inclusion of its computable constants agree. -/
theorem Model.C_constantHom (c : K R 0) :
    C k n (constantHom k c) = val k (K.ofConst c : K R n) := by
  rw [val_ofConst, ← C_zero_constantHom k c, includeVars_C]

/-- The polynomial in the model's constants defining a logarithmic root sum. -/
noncomputable def RootSum.modelModulus (s : RootSum R n) : Polynomial k :=
  (Poly.equiv s.modulus).map (Model.constantHom k)

/-- The logarithmic argument evaluated at a constant root. -/
noncomputable def RootSum.argAt (s : RootSum R n) (c : k) : M k n :=
  (Poly.equiv s.arg).eval₂ (val k) (Model.C k n c)

/-- The logarithmic arguments of the root sum are nonzero at every root of its modulus. -/
def RootSum.Regular (s : RootSum R n) : Prop :=
  s.modelModulus k ≠ 0 ∧ ∀ c, (s.modelModulus k).IsRoot c → s.argAt k c ≠ 0

/-- Every logarithm in the returned primitive has a defined argument. -/
def Answer.Regular (a : Answer R n) : Prop := ∀ s ∈ a.sums, s.Regular k

section

variable {S : Type} [CommRing S] [IsDomain S] [DecidableEq S] [NormalizedGCDMonoid S] [Div S]
variable [Algebra S k] [FaithfulSMul S k]

/-- Evaluate the weighted logarithmic derivative using a derivation of the model field. -/
noncomputable def RootSum.derivWith (D : Model.Der (M k n)) (s : RootSum S n) : M k n := by
  classical
  exact val k (K.ofConst s.weight) * ∑ c ∈ (s.modelModulus k).roots.toFinset,
    Model.C k n c * (D (s.argAt k c) / s.argAt k c)

/-- Interpret a logarithmic sum under the supplied generator velocities. -/
noncomputable def RootSum.derivAlong (v : List (K R n)) (s : RootSum S n) : M k n :=
  delta% s.derivWith k (Model.derivation k (v.map (val k)))

/-- The derivative of a logarithmic sum, one contribution per distinct root. -/
noncomputable def RootSum.deriv (t : Tower R n) (s : RootSum S n) : M k n :=
  delta% s.derivWith k (t.modelD k)

/-- Add the derivative of the field term to the contributions of the logarithmic sums. -/
noncomputable def Answer.sumDerivatives (D : Model.Der (M k n))
    (rootDerivative : RootSum S n → M k n) (a : Answer S n) : M k n :=
  D (val k a.field) + (a.sums.map rootDerivative).sum

/-- Interpret an answer under the supplied generator velocities. -/
noncomputable def Answer.derivAlong (v : List (K R n)) (a : Answer S n) : M k n :=
  delta% a.sumDerivatives k (Model.derivation k (v.map (val k))) (RootSum.derivAlong k v)

/-- The derivative of the field term and all logarithmic root sums of an answer. -/
noncomputable def Answer.deriv (t : Tower R n) (a : Answer S n) : M k n :=
  delta% a.sumDerivatives k (t.modelD k) (RootSum.deriv k t)

end

/-- A Liouville form consists of a field derivative and finitely many logarithmic derivatives. -/
def Tower.Elementary (t : Tower R n) (f : M k n) : Prop :=
  ∃ (x : M k n) (logs : List (k × M k n)),
    f = t.modelD k x + (logs.map fun (c, u) => Model.C k n c * (t.modelD k u / u)).sum

/-- A linear combination of computed elements with coefficients in the model's constant field. -/
noncomputable def Model.linearCombination : List k → List (K R n) → M k n
  | c :: cs, g :: gs => C k n c * val k g + linearCombination cs gs
  | _, _ => 0

/-- A homogeneous row is satisfied by the specified list of model coefficients. -/
def Model.rowHolds (row : List (K R 0)) (c : List k) : Prop := linearCombination k c row = 0

/-- The returned generators and rows describe precisely the solutions over the model field. -/
def Tower.SolveSpec (t : Tower R n)
    (solve : K R n → List (K R n) → List (K R n) × List (List (K R 0))) : Prop :=
  ∀ (f : K R n) (gs : List (K R n)) (y : M k n) (c : List k), c.length = gs.length →
    (t.modelD k y + val k f * y = Model.linearCombination k c gs ↔
      ∃ d : List k, d.length = (solve f gs).1.length ∧
        y = Model.linearCombination k d (solve f gs).1 ∧
        ∀ row ∈ (solve f gs).2, Model.rowHolds k row (c ++ d))

/-- The solver at a tower level represents the complete parametric solution space. -/
abbrev Level.SolveSpec (t : Tower R n) (L : Level R n) : Prop := t.SolveSpec k L.solve

/-- Each returned direction has a regular primitive. Their scalar extensions span exactly
the coefficient vectors whose input combinations admit Liouville forms. -/
def Level.ElementaryBasisSpec (t : Tower R n) (L : Level R n) : Prop :=
  ∀ gs : List (K R n),
    (∀ w ∈ L.elementaryBasis gs, w.1.length = gs.length ∧ w.2.Regular k ∧
      w.2.deriv k t = Model.linearCombination k (w.1.map (Model.constantHom k)) gs) ∧
    ∀ cs : List k, cs.length = gs.length →
      (t.Elementary k (Model.linearCombination k cs gs) ↔
        (fun i : Fin cs.length => cs.getD i 0) ∈ Submodule.span k
          ((fun (r : List (K R 0)) (i : Fin cs.length) => Model.constantHom k (r.getD i 0)) ''
            {r | r ∈ (L.elementaryBasis gs).map Prod.fst}))

/-- Either a regular answer differentiates to the input or the input lacks a Liouville form. -/
def Tower.IntegrateSpec (t : Tower R n) (integrate : K R n → Result R n) : Prop :=
  ∀ f, match integrate f with
    | .elementary a => a.Regular k ∧ a.deriv k t = val k f
    | .nonelementary => ¬ t.Elementary k (val k f)

/-- Integration at a tower level returns a sound elementary or nonelementary decision. -/
abbrev Level.IntegrateSpec (t : Tower R n) (L : Level R n) : Prop :=
  t.IntegrateSpec k L.integrate

end SympyProofs.Calculus.Antiderivative
