module

public import SympyProofs.Calculus.Antiderivative.Proof.IntegrationConsequences
public import SympyProofs.Calculus.Antiderivative.Proof.Analytic.Converse
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Complex primitives of the public integration algorithm in the original coordinates. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [Algebra R ℂ] [FaithfulSMul R ℂ] {n m : ℕ}

variable [NatBound (K R 0)] [LawfulNatBound (K R 0)]
variable [IntegerRelations (K R 0)] [LawfulIntegerRelations (K R 0)]
variable [ConstantFactors (K R 0)] [LawfulConstantFactors (K R 0)]
variable [Decidable (IsSquare (-1 : K R 0))]

/-- A returned answer differentiates to the input function at each regular point of a
complex realization of the primitive, exponential and tangent generators. -/
theorem integrate_hasDerivAt {t : Tower R n} (ht : t.Admissible ℂ) {f : K R n} {a : Answer R n}
    (h : integrate t f = .elementary a) {g : ℂ → Fin n → ℂ} {z : ℂ}
    (hg : t.SolvedBy g z) (ha : a.RegularAt (g z)) :
    HasDerivAt (fun w => a.realize (g w)) (Model.evalAt (g z) (val ℂ f)) z :=
  ((t.operations_spec ℂ).integrate ht).hasDerivAt h hg ha

/-- A negative verdict excludes an analytic primitive written on an independent realization
of any elementary differential extension. Arbitrary continuous logarithm branches are allowed. -/
theorem integrate_no_function_of_independent {t : Tower R n} (ht : t.Admissible ℂ)
    {f : K R n} (h : integrate t f = .nonelementary) {s : Tower R m}
    (hs : s.Admissible ℂ) (inc : n ≤ m) (a : Answer R m) {V : Set ℂ} {G : ℂ → Fin m → ℂ}
    {logs : RootSum R m → ℂ → ℂ → ℂ} (indep : Model.IndependentOn G V)
    (reg : ∀ z ∈ V, s.SolvedBy G z ∧ Model.RegularAt (G z) (Model.includeVars inc (val ℂ f)) ∧
      Model.RegularAt (G z) (val ℂ a.field) ∧ a.HasLogs logs G z) :
    letI : Differential (M ℂ n) := ⟨t.modelD ℂ⟩
    letI : Differential (M ℂ m) := ⟨s.modelD ℂ⟩
    letI : Algebra (M ℂ n) (M ℂ m) := (Model.includeVars inc).toAlgebra
    Extension.LiouvilleForm.ElementaryTower (M ℂ n) (M ℂ m) →
      ¬ ∀ z ∈ V, HasDerivAt (fun w => a.realizeWith (fun b c => logs b c w) (G w))
        (Model.evalAt (G z) (Model.includeVars inc (val ℂ f))) z :=
  t.no_function_of_independent ht (integrate_complete ℂ ht h) hs inc a indep reg

/-- A negative decision excludes analytic primitives on elementary extensions, on each
nonempty open set with regular logarithms and nondegenerate generator functions. -/
theorem integrate_no_function_in_extension {t : Tower R n} (ht : t.Admissible ℂ)
    {f : K R n} (h : integrate t f = .nonelementary) {s : Tower R m}
    (hs : s.Admissible ℂ) (inc : n ≤ m) (a : Answer R m) {V : Set ℂ} (hV : IsOpen V)
    (hn : V.Nonempty) {G : ℂ → Fin m → ℂ} {logs : RootSum R m → ℂ → ℂ → ℂ}
    (reg : ∀ z ∈ V, s.SolvedBy G z ∧ s.Nondegenerate (G z) ∧
      Model.RegularAt (G z) (Model.includeVars inc (val ℂ f)) ∧
      Model.RegularAt (G z) (val ℂ a.field) ∧ a.HasLogs logs G z) :
    letI : Differential (M ℂ n) := ⟨t.modelD ℂ⟩
    letI : Differential (M ℂ m) := ⟨s.modelD ℂ⟩
    letI : Algebra (M ℂ n) (M ℂ m) := (Model.includeVars inc).toAlgebra
    Extension.LiouvilleForm.ElementaryTower (M ℂ n) (M ℂ m) →
      ¬ ∀ z ∈ V, HasDerivAt (fun w => a.realizeWith (fun b c => logs b c w) (G w))
        (Model.evalAt (G z) (Model.includeVars inc (val ℂ f))) z :=
  ((t.operations_spec ℂ).integrate ht).no_function_in_extension ht h hs inc a hV hn reg

end SympyProofs.Calculus.Antiderivative
