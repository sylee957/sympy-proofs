module

public import SympyProofs.Calculus.Antiderivative.Spec.Specialization
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! Complex values of an answer at ordinary points, with locally chosen logarithms. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

open Filter Topology

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [Algebra R ℂ] [FaithfulSMul R ℂ] {n : ℕ}

/-- The distinct complex roots contributing to a logarithmic root sum. -/
noncomputable def RootSum.complexRoots (s : RootSum R n) : Finset ℂ := by
  classical
  exact (s.modelModulus ℂ).roots.toFinset

/-- Evaluate an answer with a specified logarithm for each root of each root sum. -/
noncomputable def Answer.realizeWith (a : Answer R n) (logs : RootSum R n → ℂ → ℂ)
    (p : Fin n → ℂ) : ℂ :=
  Model.evalAt p (val ℂ a.field) + (a.sums.map fun s =>
    Model.constantHom ℂ s.weight * ∑ c ∈ s.complexRoots, c * logs s c).sum

/-- Read an answer using the principal logarithm. -/
noncomputable def Answer.realize (a : Answer R n) (p : Fin n → ℂ) : ℂ :=
  a.realizeWith (fun s c => Complex.log (Model.evalAt p (s.argAt ℂ c))) p

/-- The arguments are regular and each chosen logarithm exponentiates to its argument locally. -/
def Answer.HasLogs (a : Answer R n) (logs : RootSum R n → ℂ → ℂ → ℂ)
    (g : ℂ → Fin n → ℂ) (z : ℂ) : Prop :=
  ∀ s ∈ a.sums, ∀ c ∈ s.complexRoots, Model.RegularAt (g z) (s.argAt ℂ c) ∧
    ContinuousAt (logs s c) z ∧
    ∀ᶠ w in 𝓝 z, Complex.exp (logs s c w) = Model.evalAt (g w) (s.argAt ℂ c)

/-- The field term is regular and the principal logarithm is analytic at every argument. -/
def Answer.RegularAt (a : Answer R n) (p : Fin n → ℂ) : Prop :=
  Model.RegularAt p (val ℂ a.field) ∧ ∀ s ∈ a.sums, ∀ c ∈ s.complexRoots,
    Model.RegularAt p (s.argAt ℂ c) ∧ Model.evalAt p (s.argAt ℂ c) ∈ Complex.slitPlane

end SympyProofs.Calculus.Antiderivative
