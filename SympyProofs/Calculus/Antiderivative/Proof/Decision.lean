module

public import SympyProofs.Calculus.Antiderivative.Program.Decision
public import SympyProofs.Calculus.Antiderivative.Proof.Kind.Coefficients
public import SympyProofs.Calculus.Antiderivative.Proof.Logarithmic

/-! The two generator admissibility decisions and the joint specification of a level. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

/-- All decisions that a tower of height one greater needs from the current level. -/
structure Level.Spec (t : Tower R n) (L : Level R n) : Prop where
  /-- A successful integral is regular and correct, and failure excludes a Liouville form. -/
  integrate : L.IntegrateSpec k t
  /-- Parametric elementary integrals give precisely the elementary combinations. -/
  elementaryBasis : L.ElementaryBasisSpec k t
  /-- The solution generators and rows describe every solution of the parametric equation. -/
  solve : L.SolveSpec k t
  /-- Rational rows precisely describe saturated logarithmic derivatives. -/
  logarithmic : L.LogRelationsSpec k t

/-- The level of the constant field satisfies all four specifications. -/
theorem baseLevel_spec [CharZero k] [IntegerRelations (K R 0)] [LawfulIntegerRelations (K R 0)] :
    (baseLevel R).Spec k .base :=
  ⟨baseLevel_integrate_spec k, baseLevel_elementaryBasis_spec k, baseLevel_solve_spec k,
    baseLevel_logRelations_spec k⟩

/-- Given correct decisions over the lower field, checking a generator is equivalent to
preservation of the constants at a primitive or exponential step. -/
theorem ReducedGen.check_iff (t : Tower R n) (L : Level R n) (h : L.Spec k t)
    (g : ReducedGen (K R n)) :
    g.check t.D L = true ↔ g.Admissible k t := by
  cases g with
  | exp u => exact L.expOk_iff k t h.logarithmic u
  | prim b =>
    cases he : L.rde 0 b with
    | none =>
      have hn := Level.rde_complete k h.solve he
      simpa [check, he, Admissible] using hn
    | some y =>
      have hy := Level.rde_sound k h.solve he
      have hex : ∃ z, t.modelD k z = val k b := ⟨val k y, by simpa using hy⟩
      simp [check, he, Admissible, hex]

end SympyProofs.Calculus.Antiderivative
