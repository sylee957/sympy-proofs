module

public import SympyProofs.Calculus.Antiderivative.Program.Integrate
public import SympyProofs.Calculus.Antiderivative.Proof.DecisionLevel
public import SympyProofs.Calculus.Antiderivative.Proof.Operations
public import SympyProofs.Calculus.Antiderivative.Proof.Verify

/-! Soundness and completeness of the public integration and parametric solving operations. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n : ℕ}

variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k]

variable [CharZero k] [IsAlgClosed k]
variable [NatBound (K R 0)] [LawfulNatBound (K R 0)]
variable [IntegerRelations (K R 0)] [LawfulIntegerRelations (K R 0)]
variable [ConstantFactors (K R 0)] [LawfulConstantFactors (K R 0)]

variable [Decidable (IsSquare (-1 : K R 0))]

/-- The tower operations satisfy their joint differential-field specification. -/
theorem Tower.operations_spec (t : Tower R n) : t.operations.Spec k t := by
  by_cases hf : t.TangentFree
  · rw [operations, dite_eq_left hf]
    exact ⟨t.checkSteps_iff k hf, fun ht => (t.level_spec k hf ht).integrate,
      fun ht => (t.level_spec k hf ht).solve⟩
  · exact t.operations_of_tangent k hf

/-- The native admissibility test decides preservation of the model constant field. -/
theorem Tower.admissible_iff (t : Tower R n) : t.admissible = true ↔ t.Admissible k :=
  (t.operations_spec k).admissible

/-- Every positive decision on an admissible tower returns a regular primitive of the input. -/
theorem integrate_sound {t : Tower R n} (ht : t.Admissible k) {f : K R n} {a : Answer R n}
    (h : integrate t f = .elementary a) : a.Regular k ∧ a.deriv k t = val k f := by
  have hs := (t.operations_spec k).integrate ht f
  change t.operations.integrate f = .elementary a at h
  rwa [h] at hs

/-- Every negative decision on an admissible tower excludes an elementary primitive. -/
theorem integrate_complete {t : Tower R n} (ht : t.Admissible k) {f : K R n}
    (h : integrate t f = .nonelementary) : ¬ t.Elementary k (val k f) := by
  have hs := (t.operations_spec k).integrate ht f
  change t.operations.integrate f = .nonelementary at h
  rwa [h] at hs

/-- Exact differentiation recovers the input from each elementary answer on an admissible tower. -/
theorem integrate_differentiate {t : Tower R n} (ht : t.Admissible k) {f : K R n} {a : Answer R n}
    (h : integrate t f = .elementary a) : a.differentiate t = some f := by
  obtain ⟨hr, hd⟩ := integrate_sound k ht h
  exact (a.differentiate_eq_some_iff k t hr f).mpr hd

/-- The solver describes every solution for each model parameter vector in the tower. -/
theorem solve_spec {t : Tower R n} (ht : t.Admissible k) (f : K R n) (gs : List (K R n))
    (y : M k n) (c : List k) (hc : c.length = gs.length) :
    t.modelD k y + val k f * y = Model.linearCombination k c gs ↔
      ∃ d : List k, d.length = (solve t f gs).1.length ∧
        y = Model.linearCombination k d (solve t f gs).1 ∧
        ∀ r ∈ (solve t f gs).2, Model.rowHolds k r (c ++ d) :=
  (t.operations_spec k).solve ht f gs y c hc

end SympyProofs.Calculus.Antiderivative
