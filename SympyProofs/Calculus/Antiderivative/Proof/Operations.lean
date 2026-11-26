module

public import SympyProofs.Calculus.Antiderivative.Proof.TangentOperations
public import SympyProofs.Calculus.Antiderivative.Proof.TangentUnit
public import SympyProofs.Calculus.Antiderivative.Proof.Trigonometric.Admissible
public import SympyProofs.Calculus.Antiderivative.Proof.TrigonometricDescent.Answer
public import SympyProofs.Calculus.Antiderivative.Proof.TrigonometricDescent.Solve

/-! The joint integration and solver contract survives a change of tangent coordinates. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

open Trigonometric

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n : ℕ}
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k]

/-- The level decisions in caller coordinates, including the exact test for admissibility. -/
structure Operations.Spec (t : Tower R n) (ops : Operations R n) : Prop where
  admissible : ops.admissible.get = true ↔ t.Admissible k
  integrate : t.Admissible k → t.IntegrateSpec k ops.integrate
  solve : t.Admissible k → t.SolveSpec k ops.solve

private theorem spec_of_checked (t : Tower R n) (ops : Operations R n)
    (test : ops.admissible.get = true ↔ t.Admissible k)
    (dec : K R n → Option (Result R n))
    (eqs : K R n → List (K R n) → Option (List (K R n) × List (List (K R 0))))
    (hi : ∀ f, ops.admissible.get = true → dec f = some (ops.integrate f))
    (hs : ∀ f gs, ops.admissible.get = true → eqs f gs = some (ops.solve f gs))
    (pos : ∀ f a, dec f = some (.elementary a) → a.Regular k ∧ a.deriv k t = val k f)
    (neg : ∀ f, dec f = some .nonelementary → ¬ t.Elementary k (val k f))
    (sol : ∀ f gs out, eqs f gs = some out → ∀ y c, List.length c = List.length gs →
      (t.modelD k y + val k f * y = Model.linearCombination k c gs ↔
        ∃ d : List k, d.length = out.1.length ∧ y = Model.linearCombination k d out.1 ∧
          ∀ row ∈ out.2, Model.rowHolds k row (c ++ d))) : ops.Spec k t := by
  refine ⟨test, ?_, ?_⟩
  · intro ht f
    have h := hi f (test.mpr ht)
    cases e : ops.integrate f with
    | elementary a => exact pos f a (e ▸ h)
    | nonelementary => exact neg f (e ▸ h)
  · intro ht f gs
    exact sol f gs _ (hs f gs (test.mpr ht))

variable [NatBound (K R 0)] [IntegerRelations (K R 0)] [ConstantFactors (K R 0)]
variable [Decidable (IsSquare (-1 : K R 0))]

variable [CharZero k] [IsAlgClosed k] [LawfulNatBound (K R 0)]
variable [LawfulIntegerRelations (K R 0)] [LawfulConstantFactors (K R 0)]

/-- Exponential substitution and restoration preserve the joint specification, including
when the imaginary unit must be adjoined and both results descended to the input field. -/
theorem Tower.operations_of_tangent (t : Tower R n) (h : ¬ t.TangentFree) :
    t.operations.Spec k t := by
  rw [operations, dite_eq_right h]
  split
  · rename_i hs
    rw [Tower.tangentOperations_eq]
    let _ : CharZero R := (algebraMap R k).charZero
    let i := tangentUnit (K R 0)
    have hi : i^2 = -1 := tangentUnit_sq _ hs
    let c := RingHom.id (K R 0)
    have hc (x : K R 0) : Model.constantHom k (c x) = Model.constantHom k x := rfl
    refine spec_of_checked k t _ ?_ (t.integrateOriginal c i) (t.solveOriginal c i) ?_ ?_ ?_ ?_ ?_
    · exact t.admissibleOriginal_iff k c hc i hi
    · intro f ha
      change (t.compile c i).tower.checkSteps (t.compile c i).tangentFree = true at ha
      simp only [integrateOriginal, Compiled.integrate, ha, ite_true, Option.map_some]
      rfl
    · intro f gs ha
      change (t.compile c i).tower.checkSteps (t.compile c i).tangentFree = true at ha
      simp only [solveOriginal, Compiled.solve, ha, ite_true, Option.map_some]
      rfl
    · exact t.integrateOriginal_sound k c hc i hi
    · exact t.integrateOriginal_complete k c hc i hi
    · exact fun f gs _ he => t.solveOriginal_spec k c hc i hi f gs he
  · rename_i hn
    let _ : Fact (¬ IsSquare (-1 : K R 0)) := ⟨hn⟩
    rw [Tower.tangentOperations_eq]
    refine spec_of_checked k t _ ?_ t.integrateAdjoinI t.solveAdjoinI ?_ ?_ ?_ ?_ ?_
    · exact t.admissibleAdjoinI_iff k
    · intro f ha
      change t.adjoinI.tower.checkSteps t.adjoinI.tangentFree = true at ha
      unfold adjoinI at ha
      simp only [integrateAdjoinI, integrateOriginal, Compiled.integrate, ha, ite_true,
        Option.map_some]
      rfl
    · intro f gs ha
      change t.adjoinI.tower.checkSteps t.adjoinI.tangentFree = true at ha
      unfold adjoinI at ha
      simp only [solveAdjoinI, solveOriginal, Compiled.solve, ha, ite_true, Option.map_some]
      rfl
    · exact t.integrateAdjoinI_sound k
    · exact t.integrateAdjoinI_complete k
    · exact fun f gs _ he => t.solveAdjoinI_spec k f gs he

end SympyProofs.Calculus.Antiderivative
