module

public import SympyProofs.Calculus.Antiderivative.Program.Decision
public import SympyProofs.Calculus.Antiderivative.Proof.Elementary.Basis
public import SympyProofs.Calculus.Antiderivative.Proof.Elementary.Integrate
public import SympyProofs.Calculus.Antiderivative.Proof.Solve.Step
public import SympyProofs.Calculus.Antiderivative.Proof.Logarithmic.Step
public import SympyProofs.Calculus.Antiderivative.Proof.Decision
public import SympyProofs.Calculus.Antiderivative.Proof.ConstantsConverse
public import SympyProofs.Calculus.Antiderivative.Proof.Factor.Complete
public import SympyProofs.Calculus.Antiderivative.Proof.Factor.Constants

/-! The joint induction for elementary integration and the parametric differential equation. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [NatBound (K R 0)] [IntegerRelations (K R 0)] [ConstantFactors (K R 0)] {n : ℕ}

private theorem level_step (t : Tower R n) (g : ReducedGen (K R n)) (hf : t.TangentFree)
    (h : (t.step g).TangentFree) : (t.step g).level h = stepLevel t.D g (t.level hf) := by
  cases g <;> rfl

private theorem checkSteps_step (t : Tower R n) (g : ReducedGen (K R n)) (hf : t.TangentFree)
    (h : (t.step g).TangentFree) :
    (t.step g).checkSteps h = (t.checkSteps hf && g.check t.D (t.level hf)) := by
  cases g <;> rfl

variable (k : Type) [Field k] [CharZero k] [IsAlgClosed k] [Algebra R k] [FaithfulSMul R k]
variable [LawfulNatBound (K R 0)] [LawfulIntegerRelations (K R 0)] [LawfulConstantFactors (K R 0)]

/-- Every decision required by the next tower level holds for the computed primitive or
exponential extension of an admissible field. -/
theorem stepLevel_spec (t : Tower R n) (g : ReducedGen (K R n)) (L : Level R n)
    (ht : t.Admissible k) (hg : g.Admissible k t) (hL : L.Spec k t) :
    (stepLevel t.D g L).Spec k (t.step g) := by
  refine ⟨?_,
    Elementary.basis_spec k hL.solve hL.elementaryBasis ht hg rfl,
    Solve.step_spec k t g hg L hL.solve hL.logarithmic,
    stepLevel_logRelations_spec k t g L hg hL.logarithmic⟩
  intro f
  have h := Elementary.integrate_spec k t g L hL.solve hL.integrate hL.elementaryBasis ht hg f
  cases he : Elementary.integrate t.D g L f <;> simpa only [stepLevel, he] using h

/-- Simultaneous correctness of all four decisions on a normalized, admissible tower. -/
theorem Tower.level_spec (t : Tower R n) (hf : t.TangentFree) (ht : t.Admissible k) :
    (t.level hf).Spec k t := by
  induction t, hf using Tower.tangentFree_induct with
  | base => exact baseLevel_spec k
  | step t g hf ih =>
    obtain ⟨ht, hg⟩ := (t.admissible_step_iff k g).mp ht
    rw [level_step t g hf]
    exact stepLevel_spec k t g (t.level hf) ht hg (ih ht)

/-- The executable admissibility test decides preservation of the field of constants at
each level, including all positive multiples in an exponential extension. -/
theorem Tower.checkSteps_iff (t : Tower R n) (hf : t.TangentFree) :
    t.checkSteps hf = true ↔ t.Admissible k := by
  induction t, hf using Tower.tangentFree_induct with
  | base => simp [checkSteps]
  | step t g hf ih =>
    rw [checkSteps_step t g hf, Bool.and_eq_true, ih, t.admissible_step_iff k g]
    exact and_congr_right fun ht => g.check_iff k t (t.level hf) (t.level_spec k hf ht)

end SympyProofs.Calculus.Antiderivative
