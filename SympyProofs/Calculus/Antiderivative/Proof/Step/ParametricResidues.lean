module

public import SympyProofs.Calculus.Antiderivative.Program.Step.ParametricResidues
public import SympyProofs.Calculus.Antiderivative.Proof.Step.Residue
import Mathlib.Tactic.FieldSimp

/-! At every simple normal root, the computed residue equations differentiate the actual residue. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Step

open Polynomial
open scoped Differential

variable {F E : Type} [Field F] [DecidableEq F] [Field E] [Algebra F E]
variable [Differential F] [Differential E] [DifferentialAlgebra F E]

/-- Evaluate the executable polynomial at a point of a differential field extension. -/
noncomputable def rootEval (z : E) : Poly F →+* E := (aeval z).toRingHom.comp Poly.equiv.toRingHom

omit [Differential F] [Differential E] [DifferentialAlgebra F E] in
private theorem eval_inverse (z : E) (f s : Poly F) (hs : rootEval z s = 0)
    (h : IsCoprime f s) : rootEval z f * rootEval z (bezout f s).1 = 1 := by
  have he := congrArg (rootEval z) (bezout_spec f s)
  have hg : gcd f s = 1 := by
    simpa using normalize_eq_one.mpr (gcd_isUnit_iff_isRelPrime.mpr h.isRelPrime)
  simpa [hs, hg] using he

/-- The evaluation of the computed implicit velocity is the derivative of the algebraic root. -/
theorem rootVelocity_spec (z : E) (s : Poly F) (hs : rootEval z s = 0)
    (hsep : IsCoprime s.derivative s) :
    rootEval z (rootVelocity Differential.deriv s) = z′ := by
  let ev := rootEval (F := F) z
  have hc : Poly.equiv (s.map Differential.deriv) = Differential.mapCoeffs (Poly.equiv s) := by
    ext j
    simp [Poly.coeff_map _ (map_zero _)]
  have he := Differential.deriv_aeval_eq z (Poly.equiv s)
  change (ev s)′ = _ at he
  change ev s = 0 at hs
  rw [hs, map_zero] at he
  change 0 = aeval z (Differential.mapCoeffs (Poly.equiv s)) +
    aeval z (Poly.equiv s).derivative * z′ at he
  rw [← hc, ← Poly.equiv_derivative] at he
  change 0 = ev (s.map Differential.deriv) + ev s.derivative * z′ at he
  have hi := eval_inverse z s.derivative s hs hsep
  rw [rootVelocity, map_mod_of_zero _ hs, map_mul, map_neg]
  change -ev (s.map Differential.deriv) * ev _ = _
  linear_combination (ev (bezout s.derivative s).1) * he + z′ * hi

/-- Applying the residue equations and evaluating at a root is the field derivative of
the quotient of the specialized numerator by the differential denominator derivative. -/
theorem residueDerivatives_spec (z : E) (dx s : Poly F) (as : List (Poly F))
    (hs : rootEval z s = 0) (hsep : IsCoprime s.derivative s)
    (hn : IsCoprime (polyDer Differential.deriv dx s) s) :
    (residueDerivatives Differential.deriv dx s as).map (rootEval z) =
      as.map fun a => (rootEval z a / rootEval z (polyDer Differential.deriv dx s))′ := by
  let ds := polyDer Differential.deriv dx s
  have hi := eval_inverse z ds s hs hn
  have inv : rootEval z (bezout ds s).1 = (rootEval z ds)⁻¹ := by
    exact eq_inv_of_mul_eq_one_right hi
  simp only [residueDerivatives, List.map_map]
  apply List.map_congr_left
  intro a _
  dsimp only [Function.comp_apply]
  rw [map_mod_of_zero _ hs]
  change aeval z (Poly.equiv (polyDer _ _ _)) = _
  rw [polyDer_spec]
  change aeval z (Differential.implicitDeriv _ _) = _
  have hz : z′ = aeval z (Poly.equiv (rootVelocity Differential.deriv s)) :=
    (rootVelocity_spec z s hs hsep).symm
  rw [← Differential.deriv_aeval_eq_implicitDeriv z _ hz]
  change (rootEval z (_ % s))′ = _
  rw [map_mod_of_zero _ hs, map_mul, inv, ← div_eq_mul_inv]

end SympyProofs.Calculus.Antiderivative.Step
