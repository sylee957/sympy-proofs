module

public import SympyProofs.Calculus.Antiderivative.Program.Solve
public import SympyProofs.Calculus.Antiderivative.Proof.Residue
public import SympyProofs.Calculus.Antiderivative.Proof.Logarithmic
public import SympyProofs.Calculus.Antiderivative.Proof.Kind.Coefficients
public import SympyProofs.Calculus.Antiderivative.Spec.NatBound

/-! Pole-order bounds used when clearing a first-order differential equation. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Solve

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [CharZero k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

open Polynomial

/-- A nonconstant common factor after specializing the residue parameter at a natural
number forces that number below the program's bound for normal poles. -/
theorem le_normalBound [NatBound (K R 0)] [LawfulNatBound (K R 0)]
    (a b e : Poly (K R n)) (hb : b.natDegree ≠ 0)
    (hc : IsCoprime (Step.modelPoly (val k) b) (Step.modelPoly (val k) a)) (m : ℕ)
    (hm : ¬ IsCoprime (Step.modelPoly (val k) b)
      (Step.modelPoly (val k) a - C (m : M k n) * Step.modelPoly (val k) e)) :
    m ≤ normalBound a b e := by
  have hb' : b ≠ 0 := fun h => hb (by simp [h])
  rw [normalBound, ite_eq_right hb]
  apply LawfulNatBound.natRootBound_spec _ _ (Residue.constantRoots_ne_zero k
    (Residue.residuePolynomial_ne_zero k a b e hb' hc))
  have hr := (Residue.residue_roots k a b e hb' (m : k)).mpr (by simpa using hm)
  change ((Poly.equiv _).map (Model.constantHom (R := R) k)).eval (m : k) = 0 at hr
  rwa [← map_natCast (Model.constantHom (R := R) k) m, eval_map_apply, Poly.eval_equiv,
    map_eq_zero_iff _ (Model.constantHom (R := R) k).injective] at hr

end SympyProofs.Calculus.Antiderivative.Solve
