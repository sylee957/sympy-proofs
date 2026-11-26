module

public import SympyProofs.Calculus.Antiderivative.Proof.Elementary.PolynomialBasis
public import SympyProofs.Calculus.Antiderivative.Proof.Elementary.Add

/-! The normal-residue directions and their remaining Laurent integrands. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Elementary

open Solve

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

/-- The information supplied by normal-pole and residue reduction before the Laurent step. -/
structure DirectionSpec (t : Tower R n) (g : ReducedGen (K R n))
    (gs : List (K R (n+1))) (s : ℕ)
    (ds : List (Direction R n)) : Prop where
  /-- Each direction has one coordinate per original input. -/
  width : ∀ d ∈ ds, d.coords.length = gs.length
  /-- All logarithms constructed from normal residues are regular. -/
  regular : ∀ d ∈ ds, d.answer.Regular k
  /-- The reduced answer and remaining Laurent part account for the entire integrand. -/
  identity : ∀ d ∈ ds, d.answer.deriv k (t.step g) + laurentValue k s (modelPoly k d.rest) =
    Model.linearCombination k (d.coords.map (Model.constantHom k)) gs
  /-- Every elementary combination satisfies the normal residue constraints. -/
  covers : ∀ cs : List k, cs.length = gs.length →
    (t.step g).Elementary k (Model.linearCombination k cs gs) →
    Linear.vector (RingHom.id k) gs.length cs ∈ Submodule.span k
      ((fun d : Direction R n => Linear.vector (Model.constantHom k) gs.length d.coords) ''
        {d | d ∈ ds})

end SympyProofs.Calculus.Antiderivative.Elementary
