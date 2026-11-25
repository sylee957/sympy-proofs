module

public import SympyProofs.Calculus.Risch.Program.Solve
public import SympyProofs.Calculus.Risch.Proof.SolvePoly
public import SympyProofs.Calculus.Risch.Proof.Rel

/-! What the cleared data of one instance of the parametric equation satisfy. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch.Solve

open Polynomial

variable (k : Type) [Field k] [CharZero k] {n : ℕ}

/-- The properties of `pieces t f gs`: `f = N / B` in lowest terms, the right-hand sides are
`Ws / T`, the denominator `P` is `θᵉ T B ^ bound`, and the equation for `Y / P` is
`R Y′ + S Y = Σ cᵢ Gᵢ` with an operator of degree `lam`. -/
structure PiecesSpec (t : Tower (n + 1)) (f : Term (n + 1)) (gs : List (Term (n + 1)))
    (e : ℕ) (pc : Pieces n) : Prop where
  dN : Poly.Defined k pc.N
  dB : Poly.Defined k pc.B
  dP : Poly.Defined k pc.P
  nB : Poly.Normal k pc.B
  cop : IsCoprime (Poly.model k pc.N) (Poly.model k pc.B)
  fval : Term.value k f =
    algebraMap (K k n)[X] (RatFunc (K k n)) (Poly.model k pc.N) /
      algebraMap (K k n)[X] (RatFunc (K k n)) (Poly.model k pc.B)
  nT : Poly.model k pc.T ≠ 0
  dG : ∀ G ∈ pc.Gs, Poly.Defined k G
  lenG : pc.Gs.length = gs.length
  comb : ∀ c : List k, linComb c gs =
    algebraMap (K k n)[X] (RatFunc (K k n)) (pcomb c pc.Ws) /
      algebraMap (K k n)[X] (RatFunc (K k n)) (Poly.model k pc.T)
  Pval : Poly.model k pc.P = X ^ e * (Poly.model k pc.T *
    Poly.model k pc.B ^ Resultant.residueBound pc.N pc.B (Poly.der t pc.B))
  Rval : Poly.model k pc.R = Poly.model k pc.P * (Poly.model k pc.B * Poly.model k pc.T)
  Sval : Poly.model k pc.S = Poly.model k pc.T *
    (Poly.model k pc.N * Poly.model k pc.P -
      Poly.model k pc.B * Tower.polyDer k t (Poly.model k pc.P))
  Gval : ∀ c : List k, pcomb c pc.Gs =
    pcomb c pc.Ws * (Poly.model k pc.P * Poly.model k pc.P * Poly.model k pc.B)
  good : Good k t pc.R pc.S pc.lam

end SympyProofs.Calculus.Risch.Solve
