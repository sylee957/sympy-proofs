module

public import SympyProofs.Calculus.Antiderivative.Proof.Factor.Complete
public import SympyProofs.Calculus.Antiderivative.Proof.Factor.Constants
public import SympyProofs.Calculus.Antiderivative.Program.Constants.Parameters
public import SympyProofs.Calculus.Antiderivative.Proof.Constants
public import SympyProofs.Calculus.Antiderivative.Proof.Residue
public import SympyProofs.Calculus.Antiderivative.Proof.LogRelations

/-! Constant recognition, natural root bounds and rational dependencies over ℚ(γ₁,…,γₘ). -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

/-- The constant-field rational equations stay exact with any number of parameters. -/
instance (m : ℕ) : LawfulIntegerRelations (Parameters (m + 1)) where
  kernel := rationalRows_spec
  width xs r hr := by
    change r ∈ (rowsOf xs).flatMap IntegerRelations.rows at hr
    obtain ⟨s,hs,hr⟩ := List.mem_flatMap.mp hr
    exact (LawfulIntegerRelations.width s r hr).trans (length_rowsOf xs hs)

/-- Recognizing constants and eliminating parameters preserve both natural number bounds. -/
instance (m : ℕ) : LawfulNatBound (Parameters (m + 1)) where
  natBound_spec a j h := by
    subst a
    change j ≤ ((K.const? (j : K ℤ (m + 1))).map NatBound.natBound).getD 0
    rw [← map_natCast (K.ofConst (R := ℤ) (n := m + 1)), K.const?_ofConst]
    exact LawfulNatBound.natBound_spec (j : K ℤ 0) j rfl
  natRootBound_spec p j hp he := by
    apply LawfulNatBound.natRootBound_spec _ _ (Residue.constantRoots_ne_zero ℚ hp)
    have hroot (F G : Type) [Field F] [DecidableEq F] [Field G] (f : F →+* G) (v : Poly F) :
        (Step.modelPoly f v).IsRoot (j : G) ↔ v.eval (j : F) = 0 := by
      change ((Poly.equiv v).map f).eval (j : G) = 0 ↔ _
      rw [← map_natCast f j, Polynomial.eval_map_apply, Poly.eval_equiv, map_eq_zero_iff f
        f.injective]
    apply (hroot _ _ (Model.constantHom ℚ) _).mp
    apply (Residue.constantRoots_spec ℚ p j).mpr
    rw [map_natCast]
    exact (hroot _ _ (val ℚ) p).mpr he

/-- Factorization over rational-function parameters uses the verified tower factorizer. -/
instance (m : ℕ) : LawfulConstantFactors (Parameters (m + 1)) where
  irreducible p hp q hq := ⟨factorTower_monic p hp q hq, factorTower_irreducible p hp q hq⟩
  product := factorTower_product

end SympyProofs.Calculus.Antiderivative
