module

public import SympyProofs.CubicEquation.CardanoReal.ModifiedPrincipal.Properties

/-!
# The real root given by real and imaginary parts

For real depressed coefficients `p,q`, form the sum `W` of the two principal
cube roots of the Cardano radicands. Then `principalRealRoot p q`, defined as
`W.re - sqrt(3) * W.im`, is the sum of the two modified principal cube roots,
and is a real root of the depressed cubic. Its expression uses no modified-root
function, conjugation, or conditional.
-/

@[expose] public section

noncomputable section

namespace CubicEquation.CardanoReal

open RealCubeRoot
open CardanoComplex
open Complex
open scoped ComplexConjugate

/-- Conjugation fixes the two Cardano radicands individually or exchanges them. -/
private theorem radicand_pair_conj_sum (F : ℂ → ℂ) (p q : ℝ) :
    F (conj (radicandPlus (p : ℂ) q)) + F (conj (radicandMinus (p : ℂ) q)) =
      F (radicandPlus (p : ℂ) q) + F (radicandMinus (p : ℂ) q) := by
  let s := Complex.sqrt (discriminant (p : ℂ) q)
  have hs : conj s ^ 2 = s ^ 2 := by
    rw [← map_pow]
    change conj (Complex.sqrt (discriminant (p : ℂ) q) ^ 2) =
      Complex.sqrt (discriminant (p : ℂ) q) ^ 2
    rw [sqrt_sq, discriminant_ofReal, conj_ofReal]
  change F (conj (-((q : ℂ)) / 2 + s)) + F (conj (-((q : ℂ)) / 2 - s)) = _
  rcases eq_or_eq_neg_of_sq_eq_sq (conj s) s hs with hs | hs
  · simp only [map_add, map_sub, map_div₀, map_neg, conj_ofReal, hs,
      show conj (2 : ℂ) = 2 from conj_ofReal 2]
    rfl
  · simp only [map_add, map_sub, map_div₀, map_neg, conj_ofReal, hs,
      show conj (2 : ℂ) = 2 from conj_ofReal 2, sub_neg_eq_add]
    change F (-((q : ℂ)) / 2 - s) + F (-((q : ℂ)) / 2 + s) = _
    exact add_comm _ _

/-- A real root obtained directly from the real and imaginary parts of the
sum of the principal cube roots. -/
def principalRealRoot (p q : ℝ) : ℝ :=
  let W := principal (radicandPlus (p : ℂ) q) + principal (radicandMinus (p : ℂ) q)
  W.re - Real.sqrt 3 * W.im

/-- The simplified expression equals the first modified-principal Cardano root. -/
theorem principalRealRoot_coe (p q : ℝ) :
    (principalRealRoot p q : ℂ) =
      modifiedPrincipal (radicandPlus (p : ℂ) q) +
        modifiedPrincipal (radicandMinus (p : ℂ) q) := by
  simpa only [principalRealRoot] using
    (modifiedPrincipal_add_eq_re_im (radicand_pair_conj_sum principal p q)).symm

/-- The simplified real expression solves the depressed cubic for every real `p,q`. -/
theorem principalRealRoot_spec (p q : ℝ) :
    principalRealRoot p q ^ 3 + p * principalRealRoot p q + q = 0 := by
  have h := (mem_modifiedPrincipal_pairedRoots_iff p q _).mp
    (show modifiedPrincipal (radicandPlus (p : ℂ) q) +
      modifiedPrincipal (radicandMinus (p : ℂ) q) ∈
      pairedRoots (modifiedPrincipal (radicandPlus (p : ℂ) q))
        (modifiedPrincipal (radicandMinus (p : ℂ) q)) from by simp [pairedRoots])
  rw [← principalRealRoot_coe] at h
  exact_mod_cast h

end CubicEquation.CardanoReal
