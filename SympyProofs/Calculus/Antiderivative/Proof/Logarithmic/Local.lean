module

public import SympyProofs.Calculus.Antiderivative.Proof.Logarithmic.Saturation
public import SympyProofs.Calculus.Antiderivative.Extension.LiouvilleForm

/-! Integer orders of zeros and poles give rational residues and descend through constant
extensions by polynomial Bézout identities. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Logarithmic

open Polynomial
open scoped Polynomial
open Extension.LiouvilleForm

variable {F : Type*} [Field F] [CharZero F]
local notation "ι" => algebraMap F[X] (RatFunc F)

omit [CharZero F] in
private theorem regular_dvd {s A S : F[X]} (hs : Prime s) (hsS : s ∣ S) (hn : S ≠ 0)
    (reg : Residue.Regular s (ι A / ι S)) : s ∣ A := by
  obtain ⟨v, w, hw, he⟩ := reg
  have wn : w ≠ 0 := fun z => hw (z ▸ dvd_zero _)
  have mul := (div_eq_div_iff (RatFunc.algebraMap_ne_zero hn) (RatFunc.algebraMap_ne_zero wn)).mp he
  rw [← map_mul, ← map_mul] at mul
  have eq := (IsFractionRing.injective F[X] (RatFunc F)) mul
  exact (hs.dvd_mul.mp (eq ▸ dvd_mul_of_dvd_right hsS v)).resolve_right hw

variable [Differential F] [Differential (RatFunc F)] [DifferentialAlgebra F (RatFunc F)]

/-- The residue of a saturated logarithmic derivative at a prime denominator factor is
an integer pole order divided by the positive integer clearing saturation. -/
theorem residue_of_saturated {a b : F}
    (dx : Differential.deriv (RatFunc.X : RatFunc F) = RatFunc.C a * RatFunc.X + RatFunc.C b)
    (A S : F[X]) (hn : S ≠ 0) (sat : Saturated Differential.deriv (ι A / ι S))
    {s : F[X]} (hs : Prime s) (hsS : s ∣ S) :
    ∃ r : ℚ, s ∣ A - C (r : F) * Extension.affine a b S := by
  obtain ⟨m, y, hm, hy, he⟩ := sat
  obtain ⟨j, hj⟩ := Residue.regular_logDeriv dx hs y
  obtain ⟨T, hT⟩ := hsS
  have sn := RatFunc.algebraMap_ne_zero hs.ne_zero
  have den := RatFunc.algebraMap_ne_zero hn
  let N := C (m : F) * A - C (j : F) * Extension.affine a b s * T
  have repr : Differential.logDeriv y - (j : RatFunc F) * Differential.logDeriv (ι s) =
      ι N / ι S := by
    change Differential.deriv y / y - (j : RatFunc F) * (Differential.deriv (ι s) / ι s) = _
    rw [he, affineDeriv_map dx]
    dsimp [N]
    rw [map_sub, map_mul, map_mul, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_C]
    have hmap : ι S = ι s * ι T := by rw [hT, map_mul]
    field_simp
    rw [hmap]
    rw [show RatFunc.C (m : F) = (m : RatFunc F) from map_natCast RatFunc.C m,
      show RatFunc.C (j : F) = (j : RatFunc F) from map_intCast RatFunc.C j]
    ring
  have divN := regular_dvd hs ⟨T, hT⟩ hn (repr ▸ hj)
  have full : s ∣ C (m : F) * A - C (j : F) * Extension.affine a b S := by
    rw [hT, Derivation.leibniz]
    have eq : C (m : F) * A - C (j : F) * (s • Extension.affine a b T + T • Extension.affine a b s) =
        N - s * (C (j : F) * Extension.affine a b T) := by simp only [smul_eq_mul, N]; ring
    rw [eq]
    exact dvd_sub divN (dvd_mul_right _ _)
  refine ⟨(j : ℚ) / m, ?_⟩
  have mn : (m : F) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have ass : C (m : F) * (A - C (((j : ℚ) / m : ℚ) : F) * Extension.affine a b S) =
      C (m : F) * A - C (j : F) * Extension.affine a b S := by
    rw [mul_sub, ← mul_assoc, ← C_mul]
    push_cast
    field_simp
  have hv := (show IsUnit (C (m : F)) from isUnit_C.mpr (isUnit_iff_ne_zero.mpr mn))
  exact hv.dvd_mul_left.mp (ass ▸ full)

/-- A common factor after coefficient extension forces divisibility by the original
irreducible polynomial. -/
theorem descend_dvd {E L : Type*} [Field E] [Field L] (f : E →+* L) {P A : E[X]}
    (hp : Irreducible P) {s : L[X]} (hs : Prime s) (hsP : s ∣ P.map f)
    (hsA : s ∣ A.map f) : P ∣ A := by
  rcases hp.isCoprime_or_dvd A with cp | dvd
  · exact False.elim (hs.not_isUnit (((Polynomial.isCoprime_map f).mpr cp).isUnit_of_dvd' hsP hsA))
  · exact dvd

end SympyProofs.Calculus.Antiderivative.Logarithmic
