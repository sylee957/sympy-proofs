module

public import SympyProofs.Calculus.Antiderivative.Algebra.Gaussian
public import SympyProofs.Calculus.Antiderivative.Proof.Factor.Rational
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Data.List.Prime

/-! Exact rational norms and polynomial translation over the Gaussian rational field. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.WithI

open Polynomial

variable {F : Type} [Field F] [DecidableEq F]
local notation "G" => WithI F

private theorem horner_translate (l : List G) (a : G) :
    Poly.equiv (l.foldr (fun c q => Poly.C c + (Poly.X + Poly.C a) * q) 0) =
      taylor a (Poly.Raw.toPolynomial l) := by
  induction l with
  | nil => simp
  | cons c l ih =>
    simp [ih, taylor_apply, add_comp, mul_comp, Poly.Raw.toPolynomial_cons]

@[simp] theorem equiv_translate (p : Poly G) (a : G) :
    Poly.equiv (translate p a) = taylor a (Poly.equiv p) := by
  rw [translate, horner_translate, ← Poly.equiv_ofList, Poly.ofList_coeffs]

/-- Substitution of a translate is a ring isomorphism preserving degree. -/
noncomputable def translation (a : G) : Poly G ≃+* Poly G :=
  Poly.equiv.trans ((taylorEquiv a).toRingEquiv.trans Poly.equiv.symm)

@[simp] theorem translation_apply (a : G) (p : Poly G) :
    translation a p = translate p a := by
  apply Poly.equiv.injective
  simp [translation]
  rfl

@[simp] theorem translate_degree (p : Poly G) (a : G) :
    (translate p a).natDegree = p.natDegree := by rw [← Poly.natDegree_equiv, equiv_translate]; simp

@[simp] theorem translate_back (p : Poly G) (a : G) :
    translate (translate p a) (-a) = p := by
  apply Poly.equiv.injective
  simp [taylor_taylor]

section
variable [Fact (∀ x : F, x ^ 2 ≠ -1 + 0 * x)]

omit [DecidableEq F] in
private theorem nextCoeff_taylor (p : G[X]) (hm : p.Monic) (hd : 0 < p.natDegree)
    (a : G) : (taylor a p).nextCoeff = p.nextCoeff + a * p.natDegree := by
  let j := p.natDegree - 1
  have hj : j+1 = p.natDegree := by dsimp [j]; omega
  rw [nextCoeff_of_natDegree_pos (by simpa using hd), natDegree_taylor,
    nextCoeff_of_natDegree_pos hd, taylor_coeff]
  change (hasseDeriv j p).eval a = p.coeff j + a * p.natDegree
  have hdeg : (hasseDeriv j p).natDegree ≤ 1 := (natDegree_hasseDeriv_le ..).trans (by omega)
  rw [eq_X_add_C_of_degree_le_one (degree_le_of_natDegree_le hdeg)]
  have hc : p.natDegree.choose j = p.natDegree := by rw [← hj, Nat.choose_succ_self_right]
  simp only [eval_add, eval_mul, eval_C, eval_X, hasseDeriv_coeff, zero_add, Nat.choose_self,
    Nat.cast_one, one_mul, add_comm 1 j, hj, hc,
    coeff_natDegree, hm.leadingCoeff]
  ring

theorem shift_nonreal [CharZero F] (p : Poly G) (hm : (Poly.equiv p).Monic) (hd : 0 < p.natDegree) :
    (Poly.equiv (translate p (shift p))).nextCoeff.im ≠ 0 := by
  rw [equiv_translate, nextCoeff_taylor _ hm (by simpa using hd),
    nextCoeff_of_natDegree_pos (by simpa using hd), Poly.natDegree_equiv, Poly.coeff_equiv]
  by_cases h : (p.coeff (p.natDegree-1)).im = 0
  · simp [shift, h, imaginary, Nat.cast_ne_zero.mpr hd.ne']
  · simp [shift, h]

end

/-- Inclusion of base-field polynomials in the quadratic polynomial ring. -/
noncomputable def includeBase : Poly F →+* Poly G :=
  Poly.equiv.symm.toRingHom.comp ((mapRingHom (algebraMap F G)).comp Poly.equiv.toRingHom)

@[simp] theorem equiv_includeBase (h : Poly F) :
    Poly.equiv (includeBase h) = (Poly.equiv h).map (algebraMap F G) := by simp [includeBase]

theorem includeBase_apply (h : Poly F) : includeBase h = h.map (algebraMap F G) := by
  apply Poly.equiv.injective
  rw [equiv_includeBase, ← Poly.equiv_map]

theorem includeBase_injective : Function.Injective (includeBase (F := F)) := by
  intro a b h
  apply Poly.equiv.injective
  apply map_injective _ (algebraMap F G).injective
  simpa using congrArg Poly.equiv h

@[simp] theorem includeBase_degree (h : Poly F) : (includeBase h).natDegree = h.natDegree := by
  rw [← Poly.natDegree_equiv, equiv_includeBase, natDegree_map, Poly.natDegree_equiv]

/-- Conjugating every coefficient is an automorphism of the polynomial ring. -/
noncomputable def conjugate : Poly G ≃+* Poly G :=
  Poly.equiv.trans ((mapEquiv QuadraticAlgebra.starAlgEquiv.toRingEquiv).trans Poly.equiv.symm)

private theorem conjugate_apply (p : Poly G) : conjugate p = p.map star := by
  apply Poly.equiv.injective
  change Poly.equiv (Poly.equiv.symm _) = _
  rw [RingEquiv.apply_symm_apply]
  exact (Poly.equiv_map QuadraticAlgebra.starAlgEquiv.toRingHom p).symm

private theorem conjugate_coeff (p : Poly G) (i : ℕ) :
    (conjugate p).coeff i = star (p.coeff i) := by
  rw [conjugate_apply, Poly.coeff_map _ (star_zero G)]

private theorem conjugate_involutive (p : Poly G) : conjugate (conjugate p) = p := by
  apply Poly.ext
  intro i
  simp only [conjugate_coeff, star_star]

variable [CharZero F]

/-- The norm embeds as the product of the polynomial and its conjugate. -/
theorem includeBase_normPoly (p : Poly G) : includeBase (normPoly p) = p * conjugate p := by
  let q := p * conjugate p
  have hs : conjugate q = q := by simp [q, conjugate_involutive, mul_comm]
  apply Poly.ext
  intro i
  have hc := congrArg (fun r : Poly G => r.coeff i) hs
  rw [conjugate_coeff] at hc
  have hi := congrArg QuadraticAlgebra.im hc
  simp only [QuadraticAlgebra.im_star] at hi
  have hz : (q.coeff i).im = 0 := by
    have hz₂ : (2 : F) * (q.coeff i).im = 0 := by linear_combination -hi
    exact (mul_eq_zero.mp hz₂).resolve_left (by norm_num)
  rw [includeBase_apply, normPoly, ← conjugate_apply, Poly.coeff_map _ (by simp),
    Poly.coeff_map _ (by rfl)]
  change (algebraMap F G (q.coeff i).re) = q.coeff i
  exact QuadraticAlgebra.ext rfl hz.symm

theorem normPoly_mul (p q : Poly G) : normPoly (p*q) = normPoly p * normPoly q := by
  apply includeBase_injective
  rw [map_mul, includeBase_normPoly, includeBase_normPoly, includeBase_normPoly, map_mul]
  ring

variable [Fact (∀ x : F, x ^ 2 ≠ -1 + 0 * x)]

theorem normPoly_ne_zero {p : Poly G} (hp : p ≠ 0) : normPoly p ≠ 0 := by
  intro h
  have he := includeBase_normPoly p
  rw [h, map_zero] at he
  exact mul_ne_zero hp ((map_ne_zero_iff _ conjugate.injective).mpr hp) he.symm

theorem normPoly_degree {p : Poly G} (hp : p ≠ 0) :
    (normPoly p).natDegree = 2 * p.natDegree := by
  have hd : (conjugate p).natDegree = p.natDegree := by
    have he : Poly.equiv (conjugate p) =
        (Poly.equiv p).map (QuadraticAlgebra.starAlgEquiv : G ≃ₐ[F] G).toRingHom :=
      Poly.equiv.apply_symm_apply _
    rw [← Poly.natDegree_equiv, he, natDegree_map, Poly.natDegree_equiv]
  have hc := (map_ne_zero_iff _ conjugate.injective).mpr hp
  have hm := natDegree_mul ((map_ne_zero_iff _ Poly.equiv.injective).mpr hp)
    ((map_ne_zero_iff _ Poly.equiv.injective).mpr hc)
  rw [← includeBase_degree, includeBase_normPoly]
  simpa only [← map_mul, Poly.natDegree_equiv, hd, two_mul] using hm

end SympyProofs.Calculus.Antiderivative.WithI
