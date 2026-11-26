module

public import SympyProofs.Calculus.Antiderivative.Program.TrigonometricDescent.Polynomials
public import SympyProofs.Calculus.Antiderivative.Proof.ResiduePartition
public import SympyProofs.Calculus.Antiderivative.Proof.TrigonometricResult
import Mathlib.Algebra.CharZero.Infinite

/-! Absorbing half the original logarithmic coefficient in the residue parameter. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Trigonometric.Descent

open Polynomial

variable {F k : Type} [Field F] [DecidableEq F] [Field k]

private theorem horner_rescale (a : F) (l : List F) :
    Poly.equiv (l.foldr (fun b p => Poly.C b + (Poly.C a * Poly.X) * p) 0) =
      (Poly.Raw.toPolynomial l).comp (C a * X) := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih, add_comp, mul_comp, Poly.Raw.toPolynomial_cons]

theorem equiv_rescale (a : F) (p : Poly F) :
    Poly.equiv (rescale a p) = (Poly.equiv p).comp (C a * X) := by
  rw [rescale, horner_rescale, ← Poly.equiv_ofList, Poly.ofList_coeffs]

/-- Rescaling changes the argument of every specialization of the polynomial. -/
theorem atRoot_rescale (f : F →+* k) (a : F) (p : Poly F) (x : k) :
    Step.atRoot f x (rescale a p) = Step.atRoot f (f a*x) p := by
  simp [Step.atRoot, equiv_rescale, map_comp, eval_comp]

variable {R S : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [CommRing S] [IsDomain S] [DecidableEq S] [NormalizedGCDMonoid S] [Div S] {n : ℕ}
variable (k : Type) [Field k] [CharZero k] [Algebra S k] [FaithfulSMul S k]

omit [CharZero k] in
private theorem half_root (s : RootSum S n) (z : k) :
    ((halfSum s).modelModulus k).IsRoot z ↔
      (s.modelModulus k).IsRoot ((Model.constantHom k (2/s.weight))*z) := by
  change Step.atRoot (Model.constantHom k) z (rescale _ s.modulus) = 0 ↔ _
  rw [atRoot_rescale]
  rfl

omit [CharZero k] in
private theorem half_arg (s : RootSum S n) (z : k) :
    (halfSum s).argAt k z = s.argAt k (Model.constantHom k (2/s.weight)*z) := by
  have ha (s' : RootSum S n) (b : k) : s'.argAt k b =
      Step.atRoot (val k) (Model.C k n b) s'.arg := by
    simp [RootSum.argAt, Step.atRoot, eval_map]
  rw [ha,ha]
  change Step.atRoot (val k) _ (rescale _ _) = _
  rw [atRoot_rescale, ← Model.C_constantHom, map_mul]

/-- A nonzero rescaling preserves regularity at every root. -/
theorem half_regular (s : RootSum S n) (hs : s.Regular k) (hw : s.weight ≠ 0) :
    (halfSum s).Regular k := by
  let a := Model.constantHom k (2/s.weight)
  have ha : a = 2 / Model.constantHom k s.weight := by
    rw [show a = _ from map_div₀ _ _ _, map_ofNat]
  have han : a ≠ 0 := by
    rw [ha]
    exact div_ne_zero two_ne_zero
      ((map_ne_zero_iff _ (Model.constantHom (R := S) k).injective).mpr hw)
  refine ⟨?_,fun z hz => by rw [half_arg]; exact hs.2 _ ((half_root k s z).mp hz)⟩
  intro hz
  apply hs.1
  apply Polynomial.funext
  intro y
  have h : ((halfSum s).modelModulus k).IsRoot (a⁻¹*y) := by simp [hz]
  have hy := (half_root k s _).mp h
  change (s.modelModulus k).eval (a*(a⁻¹*y)) = 0 at hy
  simpa [← mul_assoc,han] using hy

variable [Algebra R k] [FaithfulSMul R k]

/-- The rescaled, unweighted root sum differentiates to half the weighted sum. -/
theorem half_derivative (t : Tower R n) (s : RootSum S n) (hs : s.Regular k)
    (hw : s.weight ≠ 0) : RootSum.deriv k t (halfSum s) = RootSum.deriv k t s / 2 := by
  classical
  let a := Model.constantHom k (2/s.weight)
  have ha : a = 2 / Model.constantHom k s.weight := by
    rw [show a = _ from map_div₀ _ _ _, map_ofNat]
  have han : a ≠ 0 := by
    rw [ha]
    exact div_ne_zero two_ne_zero
      ((map_ne_zero_iff _ (Model.constantHom (R := S) k).injective).mpr hw)
  let u := ((halfSum s).modelModulus k).roots.toFinset
  let v := (s.modelModulus k).roots.toFinset
  have mem (z : k) : z ∈ u ↔ a*z ∈ v := by
    simp only [u,v,Multiset.mem_toFinset,mem_roots (half_regular k s hs hw).1,
      mem_roots hs.1,half_root,a]
  let ld (z : k) := t.modelD k (s.argAt k z)/s.argAt k z
  have rel : (∑ z ∈ u, Model.C k n z * ld (a*z)) =
      ∑ y ∈ v, (Model.C k n a)⁻¹*(Model.C k n y*ld y) := by
    apply Finset.sum_bij' (fun z _ => a*z) (fun y _ => a⁻¹*y)
    · exact fun z hz => (mem z).mp hz
    · intro y hy; apply (mem _).mpr; simpa [← mul_assoc,han] using hy
    · intro z _; simp [han]
    · intro y _; simp [han]
    · intro z _; simp [map_mul,← mul_assoc,han]
  simp only [RootSum.deriv,half_arg,show (halfSum s).weight = 1 from rfl,
    map_one,one_mul,← Model.C_constantHom]
  change (∑ z ∈ u, Model.C k n z * ld (a*z)) = _ * (∑ z ∈ v, Model.C k n z*ld z) / 2
  rw [rel,← Finset.mul_sum]
  rw [ha, map_div₀, map_ofNat, inv_div]
  ring

end SympyProofs.Calculus.Antiderivative.Trigonometric.Descent
