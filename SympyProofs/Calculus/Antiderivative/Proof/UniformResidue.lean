module

public import SympyProofs.Calculus.Antiderivative.Proof.Residue
public import SympyProofs.Calculus.Antiderivative.Proof.PolynomialDerivation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! If all residues agree, the logarithm of the full denominator gives the primitive.
The lower correction removes the polynomial part of its logarithmic derivative. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Residue

open Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

/-- Join a polynomial in the last generator, then interpret it in the model. -/
private noncomputable def joinHom : Poly (K R n) →+* M k (n+1) :=
  (val k).comp ((eval₂RingHom K.lift K.gen).comp Poly.equiv.toRingHom)

private theorem joinHom_apply (p : Poly (K R n)) : joinHom k p = val k (K.joinPoly p) := by
  rw [K.joinPoly, ← Poly.eval_equiv, Poly.equiv_map, eval_map]
  rfl

private theorem joinHom_C (v : K R n) : joinHom k (Poly.C v) = val k (K.lift v) := by
  simp [joinHom]

private theorem joinPoly_nonzero {d : Poly (K R n)} (hd : d ≠ 0) :
    val k (K.joinPoly d) ≠ 0 := by
  intro h
  have he := val_joinPoly k d
  rw [h, map_zero] at he
  exact (RatFunc.algebraMap_ne_zero ((Polynomial.map_ne_zero_iff (val_injective (R := R) k)).mpr
    ((map_ne_zero_iff _ Poly.equiv.injective).mpr hd))) he.symm

/-- The zero-numerator path contributes neither a logarithm nor a correction. -/
@[simp] theorem logPart_zero (d e : Poly (K R n)) (twist : K R n) :
    logPart 0 d e twist = some ([], 0) := by simp [logPart]

/-- The fast path's primitive and its lower-field correction differentiate to the input. -/
theorem uniformPart_spec (t : Tower R (n+1)) {a d e : Poly (K R n)} (hd : d ≠ 0)
    (he : t.modelD k (val k (K.joinPoly d)) = val k (K.joinPoly e))
    {logs : List (RootSum R (n+1))} {corr : K R n} (hu : uniformPart a d e = some (logs,corr)) :
    (∀ s ∈ logs, s.Regular k) ∧
      val k (K.join a d) = (logs.map (RootSum.deriv k t)).sum + val k (K.lift corr) := by
  classical
  rw [uniformPart, Poly.divMod_eq] at hu
  dsimp only at hu
  split at hu
  · contradiction
  rename_i cond
  split at hu
  · rename_i hc
    let c := (K.const? (a.leadingCoeff / (e % d).leadingCoeff)).getD 0
    let v := K.ofConst (n := n) c
    let q := (e / d).coeff 0
    have heq : e / d = Poly.C q := by
      have hdeg : (e / d).natDegree = 0 := by
        by_contra h
        simp [h] at cond
      apply Poly.equiv.injective
      rw [Poly.equiv_C]
      exact (eq_C_of_natDegree_eq_zero
        (p := Poly.equiv (e/d)) (by simpa only [Poly.natDegree_equiv] using hdeg)).trans
          (congrArg C (Poly.coeff_equiv _ 0))
    have hR := congrArg (joinHom k) (EuclideanDomain.div_add_mod e d)
    rw [heq, map_add, map_mul, joinHom_C] at hR
    have hA := congrArg (joinHom k) hc
    change joinHom k (Poly.C v * (e % d)) = joinHom k a at hA
    rw [map_mul, joinHom_C] at hA
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hu)
    have hD := joinPoly_nonzero k hd
    let s : RootSum R (n+1) := ⟨Poly.X - Poly.C c, Poly.C (K.joinPoly d), 1⟩
    have sm : s.modelModulus k = X - C (Model.constantHom k c) := by simp [s, RootSum.modelModulus]
    have sa (z : k) : s.argAt k z = val k (K.joinPoly d) := by simp [s, RootSum.argAt]
    have hv : Model.C k (n+1) (Model.constantHom k c) = val k (K.lift v) := by
      rw [val_lift, ← Model.C_constantHom k c, Model.includeVars_C]
    refine ⟨?_, ?_⟩
    · intro u hu
      obtain rfl := List.mem_singleton.mp hu
      change s.Regular k
      exact ⟨sm ▸ X_sub_C_ne_zero _, fun z _ => sa z ▸ hD⟩
    · change val k (K.join a d) = ([s].map (RootSum.deriv k t)).sum + val k (K.lift (-(v*q)))
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        RootSum.deriv, sm, roots_X_sub_C, Multiset.toFinset_singleton,
        Finset.sum_singleton, sa,
        show s.weight = 1 from rfl, map_one, one_mul, he, hv, map_neg, map_mul, K.join, map_div₀]
      rw [← joinHom_apply, ← joinHom_apply, ← joinHom_apply, ← hA, ← hR]
      have nz : joinHom k d ≠ 0 := joinHom_apply k d ▸ hD
      field_simp
      ring
  · contradiction

/-- In a tower step the input polynomial derivative satisfies the fast path's differential
identity, for both primitive and exponential generators. -/
theorem uniformPart_step (t : Tower R n) (g : ReducedGen (K R n))
    {a d : Poly (K R n)} (hd : d ≠ 0) {logs : List (RootSum R (n+1))} {corr : K R n}
    (hu : uniformPart a d (Step.polyDer t.D (g.velocity t.D) d) = some (logs, corr)) :
    (∀ s ∈ logs, s.Regular k) ∧
      val k (K.join a d) =
        (logs.map (RootSum.deriv k (t.step g))).sum + val k (K.lift corr) :=
  uniformPart_spec k _ hd (t.modelD_joinPoly k g d) hu

end SympyProofs.Calculus.Antiderivative.Residue
