module

public import SympyProofs.Sum.Gosper.Backend.Term

/-! Integer-ratio recognition and standalone RREF transport lemmas. -/

@[expose] public section

namespace Gosper.Algorithm

open IsLocalization

variable {K W : Type*} [CommRing K] [IsDomain K]
variable [CommRing W] [IsDomain W] [Algebra K W] {m n : ℕ}

/-- Mapping entries twice composes the coefficient maps. -/
theorem RrefResult.map_map {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (r : RrefResult R m n) (f : R →+* S) (g : S →+* T) :
    (r.map f).map g = r.map (g.comp f) := rfl

/-- Identity augmentation is defined over any commutative ring and commutes with maps. -/
theorem augmentedIdentity_map_ring {R S : Type*} [CommRing R] [CommRing S]
    (A : Matrix (Fin m) (Fin n) R) (f : R →+* S) :
    (augmentedIdentity A).map f = augmentedIdentity (A.map f) := by
  ext i j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp [augmentedIdentity]
  · simp [augmentedIdentity, Matrix.one_apply]

/-- Recognize an integer quotient using the field's integer-membership test. -/
noncomputable def fieldIntegerRatio {F : Type*} [Field F] [DecidableEq F]
    [DecidablePred (IsInteger ℤ : F → Prop)] (a b : F) : Option ℤ :=
  if b = 0 then none
  else if h : IsInteger ℤ (a / b) then some (Encodable.choose h)
  else none

theorem fieldIntegerRatio_eq_some {F : Type*} [Field F] [CharZero F] [DecidableEq F]
    [DecidablePred (IsInteger ℤ : F → Prop)] (a b : F) (hb : b ≠ 0) (z : ℤ) :
    fieldIntegerRatio a b = some z ↔ a = (z : F) * b := by
  simp only [fieldIntegerRatio, hb, ↓reduceIte]
  by_cases hi : IsInteger ℤ (a / b)
  · simp only [dite_eq_left hi, Option.some.injEq]
    have hc : ((Encodable.choose hi : ℤ) : F) = a / b := Encodable.choose_spec hi
    constructor
    · intro hz
      apply (div_eq_iff hb).mp
      simpa only [hz] using hc.symm
    · intro hz
      exact Int.cast_injective (hc.trans ((div_eq_iff hb).mpr hz))
  · simp only [dite_eq_right hi, reduceCtorEq, false_iff]
    intro hz
    exact hi ⟨z, ((div_eq_iff hb).mpr hz).symm⟩

private theorem matrix_kernel_fractionRing {F : Type*} [Field F]
    (A : Matrix (Fin m) (Fin n) F) (x : Fin n → FractionRing F) :
    (A.map (algebraMap F (FractionRing F))).mulVec x = 0 ↔
      A.mulVec (fun j => FractionRing.algEquiv F F (x j)) = 0 := by
  let e := FractionRing.algEquiv F F
  have hi : Function.Injective (fun y : Fin m → FractionRing F => fun i => e (y i)) := by
    intro y z h
    ext i
    exact e.injective (congrFun h i)
  rw [← hi.eq_iff]
  have hvec : (fun i => e ((A.map (algebraMap F (FractionRing F))).mulVec x i)) =
      A.mulVec (fun j => e (x j)) := by
    ext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul, e]
  have hz : (fun i : Fin m => e ((0 : Fin m → FractionRing F) i)) = 0 := by
    ext i
    exact e.map_zero
  rw [hvec, hz]

/-- A valid field RREF remains valid over its fraction field. -/
theorem rref_valid_fractionRing {F : Type*} [Field F]
    (rref : RrefOperation F) (hrref : ∀ {m n} (M : Matrix (Fin m) (Fin n) F),
      (rref M).Valid M) {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) F) :
    ((rref M).map (algebraMap F (FractionRing F))).Valid
      (M.map (algebraMap F (FractionRing F))) := by
  refine { (rref M).map_valid_self (hrref M)
    (algebraMap F (FractionRing F)) with kernel_iff := ?_ }
  intro x
  exact (matrix_kernel_fractionRing M x).trans
    (((hrref M).kernel_iff _).trans
      (matrix_kernel_fractionRing (rref M).matrix x).symm)

end Gosper.Algorithm
