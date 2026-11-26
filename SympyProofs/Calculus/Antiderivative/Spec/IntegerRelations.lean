module

public import SympyProofs.Calculus.Antiderivative.Algebra.IntegerRelations
public import SympyProofs.Calculus.Antiderivative.Program.Linear

/-! The rational rows compute integral relations even when the constant field is larger than ℚ. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

/-- A linear combination of field elements with rational coefficients. -/
def rationalCombination {F : Type} [Field F] (q : List ℚ) (x : List F) : F :=
  (q.zipWith (fun c a => (c : F) * a) x).sum

/-- The rows have one column per constant and give exactly their rational relations. -/
class LawfulIntegerRelations (F : Type) [Field F] [IntegerRelations F] : Prop where
  /-- Each equation has the indicated number of unknowns. -/
  width : ∀ xs : List F, ∀ r ∈ IntegerRelations.rows xs, r.length = xs.length
  /-- A rational combination vanishes precisely when it satisfies every row. -/
  kernel : ∀ (xs : List F) (q : List ℚ), (∀ r ∈ IntegerRelations.rows xs, Linear.dot q r = 0) ↔
    rationalCombination q xs = 0

instance : LawfulIntegerRelations ℚ where
  width xs r hr := by change r ∈ [xs] at hr; exact congrArg List.length (List.mem_singleton.mp hr)
  kernel xs q := by
    change (∀ r ∈ [xs], Linear.dot q r = 0) ↔ _
    simp [Linear.dot, rationalCombination]

/-- A field embedding preserves every rational linear combination. -/
theorem map_rationalCombination {F G : Type} [Field F] [Field G] (f : F →+* G)
    (q : List ℚ) (xs : List F) :
    f (rationalCombination q xs) = rationalCombination q (xs.map f) := by
  induction q generalizing xs with
  | nil => simp [rationalCombination]
  | cons a q ih => cases xs with
    | nil => simp [rationalCombination]
    | cons x xs => simpa [rationalCombination] using congrArg (fun t => (a : G) * f x + t) (ih xs)

/-- Computing relations through a field embedding preserves their specification. -/
theorem LawfulIntegerRelations.ofMap {F G : Type} [Field F] [Field G] [IntegerRelations G]
    [LawfulIntegerRelations G] (f : F →+* G) :
    @LawfulIntegerRelations F _ (IntegerRelations.ofMap f) := by
  let := IntegerRelations.ofMap f
  constructor
  · intro xs r hr
    simpa using LawfulIntegerRelations.width (xs.map f) r hr
  · intro xs q
    rw [← f.injective.eq_iff, map_zero f, map_rationalCombination]
    exact LawfulIntegerRelations.kernel (xs.map f) q

instance : LawfulIntegerRelations (K ℤ 0) :=
  LawfulIntegerRelations.ofMap (K.constantsEquiv ℚ).toRingHom

instance {F : Type} [Field F] [DecidableEq F] [IntegerRelations F] [LawfulIntegerRelations F] :
    LawfulIntegerRelations (K F 0) :=
  LawfulIntegerRelations.ofMap (K.constantsEquiv F).toRingHom

end SympyProofs.Calculus.Antiderivative
