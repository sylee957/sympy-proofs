module

public import SympyProofs.Calculus.Antiderivative.Proof.Integrate
public import SympyProofs.Calculus.Antiderivative.Proof.Answer
public import SympyProofs.Calculus.Antiderivative.Proof.Liouville

/-! Returned primitives and nonexistence in elementary differential extensions of mixed towers. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n : ℕ} (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k]

variable [CharZero k] [IsAlgClosed k]
variable [NatBound (K R 0)] [LawfulNatBound (K R 0)]
variable [IntegerRelations (K R 0)] [LawfulIntegerRelations (K R 0)]
variable [ConstantFactors (K R 0)] [LawfulConstantFactors (K R 0)]
variable [Decidable (IsSquare (-1 : K R 0))]

/-- An admissible tower yields an answer exactly when its input has a Liouville form. -/
theorem integrate_iff_elementary {t : Tower R n} (ht : t.Admissible k) (f : K R n) :
    (∃ a, integrate t f = .elementary a) ↔ t.Elementary k (val k f) := by
  constructor
  · rintro ⟨a, h⟩
    rw [← (integrate_sound k ht h).2]
    exact a.deriv_elementary k t
  · intro he
    cases h : integrate t f with
    | elementary a => exact ⟨a, rfl⟩
    | nonelementary => exact (integrate_complete k ht h he).elim

/-- Integration on an admissible tower returns a regular primitive exactly when a primitive
can be written in the answer language over the original coefficient field. -/
theorem integrate_iff_answer {t : Tower R n} (ht : t.Admissible k) (f : K R n) :
    (∃ a, integrate t f = .elementary a ∧ a.Regular k ∧ a.deriv k t = val k f) ↔
      ∃ a : Answer R n, a.deriv k t = val k f :=
  ((t.operations_spec k).integrate ht).iff_answer k f

/-- A negative integration decision on an admissible tower excludes a primitive in every
elementary differential field extension of the original model. -/
theorem integrate_no_primitive {t : Tower R n} (ht : t.Admissible k) {f : K R n}
    (h : integrate t f = .nonelementary) :
    letI : Differential (M k n) := ⟨t.modelD k⟩
    ∀ (E : Type) [Field E] [Differential E] [Algebra (M k n) E],
      Extension.LiouvilleForm.ElementaryTower (M k n) E →
        ∀ y : E, Differential.deriv y ≠ algebraMap (M k n) E (val k f) :=
  ((t.operations_spec k).integrate ht).no_primitive k ht h

end SympyProofs.Calculus.Antiderivative
