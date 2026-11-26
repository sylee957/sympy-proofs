module

public import SympyProofs.Calculus.Antiderivative.Algebra.K.Basic
public import SympyProofs.Calculus.Antiderivative.Algebra.MPoly.Variables
public import SympyProofs.Calculus.Antiderivative.Algebra.K.Model

/-! Preserve the old generators and adjoin the variable with index equal to the old height. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] {n m : ℕ}

/-- Discard terms that have no value at the original height before including the list. -/
def MPoly.Raw.atHeight (n : ℕ) (p : MPoly.Raw R) : MPoly.Raw R :=
  p.filter fun t => t.1.trim.length ≤ n

private theorem exponents_castLE (h : n ≤ m) (e : Mono) (he : e.trim.length ≤ n) :
    (e.exponents n).mapDomain (Fin.castLE h) = e.exponents m := by
  ext i
  by_cases hi : i.val < n
  · let j : Fin n := ⟨i.val, hi⟩
    exact Finsupp.mapDomain_apply_of_injective (Fin.castLE_injective h) (e.exponents n) j
  · rw [Finsupp.mapDomain_of_notMem_range _ _ (by
      rintro ⟨j, rfl⟩
      exact hi j.isLt)]
    exact ((Mono.fits_iff n e).mp he _ (Nat.le_of_not_lt hi)).symm

/-- The list inclusion is the polynomial homomorphism that preserves every old index. -/
theorem MPoly.Raw.toMvPolynomial_atHeight (h : n ≤ m) (p : MPoly.Raw R) :
    toMvPolynomial m (atHeight n p) = MvPolynomial.rename (Fin.castLE h) (toMvPolynomial n p) := by
  induction p with
  | nil => simp [atHeight]
  | cons v p ih =>
    rcases v with ⟨e,a⟩
    by_cases he : e.trim.length ≤ n
    · simp [atHeight, he, he.trans h, toMvPolynomial_cons, MvPolynomial.rename_monomial,
        exponents_castLE h e he, ← ih]
    · simp [atHeight, he, toMvPolynomial_cons, ← ih]

variable [IsDomain R]

/-- Inclusion of the model fraction fields along an inclusion of the first variables. -/
noncomputable def Model.includeVars (h : n ≤ m) : M R n →+* M R m :=
  IsFractionRing.lift (g := (algebraMap (MvPolynomial (Fin m) R) (M R m)).comp
    (MvPolynomial.rename (Fin.castLE h)).toRingHom)
    ((IsFractionRing.injective (MvPolynomial (Fin m) R) _).comp
      (MvPolynomial.rename_injective (R := R) _ (Fin.castLE_injective h)))

@[simp] theorem Model.includeVars_polynomial (h : n ≤ m) (p : MvPolynomial (Fin n) R) :
    includeVars (R := R) h (algebraMap _ _ p) =
      algebraMap _ _ (MvPolynomial.rename (Fin.castLE h) p) :=
  IsFractionRing.lift_algebraMap _ _

namespace K

/-- Include the polynomial lists of a raw fraction at a taller height. -/
def Raw.atHeight (n : ℕ) (x : Raw R) : Raw R :=
  ⟨x.num.atHeight n, x.den.atHeight n⟩

@[simp] theorem Raw.value_atHeight (h : n ≤ m) (x : Raw R) :
    Raw.value m (x.atHeight n) = Model.includeVars h (Raw.value n x) := by
  simp [Raw.value, Raw.polyValue, Raw.atHeight, MPoly.Raw.toMvPolynomial_atHeight h, map_div₀]

/-- View a flat fraction at a taller height. -/
def includeAt (h : n ≤ m) : K R n → K R m :=
  Quotient.map (Raw.atHeight n) fun a b (hab : Raw.value n a = Raw.value n b) => by
    change Raw.value m _ = Raw.value m _
    rw [Raw.value_atHeight h, Raw.value_atHeight h, hab]

variable [DecidableEq R] [NormalizedGCDMonoid R] [Div R]

private theorem equiv_includeAt (h : n ≤ m) (x : K R n) :
    equiv (includeAt h x) = Model.includeVars h (equiv x) :=
  Quotient.inductionOn x (Raw.value_atHeight h)

/-- The inclusion at any taller height is a ring homomorphism. -/
def includeVars (h : n ≤ m) : K R n →+* K R m where
  toFun := includeAt h
  map_zero' := equiv.injective (by simp [equiv_includeAt])
  map_one' := equiv.injective (by simp [equiv_includeAt])
  map_add' _ _ := equiv.injective (by simp [equiv_includeAt])
  map_mul' _ _ := equiv.injective (by simp [equiv_includeAt])

/-- Include the field immediately below the newest generator. -/
def lift : K R n →+* K R (n + 1) := includeVars (Nat.le_succ n)

/-- Include constants as fractions with no variables at any height. -/
def ofConst : K R 0 →+* K R n := includeVars (Nat.zero_le n)

/-- The newest variable, with derivative specified by the tower. -/
def gen : K R (n + 1) := ofRaw (Raw.ofPoly (MPoly.Raw.X (n + 1) n))

@[simp] theorem equiv_lift (x : K R n) :
    equiv (lift x) = Model.includeVars (Nat.le_succ n) (equiv x) := equiv_includeAt _ _

@[simp] theorem equiv_gen :
    equiv (gen : K R (n + 1)) =
      algebraMap (MvPolynomial (Fin (n + 1)) R) _ (MvPolynomial.X (Fin.last n)) := by
  change Raw.value (n + 1) _ = _
  rw [Raw.value_ofPoly, Raw.polyValue]
  exact congrArg _ (MPoly.Raw.toMvPolynomial_X (R := R) (Fin.last n))

@[simp] theorem stepEquiv_gen :
    Model.stepEquiv R n (equiv (gen : K R (n + 1))) = RatFunc.X := by simp

/-- In the one-variable presentation every element of the lower field is a constant. -/
@[simp] theorem stepEquiv_lift (x : K R n) :
    Model.stepEquiv R n (equiv (lift x)) = RatFunc.C (equiv x) := by
  rw [equiv_lift]
  suffices h : (Model.stepEquiv R n).toRingHom.comp (Model.includeVars (Nat.le_succ n)) =
      RatFunc.C by exact DFunLike.congr_fun h (equiv x)
  apply IsFractionRing.ringHom_ext (A := MvPolynomial (Fin n) R)
  intro p
  have hp : Model.splitPolynomial R n (MvPolynomial.rename Fin.castSucc p) = Polynomial.C p := by
    induction p using MvPolynomial.induction_on with
    | C a => simp [Model.splitPolynomial, MvPolynomial.renameEquiv, MvPolynomial.finSuccEquiv_apply]
    | add p q hp hq => simp [map_add, hp, hq]
    | mul_X p i hp => simp [hp]
  change Model.stepEquiv R n (Model.includeVars _ (algebraMap _ _ p)) = _
  rw [Model.includeVars_polynomial, Model.stepEquiv_polynomial]
  change algebraMap _ _ ((Model.splitPolynomial R n (MvPolynomial.rename Fin.castSucc p)).map _) = _
  simp [hp]

end K

end SympyProofs.Calculus.Antiderivative
