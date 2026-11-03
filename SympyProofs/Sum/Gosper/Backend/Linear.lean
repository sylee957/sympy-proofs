module

public import SympyProofs.Sum.Gosper.Backend.Term

/-! Integer-ratio recognition, matrix construction, and fraction-free RREF over an
integral domain. Runtime operations stay in the domain; reduction correctness is
checked in its canonical fraction field. -/

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

/-- A fraction-free reduction of `[A | I]` remains valid in every field into
which the coefficient domain embeds. -/
theorem TermBackend.rref_valid_augmentedIdentity (backend : TermBackend K W)
    (hbackend : backend.Valid) {E : Type*} [Field E]
    (A : Matrix (Fin m) (Fin n) K) (f : K →+* E) (hf : Function.Injective f) :
    ((backend.rref (augmentedIdentity A)).map f).Valid
      (augmentedIdentity (A.map f)) := by
  let e : FractionRing K →+* E := IsFractionRing.lift hf
  have he : e.comp (algebraMap K (FractionRing K)) = f := by
    ext x
    exact IsFractionRing.lift_algebraMap hf x
  have hbase := hbackend.rref_valid (augmentedIdentity A)
  rw [augmentedIdentity_map_ring] at hbase
  have h := RrefResult.map_valid_augmentedIdentity
    (A.map (algebraMap K (FractionRing K)))
    ((backend.rref (augmentedIdentity A)).map (algebraMap K (FractionRing K))) hbase e
  have hA : (A.map (algebraMap K (FractionRing K))).map e = A.map f := by
    ext i j
    exact IsFractionRing.lift_algebraMap hf (A i j)
  simpa only [RrefResult.map_map, he, hA] using h

/-- Filling a list of entries copies the target matrix at exactly those positions. -/
theorem TermBackend.setElement_foldl_apply (backend : TermBackend K W)
    (h : backend.Valid) (entries : List (Fin m × Fin n))
    (initial target : Matrix (Fin m) (Fin n) K) (i : Fin m) (j : Fin n) :
    (entries.foldl (fun M pos => backend.setElement M pos.1 pos.2 (target pos.1 pos.2))
      initial) i j = if (i, j) ∈ entries then target i j else initial i j := by
  induction entries generalizing initial with
  | nil => simp
  | cons pos entries ih =>
      rw [List.foldl_cons, ih, h.setElement_apply]
      by_cases hm : (i, j) ∈ entries
      · simp [hm]
      · by_cases hi : i = pos.1 <;> by_cases hj : j = pos.2 <;>
          simp_all [Prod.ext_iff]

/-- Fill the coefficient block and identity diagonal to construct `[A | I]`. -/
theorem TermBackend.fill_identity_augmented_eq (backend : TermBackend K W)
    (h : backend.Valid) (A : Matrix (Fin m) (Fin n) K) :
    (Id.run do
      let mut M := backend.zeros m (n + m)
      for i in List.finRange m do
        for j in List.finRange n do
          M := backend.setElement M i (j.castAdd m) (A i j)
        M := backend.setElement M i (Fin.natAdd n i) 1
      return M) = augmentedIdentity A := by
  let entries := (List.finRange m).flatMap fun i =>
    ((List.finRange n).map fun j => (i, j.castAdd m)) ++ [(i, Fin.natAdd n i)]
  have he : (Id.run do
      let mut M := backend.zeros m (n + m)
      for i in List.finRange m do
        for j in List.finRange n do
          M := backend.setElement M i (j.castAdd m) (A i j)
        M := backend.setElement M i (Fin.natAdd n i) 1
      return M) =
      entries.foldl (fun M pos =>
        backend.setElement M pos.1 pos.2 (augmentedIdentity A pos.1 pos.2))
        (backend.zeros m (n + m)) := by
    simp [entries, List.foldl_flatMap, List.foldl_append, List.foldl_map, augmentedIdentity]
  rw [he]
  ext i j
  rw [backend.setElement_foldl_apply h]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp [entries, augmentedIdentity]
  · by_cases hij : i = j
    · subst j
      simp [entries, augmentedIdentity]
    · simp [entries, augmentedIdentity, h.zeros_eq, hij]


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
