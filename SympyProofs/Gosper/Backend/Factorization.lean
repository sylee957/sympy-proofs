module

public import SympyProofs.Gosper.Algorithm.Polynomial

/-! A `factor_list` result and the interpretation of its linear factors as roots.
The backend factors polynomials; natural-root enumeration is derived here. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial IsLocalization

variable {K : Type*} [Field K] [DecidableEq K]

/-- The contract for SymPy's `factor_list` tuple `(coefficient, factors)`.
Repeated factors are allowed, so grouping multiplicities is not part of the contract. -/
structure IsFactorization (p : K[X]) (f : K × List (K[X] × ℕ)) : Prop where
  coefficient_ne_zero : f.1 ≠ 0
  irreducible : ∀ z ∈ f.2, Irreducible z.1
  positive : ∀ z ∈ f.2, 0 < z.2
  reconstruct : C f.1 * (f.2.map fun z => z.1 ^ z.2).prod = p

/-- Mathlib factorization as a reference implementation of `factor_list`. -/
def referenceFactor (p : K[X]) : K × List (K[X] × ℕ) :=
  ⟨p.leadingCoeff, (UniqueFactorizationMonoid.normalizedFactors p).toList.map (fun q => (q, 1))⟩

theorem referenceFactor_valid (p : K[X]) (hp : p ≠ 0) : IsFactorization p (referenceFactor p) where
  coefficient_ne_zero := leadingCoeff_ne_zero.mpr hp
  irreducible z hz := by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
    exact ((Polynomial.mem_normalizedFactors_iff hp).mp (by simpa using hq)).1
  positive z hz := by
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hz
    exact Nat.zero_lt_one
  reconstruct := by
    simpa [referenceFactor, List.map_map] using leadingCoeff_mul_prod_normalizedFactors p

/-- For a linear polynomial `a*X+b`, its unique root is `-b/a`. -/
def linearRoot (p : K[X]) : Option K :=
  if p.natDegree = 1 then some (-p.coeff 0 / p.coeff 1) else none

omit [DecidableEq K] in
theorem linearRoot_eq_some (p : K[X]) (hp : Irreducible p) (a : K) :
    linearRoot p = some a ↔ p.eval a = 0 := by
  by_cases hd : p.natDegree = 1
  · have hc : p.coeff 1 ≠ 0 := by
      simpa [← hd] using leadingCoeff_ne_zero.mpr hp.ne_zero
    have he : p.eval a = p.coeff 1 * a + p.coeff 0 := by
      conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hd.le]
      simp
    simp only [linearRoot, hd, ↓reduceIte, Option.some.injEq, he]
    rw [div_eq_iff hc]
    constructor <;> intro h <;> linear_combination -h
  · simp only [linearRoot, hd, ↓reduceIte, reduceCtorEq, false_iff]
    exact hp.not_isRoot_of_natDegree_ne_one hd

omit [DecidableEq K] in
theorem IsFactorization.eval_eq_zero_iff {p : K[X]} {f : K × List (K[X] × ℕ)}
    (h : IsFactorization p f) (a : K) : p.eval a = 0 ↔ ∃ z ∈ f.2, z.1.eval a = 0 := by
  rw [← h.reconstruct, eval_mul, eval_C, mul_eq_zero]
  simp only [h.coefficient_ne_zero, false_or, eval_list_prod, List.map_map]
  rw [List.prod_eq_zero_iff]
  constructor
  · intro hz
    obtain ⟨z, hm, he⟩ := List.mem_map.mp hz
    exact ⟨z, hm, (pow_eq_zero_iff (Nat.ne_of_gt (h.positive z hm))).mp (by simpa using he)⟩
  · rintro ⟨z, hz, he⟩
    refine List.mem_map.mpr ⟨z, hz, ?_⟩
    simp [he, Nat.ne_of_gt (h.positive z hz)]

variable [CharZero K] [DecidablePred (IsInteger ℤ : K → Prop)]

/-- Read the root of a linear factor when it is a nonnegative integer. -/
def nonnegativeIntegerRoot (p : K[X]) : Option ℕ :=
  match linearRoot p with
  | none => none
  | some root =>
    if h : IsInteger ℤ root then
      let n : ℤ := Encodable.choose h
      if 0 ≤ n then some n.toNat else none
    else none

theorem nonnegativeIntegerRoot_eq_some (p : K[X]) (n : ℕ) :
    nonnegativeIntegerRoot p = some n ↔ linearRoot p = some (n : K) := by
  unfold nonnegativeIntegerRoot
  cases hr : linearRoot p with
  | none => simp
  | some root =>
    dsimp only
    by_cases hi : IsInteger ℤ root
    · simp only [dite_eq_left hi]
      let z : ℤ := Encodable.choose hi
      have hz : (z : K) = root := Encodable.choose_spec hi
      change (if 0 ≤ z then some z.toNat else none) = some n ↔ some root = some (n : K)
      simp only [Option.some.injEq]
      constructor
      · intro h
        split_ifs at h with hz0
        have hn : z.toNat = n := Option.some.inj h
        rw [← hz, ← hn, ← Int.cast_natCast, Int.toNat_of_nonneg hz0]
      · intro h
        have hzn : z = (n : ℤ) := Int.cast_injective
          (by simpa only [Int.cast_natCast] using hz.trans h)
        simp [hzn]
    · simp only [dite_eq_right hi, reduceCtorEq, Option.some.injEq, false_iff]
      intro h
      exact hi ⟨n, by simpa using h.symm⟩

/-- Extract linear factors, recognize natural roots, and discard duplicates.
This is the interpretation of factorization used by Gosper, not a backend operation. -/
def nonnegativeIntegerRootsFromFactors (factors : List (K[X] × ℕ)) : Finset ℕ :=
  (factors.filterMap fun z => nonnegativeIntegerRoot z.1).toFinset

omit [CharZero K] in
/-- Inserting roots in a loop gives the same finite set as filtering the factors. -/
theorem nonnegativeIntegerRootsFromFactors_foldl (factors : List (K[X] × ℕ))
    (roots : Finset ℕ) :
    (factors.foldl (fun roots factor =>
      (nonnegativeIntegerRoot factor.1).elim roots (fun n => insert n roots))
        roots) = roots ∪ nonnegativeIntegerRootsFromFactors factors := by
  induction factors generalizing roots with
  | nil => simp [nonnegativeIntegerRootsFromFactors]
  | cons factor factors ih =>
    cases h : nonnegativeIntegerRoot factor.1 <;>
      simp [List.foldl_cons, ih, nonnegativeIntegerRootsFromFactors,
        h, Finset.insert_union, Finset.union_insert]

theorem IsFactorization.mem_nonnegativeIntegerRoots
    {p : K[X]} {f : K × List (K[X] × ℕ)} (h : IsFactorization p f) (n : ℕ) :
    n ∈ nonnegativeIntegerRootsFromFactors f.2 ↔ p.eval (n : K) = 0 := by
  rw [h.eval_eq_zero_iff]
  simp only [nonnegativeIntegerRootsFromFactors, List.mem_toFinset, List.mem_filterMap,
    nonnegativeIntegerRoot_eq_some]
  constructor
  · rintro ⟨z, hz, he⟩
    exact ⟨z, hz, (linearRoot_eq_some z.1 (h.irreducible z hz) _).mp he⟩
  · rintro ⟨z, hz, he⟩
    exact ⟨z, hz, (linearRoot_eq_some z.1 (h.irreducible z hz) _).mpr he⟩

end Gosper.Algorithm
