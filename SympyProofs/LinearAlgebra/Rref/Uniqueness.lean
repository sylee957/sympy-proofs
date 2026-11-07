module

public import SympyProofs.LinearAlgebra.Rref.Normalized
public import Mathlib.LinearAlgebra.Matrix.Echelon.Basic

/-! Uniqueness of RREF matrices and functions, stated using Mathlib's predicates. -/

@[expose] public section

variable {F : Type*} [Field F] {m n : ℕ}

namespace SympyProofs.Rref

/-- A matrix satisfying Mathlib's RREF predicate admits a normalized certificate
with exactly the same entries. -/
theorem NormalizedRref.exists_valid_of_isReducedRowEchelon
    {A : Matrix (Fin m) (Fin n) F} (hA : A.IsReducedRowEchelon) :
    ∃ r : NormalizedRref F m n, r.matrix = A ∧ r.Valid A := by
  classical
  have hex : ∃ k : ℕ, ∀ i : Fin m, k ≤ i.val → A i = 0 :=
    ⟨m, by intro i hi; omega⟩
  let rank := Nat.find hex
  have hrank : rank ≤ m := Nat.find_min' hex (by intro i hi; omega)
  have hzero : ∀ i : Fin m, rank ≤ i.val → A i = 0 := Nat.find_spec hex
  have hnonzero (i : Fin rank) : A (Fin.castLE hrank i) ≠ 0 := by
    intro hz
    have hle : rank ≤ i.val := Nat.find_min' hex (by
      intro k hik
      by_cases he : k.val = i.val
      · have hki : k = Fin.castLE hrank i := Fin.ext he
        simpa [hki] using hz
      · exact hA.isRowEchelon.row_eq_zero_of_lt
          (show Fin.castLE hrank i < k by change i.val < k.val; omega) hz)
    exact (Nat.not_le_of_lt i.isLt) hle
  choose p hp using fun i => Matrix.row_ne_zero_iff_exists_isLeadingEntry.mp (hnonzero i)
  have hlead (i : Fin m) (q : Fin n) (hq : (List.ofFn p)[i.val]? = some q) :
      A.IsLeadingEntry i q := by
    have hi : i.val < rank := by
      simpa using (List.getElem?_eq_some_iff.mp hq).1
    have he : p ⟨i.val, hi⟩ = q := by
      simpa [List.getElem?_eq_getElem, hi] using hq
    simpa [he] using hp ⟨i.val, hi⟩
  refine ⟨⟨A, List.ofFn p, by simpa using hrank⟩, rfl, ?_⟩
  constructor
  · change (List.ofFn p).Pairwise (· < ·)
    rw [List.pairwise_ofFn]
    intro i k hik
    by_contra hle
    exact (hp k).2 (hA.isRowEchelon
      (show Fin.castLE hrank i < Fin.castLE hrank k from hik)
      (fun j hj => (hp i).1 j (lt_of_lt_of_le hj (not_lt.mp hle))))
  · intro i q hq k
    change A k q = if k = i then 1 else 0
    by_cases hki : k = i
    · simpa [hki] using hA.eq_one (hlead i q hq)
    · simpa [hki] using hA.eq_zero_of_ne_of_isLeadingEntry hki (hlead i q hq)
  · intro i q hq
    exact (hlead i q hq).1
  · intro i hi
    apply hzero i
    have : (List.ofFn p).length ≤ i.val := List.getElem?_eq_none_iff.mp hi
    simpa using this
  · intro x
    rfl

end SympyProofs.Rref

namespace Matrix

/-- Reduced row echelon matrices of the same shape are equal when their kernels
are equal. No full-rank or squareness assumption is needed. -/
theorem IsReducedRowEchelon.eq_of_ker_eq {A B : Matrix (Fin m) (Fin n) F}
    (hA : A.IsReducedRowEchelon) (hB : B.IsReducedRowEchelon)
    (hker : LinearMap.ker A.mulVecLin = LinearMap.ker B.mulVecLin) : A = B := by
  obtain ⟨r, hr, hrv⟩ :=
    SympyProofs.Rref.NormalizedRref.exists_valid_of_isReducedRowEchelon hA
  obtain ⟨s, hs, hsv⟩ :=
    SympyProofs.Rref.NormalizedRref.exists_valid_of_isReducedRowEchelon hB
  have hsv' : s.Valid A := by
    refine { hsv with kernel_iff := ?_ }
    intro x
    change x ∈ LinearMap.ker A.mulVecLin ↔ s.matrix.mulVec x = 0
    rw [hker]
    exact hsv.kernel_iff x
  simpa only [hr, hs] using r.normalized_eq s hrv hsv'

end Matrix

namespace SympyProofs.Rref

/-- Any two matrix-valued functions that return RREF and preserve kernels agree
on every input, hence are equal as functions. -/
theorem rref_function_unique
    (f g : Matrix (Fin m) (Fin n) F → Matrix (Fin m) (Fin n) F)
    (hf : ∀ A, (f A).IsReducedRowEchelon)
    (hfker : ∀ A, LinearMap.ker (f A).mulVecLin = LinearMap.ker A.mulVecLin)
    (hg : ∀ A, (g A).IsReducedRowEchelon)
    (hgker : ∀ A, LinearMap.ker (g A).mulVecLin = LinearMap.ker A.mulVecLin) :
    f = g := by
  funext A
  exact (hf A).eq_of_ker_eq (hg A) ((hfker A).trans (hgker A).symm)

end SympyProofs.Rref
