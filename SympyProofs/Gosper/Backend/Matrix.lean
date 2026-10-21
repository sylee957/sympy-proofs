module

public import SympyProofs.Gosper.Backend.Basic

/-! Correctness of matrix construction and solution extraction through backend operations. -/

@[expose] public section

namespace Gosper.Algorithm

variable {K : Type*} [Field K] {m n : ℕ}

/-- Filling a list of entries copies the target matrix at exactly those positions. -/
theorem Backend.setElement_foldl_apply (backend : Backend K) (h : backend.Valid)
    (entries : List (Fin m × Fin n)) (initial target : Matrix (Fin m) (Fin n) K)
    (i : Fin m) (j : Fin n) :
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

/-- Writing every coefficient column and then the right-hand side constructs `[A | b]`. -/
theorem Backend.fill_augmented_eq (backend : Backend K) (h : backend.Valid)
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) :
    (Id.run do
      let mut M := backend.zeros m (n + 1)
      for i in List.finRange m do
        for j in List.finRange n do
          M := backend.setElement M i j.castSucc (A i j)
        M := backend.setElement M i (Fin.last n) (b i)
      return M) = augmented A b := by
  let entries := (List.finRange m).flatMap fun i =>
    ((List.finRange n).map fun j => (i, j.castSucc)) ++ [(i, Fin.last n)]
  have he : (Id.run do
      let mut M := backend.zeros m (n + 1)
      for i in List.finRange m do
        for j in List.finRange n do
          M := backend.setElement M i j.castSucc (A i j)
        M := backend.setElement M i (Fin.last n) (b i)
      return M) =
      entries.foldl (fun M pos => backend.setElement M pos.1 pos.2 (augmented A b pos.1 pos.2))
        (backend.zeros m (n + 1)) := by
    simp [entries, List.foldl_flatMap, List.foldl_append, List.foldl_map, augmented]
  rw [he]
  ext i j
  rw [backend.setElement_foldl_apply h]
  have hm : (i, j) ∈ entries := by
    apply List.mem_flatMap.mpr
    refine ⟨i, List.mem_finRange i, ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp
    · simp
  simp [hm]

/-- Read the augmented column once and reconstruct the polynomial from its pivot rows. -/
theorem Backend.reconstruct_eq [DecidableEq K] (backend : Backend K) (h : backend.Valid)
    (r : RrefResult K m (n + 1)) (hlast : Fin.last n ∉ r.pivots) :
    (Id.run do
      let rhs := backend.getCol r.matrix (Fin.last n)
      let mut x : Polynomial K := 0
      for ⟨(pivot, row), hp⟩ in r.pivots.zipIdx.attach do
        let row : Fin m := ⟨row, lt_of_lt_of_le (List.mem_zipIdx' hp).1 r.length_le⟩
        x := x + Polynomial.monomial (pivot : ℕ) (rhs row / r.denominator)
      return x) = Polynomial.ofFn n r.solution := by
  rw [r.ofFn_solution_eq_pivots hlast, List.mapFinIdx_eq_zipIdx_map,
    List.sum_eq_foldl, List.foldl_map]
  simp [h.getCol_apply]

end Gosper.Algorithm
