module

public import SympyProofs.Sum.Gosper.Backend.Inverse

/-! Fixed-length vector implementation of the right-block matrix-vector product. -/

@[expose] public section

namespace Gosper.Algorithm

private theorem set_ofFn {α : Type*} {m : ℕ} (values : Fin m → α)
    (i : Fin m) (value : α) :
    (Vector.ofFn values).set i.val value = Vector.ofFn (Function.update values i value) := by
  apply Vector.ext
  intro j hj
  simp [Vector.getElem_set, Function.update, Fin.ext_iff, eq_comm]

private theorem set_foldl_ofFn {α : Type*} {m : ℕ} (entries : List (Fin m))
    (initial target : Fin m → α) :
    entries.foldl (fun a i => a.set i.val (target i)) (Vector.ofFn initial) =
      Vector.ofFn (fun i => if i ∈ entries then target i else initial i) := by
  induction entries generalizing initial with
  | nil => simp
  | cons i entries ih =>
    rw [List.foldl_cons, set_ofFn, ih]
    congr 1
    funext j
    by_cases hm : j ∈ entries
    · simp [hm]
    · by_cases hj : j = i <;> simp [hm, hj, Function.update]

variable {K : Type*} [Field K] {m n : ℕ}

/-- The nested vector loop computes the transformed right-hand side once. -/
theorem RrefResult.transform_rhs_vector_eq (r : RrefResult K m (n + m))
    (values : Fin m → K) :
    (Id.run do
      let mut transformed := Vector.replicate m (0 : K)
      for i in List.finRange m do
        let mut value := (0 : K)
        for k in List.finRange m do
          value := value + r.matrix i (Fin.natAdd n k) * values k
        transformed := transformed.set i.val value
      return transformed) = Vector.ofFn (r.rightMatrix.mulVec values) := by
  have hsum (i : Fin m) :
      (List.finRange m).foldl
        (fun value k => value + r.matrix i (Fin.natAdd n k) * values k) 0 =
      r.rightMatrix.mulVec values i := by
    rw [← List.foldl_map, ← List.sum_eq_foldl, ← List.ofFn_eq_map, List.sum_ofFn]
    rfl
  have hz : Vector.replicate m (0 : K) = Vector.ofFn (fun _ : Fin m => (0 : K)) := by
    apply Vector.ext
    simp
  simp [hsum, hz]
  simpa only [List.mem_finRange, ↓reduceIte] using
    set_foldl_ofFn (List.finRange m) (fun _ => (0 : K)) (r.rightMatrix.mulVec values)

end Gosper.Algorithm
