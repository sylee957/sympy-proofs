module

public import SympyProofs.LinearAlgebra.Rref.Invariants
public import SympyProofs.LinearAlgebra.Rref.Uniqueness

/-! Verification of the imperative RREF loops and public correctness and uniqueness
theorems. The mathematical row-operation invariants are in `Rref.Invariants`. -/

@[expose] public section

set_option experimental.vcgen true

namespace SympyProofs.Rref
namespace RrefAlgorithm

private theorem not_mem_prefix {k : ℕ} {pref suff : List (Fin k)} {i : Fin k}
    (hs : List.finRange k = pref ++ i :: suff) : i ∉ pref := by
  have hn : (pref ++ i :: suff).Nodup := hs ▸ List.nodup_finRange k
  exact fun h => (List.nodup_append.mp hn).2.2 i h i (by simp) rfl

private theorem index_eq_length {k : ℕ} {pref suff : List (Fin k)} {i : Fin k}
    (hs : List.finRange k = pref ++ i :: suff) : i.val = pref.length := by
  have hn : pref.length < k := by
    have := congrArg List.length hs
    simp only [List.length_finRange, List.length_append, List.length_cons] at this
    omega
  have he : (List.finRange k)[pref.length]? = some i := by simp [hs]
  have he' := congrArg (Option.map Fin.val) he
  simpa [List.getElem?_eq_getElem, hn] using he'.symm

private theorem mem_range (lo hi i : ℕ) :
    i ∈ ForIn.toList ([lo:hi] : Std.Legacy.Range) ↔ lo ≤ i ∧ i < hi := by
  rw [Std.Internal.LawfulMemForInId.mem_toList_iff]
  change (lo ≤ i ∧ i < hi ∧ (i - lo) % 1 = 0) ↔ _
  omega

private theorem range_not_mem_prefix {lo hi i : ℕ} {pref suff : List ℕ}
    (hs : ForIn.toList ([lo:hi] : Std.Legacy.Range) = pref ++ i :: suff) : i ∉ pref := by
  have hn : (pref ++ i :: suff).Nodup := by
    rw [← hs]
    simpa using (List.nodup_range' (s := lo) (n := hi - lo))
  exact fun h => (List.nodup_append.mp hn).2.2 i h i (by simp) rfl

variable {F : Type*} [Field F] {m n : ℕ}

/-- The suffix normalization loop and direct pivot assignment normalize the whole row. -/
private theorem normalizedPivot_finish {rows : Vector (Vector F n) m}
    {c : Fin n} {p : Fin m} {a : F} {done : Vector F n}
    (ha : a = rows[p.val][c.val]) (hp : rows[p.val][c.val] ≠ 0)
    (hz : ∀ j : Fin n, j.val < c.val → rows[p.val][j.val] = 0)
    (hdone : ∀ j : Fin n, done[j.val] =
      if c.val + 1 ≤ j.val then rows[p.val][j.val] * a⁻¹ else rows[p.val][j.val]) :
    done.set c.val 1 = normalizedPivot rows c p := by
  apply Vector.ext
  intro j hj
  let k : Fin n := ⟨j, hj⟩
  have hd := hdone k
  change done[j] = (if c.val + 1 ≤ j then rows[p.val][j] * a⁻¹ else rows[p.val][j]) at hd
  by_cases hc : c.val = j
  · subst j
    simp [normalizedPivot, hp]
  · rw [Vector.getElem_set_ne c.isLt hj hc, hd]
    by_cases hle : c.val + 1 ≤ j
    · simp [normalizedPivot, hle, ha, div_eq_mul_inv]
    · have hjc : j < c.val := by omega
      have hzj : rows[p.val][j] = 0 := hz k hjc
      simp [normalizedPivot, hle, hzj]

end RrefAlgorithm

section FieldAlgorithm

variable {F : Type*} [Field F] [DecidableEq F] {m n : ℕ}

open RrefAlgorithm in
open scoped Std.WP in
/-- The imperative algorithm produces unit pivots, increasing pivot columns, and trailing zero rows. -/
theorem rref_spec (A : Vector (Vector F n) m) :
    ∃ rank, DenseInvariant (toMatrix A) (rref A).rows (rref A).pivots n rank := by
  generalize he : rref A = result
  apply Std.WP.Id.of_run_eq_wp he
  vcgen invariants
  · fun pref _ (rows, pivots, rank) => DenseInvariant (toMatrix A) rows pivots pref.length rank
  · by
    rename_i pref c suff hs before pivots rank hi rest hbound
    exact fun pref _ (selected, a) =>
      (∀ r, selected = some r → rank ≤ r.val ∧ before[r.val][c.val] ≠ 0 ∧ a = before[r.val][c.val]) ∧
      (selected = none → ∀ i : Fin m, i.val ∈ pref → before[i.val][c.val] = 0)
  · by
    rename_i cols c cs hcs before pivots rank hc rest hbound selectedValue a hscan r hselected
    exact fun pref _ entry => ∀ j : Fin n,
      entry[j.val] = if j.val ∈ pref then rows[p.val][j.val] * scale else rows[p.val][j.val]
  · by
    rename_i cols c cs hcs before pivots rank hc rest hbound selectedValue a hscan r hselected swapped initialPivot done hdone
    exact fun pref _ current => ∀ i : Fin m,
      current[i.val] = if i ∈ pref then (crossRows rows c p)[i.val] else rows[i.val]
  · fun pref _ entry => ∀ j : Fin n,
      entry[j.val] = if j.val ∈ pref then row[j.val] - b * pivot[j.val] else row[j.val]
  case vc1 =>
    refine ⟨?_, by simp, by intro i; simp +zetaDelta,
      by intro i q; simp +zetaDelta, by intro i k q t; simp +zetaDelta⟩
    constructor <;> simp +zetaDelta
  case vc2 =>
    rename_i rows pivots rank h rest
    exact ⟨rank, by simpa using h⟩
  case vc3 => simp +zetaDelta
  case vc4 => simp +zetaDelta
  case vc5 => simp
  case vc6 =>
    rename_i cols c cs hcs before oldPivots rank0 hc rest hbound selectedValue a hscan r hselected
      swapped initialPivot done hdone after hafter
    have hp := hscan.1 r hselected
    have hpn : oldPivots[p.val] = none := (hc.unused_iff p).mpr (by simp [p])
    have hrn : oldPivots[r.val] = none := (hc.unused_iff r).mpr hp.1
    have hs : DenseInvariant (toMatrix A) swapped oldPivots c.val rank0 := by
      simpa [index_eq_length hcs] using hc.swap_unused p r hpn hrn
    have ha : swapped[p.val][c.val] ≠ 0 := by simpa [swapped] using hp.2.1
    have hpa : a = swapped[p.val][c.val] := by simpa [swapped] using hp.2.2
    have hpeq : pivot = normalizedPivot swapped c p := by
      apply normalizedPivot_finish hpa ha (hs.unused p hpn)
      intro j
      simpa [mem_range, scale, j.isLt] using hdone j
    have heq : after = crossRows (normalizedRows swapped c p) c p := by
      apply Vector.ext
      intro i hi
      simpa [rows, hpeq, normalizedRows] using hafter ⟨i, hi⟩
    simpa [pivots, rank, heq, index_eq_length hcs] using hs.advance p rfl ha
  case vc7 =>
    rename_i cols c cs hcs before pivots rank hc rest hbound selectedValue a hscan r hselected
      swapped initialPivot done hdone pref i suff hs current hcurrent heq
    have hrow : current[i.val] = rows[i.val] := by simpa [not_mem_prefix hs] using hcurrent i
    have hip : i = p := by simpa using heq
    have hsame : (crossRows rows c p)[i.val] = rows[i.val] := by
      apply Vector.ext
      intro j hj
      simp [crossRows, hip]
    intro k
    by_cases hki : k = i
    · subst k
      simp [hsame, hrow]
    · simpa [hki] using hcurrent k
  case vc8 =>
    rename_i cols c cs hcs before pivots rank hc rest hbound selectedValue a hscan r hselected
      swapped initialPivot done hdone pref i suff hs current hcurrent hne hz
    have hrow : current[i.val] = rows[i.val] := by simpa [not_mem_prefix hs] using hcurrent i
    have hip : i ≠ p := by simpa using hne
    have hpc : rows[p.val][c.val] = 1 := by simp [rows, pivot]
    have hzero : rows[i.val][c.val] = 0 := by simpa [b, hrow] using hz
    have hsame : (crossRows rows c p)[i.val] = rows[i.val] := by
      apply Vector.ext
      intro j hj
      simp [crossRows, hip, hpc, hzero]
    intro k
    by_cases hki : k = i
    · subst k
      simp [hsame, hrow]
    · simpa [hki] using hcurrent k
  case vc9 => simp
  case vc10 =>
    rename_i cols c cs hcs before pivots rank hc rest hbound selectedValue a hscan r hselected
      swapped initialPivot normalized hnormalized start pref i suff hs current hcurrent hne hnz initialRow done hdone
    have hrow : current[i.val] = start[i.val] := by simpa [not_mem_prefix hs] using hcurrent i
    have hip : i ≠ p := by simpa using hne
    have hp := hscan.1 r hselected
    have hpn : pivots[p.val] = none := (hc.unused_iff p).mpr (by simp [p])
    have hrn : pivots[r.val] = none := (hc.unused_iff r).mpr hp.1
    have hswap : DenseInvariant (toMatrix A) swapped pivots c.val rank := by
      simpa [index_eq_length hcs] using hc.swap_unused p r hpn hrn
    have hpa : a = swapped[p.val][c.val] := by simpa [swapped] using hp.2.2
    have ha : swapped[p.val][c.val] ≠ 0 := by simpa [swapped] using hp.2.1
    have hpeq : pivot = normalizedPivot swapped c p := by
      apply normalizedPivot_finish hpa ha (hswap.unused p hpn)
      intro j
      simpa [mem_range, scale, j.isLt] using hnormalized j
    have hpzero (j : Fin n) (hj : j.val < c.val) : pivot[j.val] = 0 := by
      simp [hpeq, normalizedPivot, hswap.unused p hpn j hj]
    have hpc : start[p.val][c.val] = 1 := by simp [start, pivot]
    have hpr : start[p.val] = pivot := by simp [start]
    have hcross (j : Fin n) : (crossRows start c p)[i.val][j.val] =
        current[i.val][j.val] - b * pivot[j.val] := by
      rw [crossRows_get, ite_eq_right hip, hpc, one_mul, hpr, ← hrow]
    have hdone' : row = (crossRows start c p)[i.val] := by
      apply Vector.ext
      intro j hj
      rw [hcross ⟨j, hj⟩]
      by_cases hjc : c.val = j
      · subst j
        simp [row, pivot, b]
      · have hd := hdone ⟨j, hj⟩
        by_cases hle : c.val + 1 ≤ j
        · simpa only [row, Vector.getElem_set_ne c.isLt hj hjc, mem_range, hle,
            hj, and_self, ite_true, initialRow] using hd
        · have hz : pivot[j] = 0 := hpzero ⟨j, hj⟩ (by change j < c.val; omega)
          simpa only [row, Vector.getElem_set_ne c.isLt hj hjc, mem_range, hle,
            false_and, ite_false, initialRow, hz, mul_zero, sub_zero] using hd
    intro k
    by_cases hik : i = k
    · subst k
      simp [rows, hdone']
    · have hv : i.val ≠ k.val := fun he => hik (Fin.ext he)
      simpa [rows, hv, Ne.symm hik] using hcurrent k
  case vc11 =>
    rename_i initialRow pref j suff hs entry hentry
    have hnot := range_not_mem_prefix hs
    have hjn : j < n := (mem_range _ _ _).mp (by rw [hs]; simp) |>.2
    have heq : entry[j] = initialRow[j] := by simpa [hnot] using hentry ⟨j, hjn⟩
    intro k
    by_cases hjk : j = k.val
    · simp [row, ← hjk, heq]
    · simpa [row, hjk, Ne.symm hjk] using hentry k
  case vc12 =>
    rename_i pref j suff hs entry hentry
    have hnot := range_not_mem_prefix hs
    have hjn : j < n := (mem_range _ _ _).mp (by rw [hs]; simp) |>.2
    have heq : entry[j] = rows[p.val][j] := by simpa [hnot] using hentry ⟨j, hjn⟩
    intro k
    by_cases hjk : j = k.val
    · simp [pivot, ← hjk, heq]
    · simpa [pivot, hjk, Ne.symm hjk] using hentry k
  case vc13 =>
    rename_i pref c suff hs rows pivots rank hi rest hbound selectedValue a hscan missing hmissing hselected
    have hnone : missing = none := by cases missing <;> simp_all
    have hzero (i : Fin m) (hip : pivots[i.val] = none) : rows[i.val][c.val] = 0 :=
      hscan.2 (hselected.trans hnone) i ((mem_range _ _ _).mpr ⟨(hi.unused_iff i).mp hip, i.isLt⟩)
    have hc := index_eq_length hs
    have h : DenseInvariant (toMatrix A) rows pivots c.val rank := by simpa [hc] using hi
    have hnext : DenseInvariant (toMatrix A) rows pivots (c.val + 1) rank := by
      refine { h with known := ?_, unused := ?_ }
      · intro i p hip
        exact Nat.lt_succ_of_lt (h.known i p hip)
      · intro i hip j hj
        by_cases hjc : j = c
        · subst j
          exact hzero i hip
        · have hjlt : j.val < c.val := by
            have : j.val ≠ c.val := fun he => hjc (Fin.ext he)
            omega
          exact h.unused i hip j hjlt
    simpa [hc] using hnext
  case vc14 =>
    rename_i cols c cs hcs rows pivots rank hc rest hbound pref i suff hs selectedValue a hscan hz
    refine ⟨hscan.1, ?_⟩
    intro hnone k hk
    simp only [List.mem_append, List.mem_singleton] at hk
    rcases hk with hk | hk
    · exact hscan.2 hnone k hk
    · simpa [hk] using hz
  case vc15 =>
    rename_i cols c cs hcs rows pivots rank hc rest hbound selectedInitial pref i suff hs selectedValue a0 hscan hnz
    have hm : rank ≤ i ∧ i < m := (mem_range _ _ _).mp (by rw [hs]; simp)
    simp_all +zetaDelta
  case vc16 =>
    rename_i cols c cs hcs rows pivots rank hc rest hbound
    simpa using hc.complete (by omega)

/-- The returned buffers satisfy the completed elimination invariant. -/
theorem rref_valid (A : Vector (Vector F n) m) :
    RrefAlgorithm.Invariant (toMatrix A) (rref A).rows (rref A).pivots n := by
  obtain ⟨rank, h⟩ := rref_spec A
  exact h.toInvariant

/-- The computed rows satisfy Mathlib's standard RREF predicate. -/
theorem rref_isReducedRowEchelon (A : Vector (Vector F n) m) :
    (toMatrix (rref A).rows).IsReducedRowEchelon := by
  obtain ⟨rank, h⟩ := rref_spec A
  exact h.isReducedRowEchelon

/-- The computed rows preserve the input's kernel. -/
theorem rref_kernel_iff (A : Vector (Vector F n) m) (x : Fin n → F) :
    (toMatrix A).mulVec x = 0 ↔ (toMatrix (rref A).rows).mulVec x = 0 :=
  (rref_valid A).kernel x

/-- The input and computed rows have equal kernels as subspaces. -/
theorem rref_ker_eq (A : Vector (Vector F n) m) :
    LinearMap.ker (toMatrix A).mulVecLin =
      LinearMap.ker (toMatrix (rref A).rows).mulVecLin := by
  ext x
  exact rref_kernel_iff A x

/-- Any RREF matrix with the input's kernel equals the computed matrix. -/
theorem rref_unique (A : Vector (Vector F n) m) (B : Matrix (Fin m) (Fin n) F)
    (hB : B.IsReducedRowEchelon)
    (hker : LinearMap.ker B.mulVecLin = LinearMap.ker (toMatrix A).mulVecLin) :
    B = toMatrix (rref A).rows :=
  hB.eq_of_ker_eq (rref_isReducedRowEchelon A) (hker.trans (rref_ker_eq A))

/-- Every matrix-valued RREF function preserving kernels agrees with this algorithm,
after materializing its input and viewing its output as a matrix. -/
theorem rref_function_eq
    (f : Matrix (Fin m) (Fin n) F → Matrix (Fin m) (Fin n) F)
    (hf : ∀ A, (f A).IsReducedRowEchelon)
    (hker : ∀ A, LinearMap.ker (f A).mulVecLin = LinearMap.ker A.mulVecLin) :
    f = fun A => toMatrix (rref (Vector.ofFn fun i => Vector.ofFn (A i))).rows := by
  funext A
  have hview : toMatrix (Vector.ofFn fun i => Vector.ofFn (A i)) = A := by
    funext i j
    simp [toMatrix]
  apply rref_unique _ _ (hf A)
  simpa only [hview] using hker A

/-- The returned pivot metadata agrees exactly with Mathlib's leading entries. -/
theorem rref_isLeadingEntry_iff (A : Vector (Vector F n) m) (i : Fin m) (p : Fin n) :
    (toMatrix (rref A).rows).IsLeadingEntry i p ↔ (rref A).pivots[i.val] = some p :=
  (rref_valid A).isLeadingEntry_iff i p

/-- RREF, kernel preservation, and correct pivot metadata uniquely determine the
entire output of the algorithm. -/
theorem rref_output_unique (A : Vector (Vector F n) m) (out : RrefOutput F m n)
    (hout : (toMatrix out.rows).IsReducedRowEchelon)
    (hker : LinearMap.ker (toMatrix out.rows).mulVecLin =
      LinearMap.ker (toMatrix A).mulVecLin)
    (hpivots : ∀ (i : Fin m) (p : Fin n),
      (toMatrix out.rows).IsLeadingEntry i p ↔ out.pivots[i.val] = some p) :
    out = rref A := by
  have hmatrix := rref_unique A (toMatrix out.rows) hout hker
  have hrows : out.rows = (rref A).rows := by
    apply Vector.ext
    intro i hi
    apply Vector.ext
    intro j hj
    exact congrFun (congrFun hmatrix ⟨i, hi⟩) ⟨j, hj⟩
  have hp : out.pivots = (rref A).pivots := by
    apply Vector.ext
    intro i hi
    apply Option.ext
    intro p
    rw [← hpivots ⟨i, hi⟩ p, hmatrix, rref_isLeadingEntry_iff]
  exact congrArg₂ RrefOutput.mk hrows hp

/-- Any implementation with the same input and output types satisfying the RREF,
kernel, and pivot conditions is equal to `rref` as a function. -/
theorem rref_algorithm_unique
    (f : Vector (Vector F n) m → RrefOutput F m n)
    (hf : ∀ A, (toMatrix (f A).rows).IsReducedRowEchelon)
    (hker : ∀ A, LinearMap.ker (toMatrix (f A).rows).mulVecLin =
      LinearMap.ker (toMatrix A).mulVecLin)
    (hpivots : ∀ A (i : Fin m) (p : Fin n),
      (toMatrix (f A).rows).IsLeadingEntry i p ↔ (f A).pivots[i.val] = some p) :
    f = rref := by
  funext A
  exact rref_output_unique A (f A) (hf A) (hker A) (hpivots A)

/-- Every recorded pivot is one. -/
theorem rref_pivot_eq_one (A : Vector (Vector F n) m) (i : Fin m) (p : Fin n)
    (hp : (rref A).pivots[i.val] = some p) : (rref A).rows[i.val][p.val] = 1 := by
  obtain ⟨rank, h⟩ := rref_spec A
  exact h.monic i p hp

/-- Pivot columns increase strictly with the row index. -/
theorem rref_pivots_increasing (A : Vector (Vector F n) m) (i k : Fin m) (p q : Fin n)
    (hik : i < k) (hp : (rref A).pivots[i.val] = some p) (hq : (rref A).pivots[k.val] = some q) : p < q := by
  obtain ⟨rank, h⟩ := rref_spec A
  exact h.ordered i k p q hik hp hq

/-- Materializing a function matrix gives the same correctness specification. -/
theorem rref_valid_ofFn (A : Matrix (Fin m) (Fin n) F) :
    let input := Vector.ofFn fun i => Vector.ofFn (A i)
    RrefAlgorithm.Invariant A (rref input).rows (rref input).pivots n := by
  have hview : toMatrix (Vector.ofFn fun i => Vector.ofFn (A i)) = A := by
    funext i j
    simp [toMatrix]
  simpa only [hview] using rref_valid (Vector.ofFn fun i => Vector.ofFn (A i))

end FieldAlgorithm

end SympyProofs.Rref
