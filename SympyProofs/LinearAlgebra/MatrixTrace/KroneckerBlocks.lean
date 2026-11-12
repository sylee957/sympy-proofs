module

public import SympyProofs.LinearAlgebra.MatrixTrace.Kronecker

/-! Square-slice decompositions of traces of rectangular Kronecker factors.

Block `(i, j)` of `A ⊗ B` occupies rows `[i*p, (i+1)*p)` and columns
`[j*q, (j+1)*q)`. Their intersection determines a square slice of `B`.
The trace is the sum of `A i j` times the traces of these slices. Collecting
the slice traces in a matrix gives the smaller expression `trace (A * C(B))`.
-/

@[expose] public section

namespace Matrix

variable {R : Type*} {m n p q : ℕ}

/-- Length of the intersection of a Kronecker block row and block column. -/
def kroneckerTraceBlockSize (p q i j : ℕ) : ℕ :=
  min ((i + 1) * p) ((j + 1) * q) - max (i * p) (j * q)

private theorem traceBlock_bounds {i j : ℕ} (t : Fin (kroneckerTraceBlockSize p q i j)) :
    i * p ≤ max (i * p) (j * q) + t ∧
    j * q ≤ max (i * p) (j * q) + t ∧
    max (i * p) (j * q) + t < (i + 1) * p ∧
    max (i * p) (j * q) + t < (j + 1) * q := by
  have := t.is_lt
  unfold kroneckerTraceBlockSize at this
  omega

/-- The square slice of `B` cut out by the diagonal through block `(i, j)`.
An empty intersection gives a `0 × 0` matrix. -/
def kroneckerTraceBlock (B : Matrix (Fin p) (Fin q) R) (i j : ℕ) :
    Matrix (Fin (kroneckerTraceBlockSize p q i j))
      (Fin (kroneckerTraceBlockSize p q i j)) R :=
  B.submatrix
    (fun t => ⟨max (i * p) (j * q) + t - i * p, by
      have ht := traceBlock_bounds t
      simp only [Nat.add_mul, Nat.one_mul] at ht
      omega⟩)
    (fun t => ⟨max (i * p) (j * q) + t - j * q, by
      have ht := traceBlock_bounds t
      simp only [Nat.add_mul, Nat.one_mul] at ht
      omega⟩)

/-- The matrix of square-slice traces, transposed to pair with an `m × n` matrix. -/
def kroneckerTraceMatrix [AddCommMonoid R] (m n : ℕ)
    (B : Matrix (Fin p) (Fin q) R) : Matrix (Fin n) (Fin m) R :=
  fun j i => trace (kroneckerTraceBlock B i j)

@[simp]
theorem kroneckerTraceMatrix_apply [AddCommMonoid R]
    (B : Matrix (Fin p) (Fin q) R) (i : Fin m) (j : Fin n) :
    kroneckerTraceMatrix m n B j i = trace (kroneckerTraceBlock B i j) :=
  rfl

/-- Blocks disjoint from the diagonal contribute zero. -/
theorem trace_kroneckerTraceBlock_eq_zero [AddCommMonoid R]
    (B : Matrix (Fin p) (Fin q) R) (i j : ℕ)
    (h : min ((i + 1) * p) ((j + 1) * q) ≤ max (i * p) (j * q)) :
    trace (kroneckerTraceBlock B i j) = 0 := by
  have hs : kroneckerTraceBlockSize p q i j = 0 := Nat.sub_eq_zero_of_le h
  have : IsEmpty (Fin (kroneckerTraceBlockSize p q i j)) := by rw [hs]; infer_instance
  exact trace_eq_zero_of_isEmpty _

private theorem traceBlock_column_mono {i j i' j' : ℕ}
    (h : 0 < kroneckerTraceBlockSize p q i j)
    (h' : 0 < kroneckerTraceBlockSize p q i' j') (hi : i < i') : j ≤ j' := by
  by_contra hj
  have hrow : (i + 1) * p ≤ i' * p := Nat.mul_le_mul_right p (Nat.succ_le_of_lt hi)
  have hcol := Nat.mul_le_mul_right q (show j' + 1 ≤ j by omega)
  unfold kroneckerTraceBlockSize at h h'
  omega

/-- At most `m + n - 1` Kronecker blocks intersect the diagonal in a nonempty
square slice. The bound does not require the full product to be square. -/
theorem card_kroneckerTraceBlocks_le (m n p q : ℕ) :
    (Finset.univ.filter (fun ij : Fin m × Fin n =>
      0 < kroneckerTraceBlockSize p q ij.1 ij.2)).card ≤ m + n - 1 := by
  classical
  calc
    _ ≤ (Finset.range (m + n - 1)).card := by
      apply Finset.card_le_card_of_injOn (fun ij : Fin m × Fin n => ij.1.val + ij.2.val)
      · intro ij _
        simp only [Finset.mem_coe, Finset.mem_range]
        have hi := ij.1.is_lt
        have hj := ij.2.is_lt
        omega
      · intro ij hij kl hkl heq
        change ij.1.val + ij.2.val = kl.1.val + kl.2.val at heq
        have hij' := (Finset.mem_filter.mp hij).2
        have hkl' := (Finset.mem_filter.mp hkl).2
        have hi : ij.1.val = kl.1.val := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have := traceBlock_column_mono hij' hkl' hlt
            omega
          · have := traceBlock_column_mono hkl' hij' hgt
            omega
        exact Prod.ext (Fin.ext hi) (Fin.ext (by omega))
    _ = _ := Finset.card_range _

private def traceBlockIndex (i : Fin m) (j : Fin n)
    (t : Fin (kroneckerTraceBlockSize p q i j)) : Fin (m * p) :=
  ⟨max (i.val * p) (j.val * q) + t, by
    have ht := (traceBlock_bounds t).2.2.1
    have hi := Nat.mul_le_mul_right p (Nat.succ_le_of_lt i.is_lt)
    exact lt_of_lt_of_le ht hi⟩

private theorem traceBlockIndex_divNat (i : Fin m) (j : Fin n)
    (t : Fin (kroneckerTraceBlockSize p q i j)) :
    (traceBlockIndex i j t).divNat = i := by
  apply Fin.ext
  exact Nat.div_eq_of_lt_le (traceBlock_bounds t).1 (traceBlock_bounds t).2.2.1

private theorem traceBlockIndex_cast_divNat (h : m * p = n * q)
    (i : Fin m) (j : Fin n) (t : Fin (kroneckerTraceBlockSize p q i j)) :
    ((traceBlockIndex i j t).cast h).divNat = j := by
  apply Fin.ext
  exact Nat.div_eq_of_lt_le (traceBlock_bounds t).2.1 (traceBlock_bounds t).2.2.2

private theorem sum_traceBlockIndex [AddCommMonoid R] (h : m * p = n * q)
    (f : Fin (m * p) → R) :
    ∑ k, f k = ∑ i : Fin m, ∑ j : Fin n,
      ∑ t : Fin (kroneckerTraceBlockSize p q i j), f (traceBlockIndex i j t) := by
  rw [← Finset.sum_fiberwise Finset.univ
    (fun k : Fin (m * p) => (k.divNat, (k.cast h).divNat)) f,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  symm
  refine Finset.sum_bij (fun t _ => traceBlockIndex i j t) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro t _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Prod.ext (traceBlockIndex_divNat i j t) (traceBlockIndex_cast_divNat h i j t)
  · intro t _ u _ htu
    apply Fin.ext
    have := congrArg Fin.val htu
    change max (i.val * p) (j.val * q) + t.val =
      max (i.val * p) (j.val * q) + u.val at this
    omega
  · intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    have hi : k.val / p = i.val := congrArg (fun x => x.1.val) hk'
    have hj : k.val / q = j.val := congrArg (fun x => x.2.val) hk'
    have hp := k.modNat.is_lt
    have hq := (k.cast h).modNat.is_lt
    change k.val % p < p at hp
    change k.val % q < q at hq
    have hkp := Nat.mod_add_div k.val p
    have hkq := Nat.mod_add_div k.val q
    rw [hi, Nat.mul_comm p] at hkp
    rw [hj, Nat.mul_comm q] at hkq
    have ht : k.val - max (i.val * p) (j.val * q) <
        kroneckerTraceBlockSize p q i j := by
      simp only [kroneckerTraceBlockSize, Nat.add_mul, Nat.one_mul]
      omega
    refine ⟨⟨k.val - max (i.val * p) (j.val * q), ht⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    change max (i.val * p) (j.val * q) + (k.val - max (i.val * p) (j.val * q)) = k.val
    omega

/-- Decompose the trace into weighted traces of square slices of the second factor.
The factors may be rectangular, and zero dimensions are allowed. -/
theorem trace_kroneckerFin_eq_sum_traceBlock [Semiring R]
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin p) (Fin q) R)
    (h : m * p = n * q) :
    trace ((kroneckerFin A B).submatrix id (Fin.cast h)) =
      ∑ i : Fin m, ∑ j : Fin n, A i j * trace (kroneckerTraceBlock B i j) := by
  rw [trace_kroneckerFin_of_mul_eq_mul, sum_traceBlockIndex h]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [traceBlockIndex_divNat, traceBlockIndex_cast_divNat,
    trace, diag, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  congr 2
  · apply Fin.ext
    change (max (i.val * p) (j.val * q) + t.val) % p =
      max (i.val * p) (j.val * q) + t.val - i.val * p
    rw [Nat.mod_eq_sub_div_mul,
      Nat.div_eq_of_lt_le (traceBlock_bounds t).1 (traceBlock_bounds t).2.2.1]
  · apply Fin.ext
    change (max (i.val * p) (j.val * q) + t.val) % q =
      max (i.val * p) (j.val * q) + t.val - j.val * q
    rw [Nat.mod_eq_sub_div_mul,
      Nat.div_eq_of_lt_le (traceBlock_bounds t).2.1 (traceBlock_bounds t).2.2.2]

/-- A square Kronecker-product trace as the trace of an ordinary `m × m` product. -/
theorem trace_kroneckerFin_eq_trace_mul [Semiring R]
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin p) (Fin q) R)
    (h : m * p = n * q) :
    trace ((kroneckerFin A B).submatrix id (Fin.cast h)) =
      trace (A * kroneckerTraceMatrix m n B) := by
  rw [trace_kroneckerFin_eq_sum_traceBlock A B h]
  rfl

/-- Over a commutative semiring, the final trace can instead use an `n × n` product. -/
theorem trace_kroneckerFin_eq_trace_mul_comm [CommSemiring R]
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin p) (Fin q) R)
    (h : m * p = n * q) :
    trace ((kroneckerFin A B).submatrix id (Fin.cast h)) =
      trace (kroneckerTraceMatrix m n B * A) := by
  rw [trace_kroneckerFin_eq_trace_mul A B h, trace_mul_comm]

/-- The ordinary-product reduction with a cast-free diagonal-sum left-hand side. -/
theorem diagonalSum_kroneckerFin_eq_trace_mul [Semiring R]
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin p) (Fin q) R)
    (h : m * p = n * q) :
    diagonalSum (kroneckerFin A B) = trace (A * kroneckerTraceMatrix m n B) := by
  rw [← trace_submatrix_cast_eq_diagonalSum (kroneckerFin A B) h]
  exact trace_kroneckerFin_eq_trace_mul A B h

end Matrix
