module

public import SympyProofs.Gosper.Basic

/-! # Gosper's signed degree bound, Cases 1 and 2 on p. 41

`paperDegreeBound` retains negative bounds and integer exceptional roots.
`solution_intDegree_le` bounds every nonzero polynomial solution;
`no_polynomial_solution_of_degreeBound_neg` gives the paper's early rejection.
`degreeBound` converts the bound to a natural number for the coefficient matrix.
-/

@[expose] public section
noncomputable section

namespace Gosper

open Polynomial Finset.HasAntidiagonal

variable {K : Type*} [Field K]

theorem coeff_taylor_top (p : K[X]) (a : K) (n : ℕ) (hp : p.natDegree ≤ n) :
    (taylor a p).coeff n = p.coeff n := by
  rcases hp.eq_or_lt with h | h
  · rw [← h, coeff_taylor_natDegree, coeff_natDegree]
  · rw [coeff_eq_zero_of_natDegree_lt h,
      coeff_eq_zero_of_natDegree_lt (by simpa using h)]

theorem coeff_taylor_next (p : K[X]) (a : K) (n : ℕ) (hp : p.natDegree ≤ n + 1) :
    (taylor a p).coeff n = p.coeff n + (n + 1 : K) * a * p.coeff (n + 1) := by
  rw [taylor_coeff]
  have hd : (hasseDeriv n p).natDegree ≤ 1 :=
    (natDegree_hasseDeriv_le p n).trans (by omega)
  rw [eq_X_add_C_of_natDegree_le_one hd]
  simp only [eval_add, eval_mul, eval_C, eval_X, hasseDeriv_coeff, zero_add,
    Nat.choose_self, Nat.cast_one, one_mul]
  rw [Nat.add_comm 1 n, Nat.choose_succ_self_right]
  push_cast
  ring

theorem coeff_mul_next (f g : K[X]) (m n : ℕ) (hf : f.natDegree ≤ m + 1)
    (hg : g.natDegree ≤ n + 1) :
    (f * g).coeff (m + n + 1) =
      f.coeff (m + 1) * g.coeff n + f.coeff m * g.coeff (n + 1) := by
  classical
  rw [coeff_mul]
  have he : (∑ ij ∈ antidiagonal (m + n + 1), f.coeff ij.1 * g.coeff ij.2) =
      ∑ ij ∈ ({(m + 1, n), (m, n + 1)} : Finset (ℕ × ℕ)),
        f.coeff ij.1 * g.coeff ij.2 := by
    symm
    apply Finset.sum_subset
    · intro ij hij
      simp only [Finset.mem_insert, Finset.mem_singleton] at hij
      rcases hij with rfl | rfl <;> simp [mem_antidiagonal] <;> omega
    · intro ij hij hnot
      have hsum := mem_antidiagonal.mp hij
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
      by_cases hi : m + 1 < ij.1
      · rw [coeff_eq_zero_of_natDegree_lt (hf.trans_lt hi), zero_mul]
      by_cases hj : n + 1 < ij.2
      · rw [coeff_eq_zero_of_natDegree_lt (hg.trans_lt hj), mul_zero]
      have hcases : (ij.1 = m + 1 ∧ ij.2 = n) ∨ (ij.1 = m ∧ ij.2 = n + 1) := by omega
      rcases hcases with h | h
      · exact (hnot.1 (Prod.ext h.1 h.2)).elim
      · exact (hnot.2 (Prod.ext h.1 h.2)).elim
  rw [he]
  simp

/-- Coefficient of the highest possible power. Here `A = q(n+1)` and `B = r(n)`. -/
theorem equation_top_coeff (A B f : K[X]) (m k : ℕ)
    (hA : A.natDegree ≤ m) (hB : B.natDegree ≤ m) (hf : f.natDegree ≤ k) :
    (A * f - B * taylor (-1) f).coeff (m + k) =
      (A.coeff m - B.coeff m) * f.coeff k := by
  rw [coeff_sub, coeff_mul_add_eq_of_natDegree_le hA hf,
    coeff_mul_add_eq_of_natDegree_le hB (by simpa using hf), coeff_taylor_top f (-1) k hf]
  ring

/-- Case 1: unequal highest coefficients give the exact degree. -/
theorem degree_case_one (A B f : K[X]) (m : ℕ)
    (hA : A.natDegree ≤ m) (hB : B.natDegree ≤ m) (hf : f ≠ 0)
    (hlead : A.coeff m ≠ B.coeff m) :
    (A * f - B * taylor (-1) f).natDegree = m + f.natDegree := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact natDegree_mul_le.trans (Nat.add_le_add_right hA _)
    · exact natDegree_mul_le.trans (by simpa using Nat.add_le_add_right hB f.natDegree)
  · rw [equation_top_coeff A B f m f.natDegree hA hB le_rfl, coeff_natDegree]
    exact mul_ne_zero (sub_ne_zero.mpr hlead) (leadingCoeff_ne_zero.mpr hf)

/-- Case 2: after the leading terms cancel, the next coefficient is linear
in the candidate degree. This includes the exceptional root `k₀`. -/
theorem equation_next_coeff (A B f : K[X]) (m k : ℕ)
    (hA : A.natDegree ≤ m + 1) (hB : B.natDegree ≤ m + 1)
    (hf : f.natDegree ≤ k + 1) (hlead : A.coeff (m + 1) = B.coeff (m + 1)) :
    (A * f - B * taylor (-1) f).coeff (m + k + 1) =
      (A.coeff m - B.coeff m + (k + 1 : K) * B.coeff (m + 1)) * f.coeff (k + 1) := by
  rw [coeff_sub, coeff_mul_next A f m k hA hf,
    coeff_mul_next B (taylor (-1) f) m k hB (by simpa using hf),
    coeff_taylor_top f (-1) (k + 1) hf, coeff_taylor_next f (-1) k hf, hlead]
  ring

/-- If the coefficient above is above the degree of the right-hand side,
the candidate degree must be the exceptional root. -/
theorem degree_case_two_exception (p A B f : K[X]) (m k : ℕ)
    (hA : A.natDegree ≤ m + 1) (hB : B.natDegree ≤ m + 1)
    (hf : f.natDegree = k + 1) (hf0 : f ≠ 0)
    (hlead : A.coeff (m + 1) = B.coeff (m + 1))
    (he : A * f - B * taylor (-1) f = p) (hdeg : p.natDegree < m + k + 1) :
    A.coeff m - B.coeff m + (k + 1 : K) * B.coeff (m + 1) = 0 := by
  have h := congrArg (fun P : K[X] => P.coeff (m + k + 1)) he
  rw [equation_next_coeff A B f m k hA hB hf.le hlead,
    coeff_eq_zero_of_natDegree_lt hdeg, ← hf, coeff_natDegree] at h
  exact (mul_eq_zero.mp h).resolve_right (leadingCoeff_ne_zero.mpr hf0)

/-- Equation (8''): the symmetric form of the Gosper equation. -/
theorem operator_symmetric [CharZero K] (q r f : K[X]) :
    operator q r f =
      C (2 : K)⁻¹ * ((taylor 1 q - r) * (f + taylor (-1) f) +
        (taylor 1 q + r) * (f - taylor (-1) f)) := by
  have htwo : (2 : K) ≠ 0 := by norm_num
  rw [operator_apply]
  have h : (taylor 1 q - r) * (f + taylor (-1) f) +
      (taylor 1 q + r) * (f - taylor (-1) f) =
      C (2 : K) * (taylor 1 q * f - r * taylor (-1) f) := by
    simp only [map_ofNat]
    ring
  rw [h, ← mul_assoc, ← map_mul, inv_mul_cancel₀ htwo, map_one, one_mul]

/-- The next coefficient, including the constant-certificate case `k = 0`. -/
theorem equation_next_coeff_nat (A B f : K[X]) (l k : ℕ)
    (hA : A.natDegree ≤ l + 1) (hB : B.natDegree ≤ l + 1)
    (hf : f.natDegree ≤ k) (hlead : A.coeff (l + 1) = B.coeff (l + 1)) :
    (A * f - B * taylor (-1) f).coeff (l + k) =
      (A.coeff l - B.coeff l + (k : K) * B.coeff (l + 1)) * f.coeff k := by
  cases k with
  | zero =>
    have hf0 : f.natDegree = 0 := by omega
    rw [eq_C_of_natDegree_eq_zero hf0]
    simp only [taylor_C, coeff_sub, coeff_mul_C, Nat.cast_zero, zero_mul, add_zero,
      coeff_C_zero]
    ring
  | succ k =>
    simpa [Nat.add_assoc] using equation_next_coeff A B f l k hA hB hf hlead

/-- The root `k₀` of the linear coefficient `L(k)` in Case 2. -/
def exceptionalDegree (A B : K[X]) (l : ℕ) : K :=
  (B.coeff (l - 1) - A.coeff (l - 1)) / B.coeff l

/-- The paper's Case 2 bound, retaining integer roots even when negative. -/
def caseTwoDegreeBound (p A B : K[X]) (l : ℕ) : ℤ := by
  classical
  exact if h : ∃ k : ℤ, (k : K) = exceptionalDegree A B l then
    max (Classical.choose h) ((p.natDegree : ℤ) - l + 1)
  else (p.natDegree : ℤ) - l + 1

/-- The displayed maximum when `k₀` is an integer (including negative integers). -/
theorem caseTwoDegreeBound_of_integer [CharZero K] (p A B : K[X]) (l : ℕ) (k₀ : ℤ)
    (hk : (k₀ : K) = exceptionalDegree A B l) :
    caseTwoDegreeBound p A B l = max k₀ ((p.natDegree : ℤ) - l + 1) := by
  classical
  unfold caseTwoDegreeBound
  split_ifs with h
  · have he : Classical.choose h = k₀ :=
      Int.cast_injective ((Classical.choose_spec h).trans hk.symm)
    rw [he]
  · exact (h ⟨k₀, hk⟩).elim

/-- The ordinary bound when `k₀` is not an integer. -/
theorem caseTwoDegreeBound_of_not_integer (p A B : K[X]) (l : ℕ)
    (hk : ¬∃ k : ℤ, (k : K) = exceptionalDegree A B l) :
    caseTwoDegreeBound p A B l = (p.natDegree : ℤ) - l + 1 := by
  classical
  simp [caseTwoDegreeBound, hk]

theorem ordinary_le_caseTwoDegreeBound (p A B : K[X]) (l : ℕ) :
    (p.natDegree : ℤ) - l + 1 ≤ caseTwoDegreeBound p A B l := by
  classical
  unfold caseTwoDegreeBound
  split_ifs
  · exact le_max_right _ _
  · exact le_rfl

theorem integer_le_caseTwoDegreeBound [CharZero K] (p A B : K[X]) (l : ℕ) (k : ℤ)
    (hk : (k : K) = exceptionalDegree A B l) : k ≤ caseTwoDegreeBound p A B l := by
  classical
  unfold caseTwoDegreeBound
  split_ifs with h
  · have he : k = Classical.choose h := Int.cast_injective (hk.trans (Classical.choose_spec h).symm)
    rw [he]
    exact le_max_left _ _
  · exact (h ⟨k, hk⟩).elim

/-- Gosper's signed degree bound. Its paper-style theorem statements are
`paper_degree_bound_case_one`, `paper_degree_bound_case_two_integer`, and
`paper_degree_bound_case_two_noninteger` below. For nonzero `p`,
`p.natDegree` is its ordinary degree. -/
def paperDegreeBound (p A B : K[X]) : ℤ := by
  classical
  let l := max A.natDegree B.natDegree
  exact if A.coeff l ≠ B.coeff l then (p.natDegree : ℤ) - l
    else if l = 0 then (p.natDegree : ℤ) + 1
    else caseTwoDegreeBound p A B l

/-- The natural degree bound for indexing the coefficient matrix. The main
criterion separately checks that the signed bound is nonnegative. -/
def degreeBound (p A B : K[X]) : ℕ := (paperDegreeBound p A B).toNat

/-- The paper's Case 1 formula. -/
theorem paperDegreeBound_case_one (p A B : K[X])
    (h : A.coeff (max A.natDegree B.natDegree) ≠ B.coeff (max A.natDegree B.natDegree)) :
    paperDegreeBound p A B = (p.natDegree : ℤ) - max A.natDegree B.natDegree := by
  classical
  simp [paperDegreeBound, h]

/-- The paper's Case 2 formula, including equal constant coefficients. -/
theorem paperDegreeBound_case_two [CharZero K] (p A B : K[X])
    (h : A.coeff (max A.natDegree B.natDegree) = B.coeff (max A.natDegree B.natDegree)) :
    paperDegreeBound p A B = caseTwoDegreeBound p A B (max A.natDegree B.natDegree) := by
  classical
  unfold paperDegreeBound
  dsimp only
  rw [ite_eq_right (not_ne_iff.mpr h)]
  by_cases hl : max A.natDegree B.natDegree = 0
  · rw [ite_eq_left hl, hl]
    have h0 : A.coeff 0 = B.coeff 0 := by simpa [hl] using h
    rw [caseTwoDegreeBound_of_integer p A B 0 0 (by simp [exceptionalDegree, h0])]
    simp only [Nat.cast_zero, sub_zero]
    omega
  · rw [ite_eq_right hl]

/-- The leading-coefficient split agrees with Case 1 as printed in the paper. -/
theorem paper_case_one_degrees (A B : K[X]) (l : ℕ)
    (hA : A.natDegree ≤ l) (hB : B.natDegree ≤ l)
    (h : A.coeff l ≠ B.coeff l) :
    (A - B).natDegree = l ∧ (A + B).degree ≤ (A - B).degree := by
  have htop : (A - B).coeff l ≠ 0 := by simpa using sub_ne_zero.mpr h
  have hd : (A - B).natDegree = l :=
    natDegree_eq_of_le_of_coeff_ne_zero ((natDegree_sub_le _ _).trans (max_le hA hB)) htop
  refine ⟨hd, ?_⟩
  have hne : A - B ≠ 0 := by intro hz; simp [hz] at htop
  rw [degree_eq_natDegree hne, hd]
  exact natDegree_le_iff_degree_le.mp ((natDegree_add_le _ _).trans (max_le hA hB))

/-- The leading-coefficient split agrees with Case 2 as printed in the paper. -/
theorem paper_case_two_degrees [CharZero K] (A B : K[X]) (l : ℕ)
    (hA : A.natDegree ≤ l) (hB : B.natDegree ≤ l)
    (h : A.coeff l = B.coeff l) (hb : B.coeff l ≠ 0) :
    (A + B).natDegree = l ∧ (A - B).degree < (A + B).degree := by
  have htop : (A + B).coeff l ≠ 0 := by
    rw [coeff_add, h, ← two_mul]
    exact mul_ne_zero (by norm_num) hb
  have hd : (A + B).natDegree = l :=
    natDegree_eq_of_le_of_coeff_ne_zero ((natDegree_add_le _ _).trans (max_le hA hB)) htop
  refine ⟨hd, ?_⟩
  have hne : A + B ≠ 0 := by intro hz; simp [hz] at htop
  rw [degree_eq_natDegree hne, hd, degree_lt_iff_coeff_zero]
  intro i hi
  rcases hi.eq_or_lt with he | hi
  · subst i
    simp [h]
  · rw [coeff_sub, coeff_eq_zero_of_natDegree_lt (hA.trans_lt hi),
      coeff_eq_zero_of_natDegree_lt (hB.trans_lt hi), sub_self]

/-- Case 1 gives the exact degree, not merely an upper bound. -/
theorem degree_case_one_exact (p A B f : K[X]) (l : ℕ)
    (hA : A.natDegree ≤ l) (hB : B.natDegree ≤ l) (hf : f ≠ 0)
    (hlead : A.coeff l ≠ B.coeff l) (he : A * f - B * taylor (-1) f = p) :
    (f.natDegree : ℤ) = (p.natDegree : ℤ) - l := by
  have hd := degree_case_one A B f l hA hB hf hlead
  rw [he] at hd
  omega

/-- Case 2: the degree is ordinary or is the exceptional integer root. -/
theorem degree_case_two_le_or_exception [CharZero K] (p A B f : K[X]) (l : ℕ)
    (hA : A.natDegree ≤ l + 1) (hB : B.natDegree ≤ l + 1)
    (hlead : A.coeff (l + 1) = B.coeff (l + 1)) (hb : B.coeff (l + 1) ≠ 0)
    (hf : f ≠ 0) (he : A * f - B * taylor (-1) f = p) :
    (f.natDegree : ℤ) ≤ (p.natDegree : ℤ) - (l + 1) + 1 ∨
      (f.natDegree : K) = exceptionalDegree A B (l + 1) := by
  by_cases hd : f.natDegree + l ≤ p.natDegree
  · exact Or.inl (by omega)
  right
  have hc := equation_next_coeff_nat A B f l f.natDegree hA hB le_rfl hlead
  rw [he, coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < l + f.natDegree),
    coeff_natDegree] at hc
  have hz : A.coeff l - B.coeff l + (f.natDegree : K) * B.coeff (l + 1) = 0 :=
    (mul_eq_zero.mp hc.symm).resolve_right (leadingCoeff_ne_zero.mpr hf)
  unfold exceptionalDegree
  rw [Nat.add_sub_cancel_right, eq_div_iff hb]
  linear_combination hz

/-- Every nonzero solution satisfies the paper's signed degree bound. -/
theorem solution_intDegree_le [CharZero K] (p A B f : K[X])
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hf0 : f ≠ 0)
    (he : A * f - B * taylor (-1) f = p) :
    (f.natDegree : ℤ) ≤ paperDegreeBound p A B := by
  classical
  let l := max A.natDegree B.natDegree
  have hA : A.natDegree ≤ l := le_max_left _ _
  have hB : B.natDegree ≤ l := le_max_right _ _
  unfold paperDegreeBound
  change (f.natDegree : ℤ) ≤ if A.coeff l ≠ B.coeff l then (p.natDegree : ℤ) - l
    else if l = 0 then (p.natDegree : ℤ) + 1 else caseTwoDegreeBound p A B l
  split_ifs with hlead hl
  · have hd := degree_case_one A B f l hA hB hf0 hlead
    rw [he] at hd
    omega
  · have hlead : A.coeff l = B.coeff l := not_ne_iff.mp hlead
    have hb : B.coeff l ≠ 0 := by
      rcases max_choice A.natDegree B.natDegree with hm | hm
      · rw [← hlead, show l = A.natDegree from hm, coeff_natDegree]
        exact leadingCoeff_ne_zero.mpr hA0
      · rw [show l = B.natDegree from hm, coeff_natDegree]
        exact leadingCoeff_ne_zero.mpr hB0
    by_contra hlarge
    have hpos : 0 < f.natDegree := by omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
    change f.natDegree = k + 1 at hk
    have ha0 : A.natDegree = 0 := by omega
    have hb0 : B.natDegree = 0 := by omega
    have h := congrArg (fun P : K[X] => P.coeff k) he
    rw [eq_C_of_natDegree_eq_zero ha0, eq_C_of_natDegree_eq_zero hb0] at h
    simp only [coeff_sub, coeff_C_mul] at h
    rw [coeff_taylor_next f (-1) k (by omega),
      coeff_eq_zero_of_natDegree_lt (p := p) (by omega : p.natDegree < k)] at h
    have hz : (k + 1 : K) * B.coeff 0 * f.leadingCoeff = 0 := by
      rw [hl] at hlead
      rw [hlead, ← hk, coeff_natDegree] at h
      linear_combination h
    have hk0 : (k + 1 : K) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
    exact (mul_ne_zero (mul_ne_zero hk0 (by simpa [hl] using hb))
      (leadingCoeff_ne_zero.mpr hf0) hz).elim
  · have hlead : A.coeff l = B.coeff l := not_ne_iff.mp hlead
    have hb : B.coeff l ≠ 0 := by
      rcases max_choice A.natDegree B.natDegree with hm | hm
      · rw [← hlead, show l = A.natDegree from hm, coeff_natDegree]
        exact leadingCoeff_ne_zero.mpr hA0
      · rw [show l = B.natDegree from hm, coeff_natDegree]
        exact leadingCoeff_ne_zero.mpr hB0
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hl
    change l = m + 1 at hm
    obtain hd | hk := degree_case_two_le_or_exception p A B f m
      (by simpa [hm] using hA) (by simpa [hm] using hB)
      (by simpa [hm] using hlead) (by simpa [hm] using hb) hf0 he
    · exact hd.trans (by simpa [hm] using ordinary_le_caseTwoDegreeBound p A B l)
    · exact integer_le_caseTwoDegreeBound p A B l f.natDegree (by simpa [hm] using hk)

private theorem paper_degree_cases [CharZero K] (A B : K[X])
    (hA : A ≠ 0) (hB : B ≠ 0) :
    let l := max A.natDegree B.natDegree
    (A.coeff l ≠ B.coeff l ∧ (A - B).natDegree = l ∧
      (A + B).degree ≤ (A - B).degree) ∨
    (A.coeff l = B.coeff l ∧ (A + B).natDegree = l ∧
      (A - B).degree < (A + B).degree) := by
  dsimp only
  by_cases h : A.coeff (max A.natDegree B.natDegree) =
      B.coeff (max A.natDegree B.natDegree)
  · have hb : B.coeff (max A.natDegree B.natDegree) ≠ 0 := by
      rcases max_choice A.natDegree B.natDegree with hm | hm
      · rw [← h, hm, coeff_natDegree]
        exact leadingCoeff_ne_zero.mpr hA
      · rw [hm, coeff_natDegree]
        exact leadingCoeff_ne_zero.mpr hB
    exact Or.inr ⟨h, paper_case_two_degrees A B _ (le_max_left _ _) (le_max_right _ _) h hb⟩
  · exact Or.inl ⟨h, paper_case_one_degrees A B _ (le_max_left _ _) (le_max_right _ _) h⟩

private theorem paperDegreeBound_case_two_of_degrees [CharZero K] (p A B : K[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (l : ℕ)
    (hcase : (A - B).degree < (A + B).degree) (hl : (A + B).degree = l) :
    paperDegreeBound p A B = caseTwoDegreeBound p A B l := by
  rcases paper_degree_cases A B hA hB with ⟨_, _, hle⟩ | ⟨heq, hd, _⟩
  · exact (not_lt_of_ge hle hcase).elim
  · rw [paperDegreeBound_case_two p A B heq, ← hd, natDegree_eq_of_degree_eq_some hl]

/-- Case 1: if `deg(A+B) ≤ deg(A-B) = l`, then `deg(f) = deg(p) - l`.
Here `A(n) = q(n+1)` and `B(n) = r(n)`. -/
theorem paper_degree_bound_case_one [CharZero K] (p A B f : K[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hf : f ≠ 0) (l : ℕ)
    (hcase : (A + B).degree ≤ (A - B).degree) (hl : (A - B).degree = l)
    (h_equation : A * f - B * taylor (-1) f = p) :
    (f.natDegree : ℤ) = (p.natDegree : ℤ) - l := by
  rcases paper_degree_cases A B hA hB with ⟨hne, hd, _⟩ | ⟨_, _, hlt⟩
  · have hm : max A.natDegree B.natDegree = l :=
      hd.symm.trans (natDegree_eq_of_degree_eq_some hl)
    exact degree_case_one_exact p A B f l
      (hm ▸ le_max_left _ _) (hm ▸ le_max_right _ _) hf (hm ▸ hne) h_equation
  · exact (not_lt_of_ge hcase hlt).elim

/-- Case 2: if `deg(A-B) < deg(A+B) = l` and `k₀` is an integer,
then `deg(f) ≤ max {k₀, deg(p) - l + 1}`.
Here `A(n) = q(n+1)` and `B(n) = r(n)`. -/
theorem paper_degree_bound_case_two_integer [CharZero K] (p A B f : K[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hf : f ≠ 0) (l : ℕ)
    (hcase : (A - B).degree < (A + B).degree) (hl : (A + B).degree = l)
    (k₀ : ℤ) (hroot : (k₀ : K) = (B.coeff (l - 1) - A.coeff (l - 1)) / B.coeff l)
    (h_equation : A * f - B * taylor (-1) f = p) :
    (f.natDegree : ℤ) ≤ max k₀ ((p.natDegree : ℤ) - l + 1) := by
  have h := solution_intDegree_le p A B f hA hB hf h_equation
  rw [paperDegreeBound_case_two_of_degrees p A B hA hB l hcase hl,
    caseTwoDegreeBound_of_integer p A B l k₀ hroot] at h
  exact h

/-- Case 2: if `deg(A-B) < deg(A+B) = l` and the exceptional root is not
an integer, then `deg(f) ≤ deg(p) - l + 1`. -/
theorem paper_degree_bound_case_two_noninteger [CharZero K] (p A B f : K[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hf : f ≠ 0) (l : ℕ)
    (hcase : (A - B).degree < (A + B).degree) (hl : (A + B).degree = l)
    (hroot : ¬∃ k₀ : ℤ, (k₀ : K) =
      (B.coeff (l - 1) - A.coeff (l - 1)) / B.coeff l)
    (h_equation : A * f - B * taylor (-1) f = p) :
    (f.natDegree : ℤ) ≤ (p.natDegree : ℤ) - l + 1 := by
  have h := solution_intDegree_le p A B f hA hB hf h_equation
  rw [paperDegreeBound_case_two_of_degrees p A B hA hB l hcase hl,
    caseTwoDegreeBound_of_not_integer p A B l hroot] at h
  exact h

/-- Every polynomial solution fits in the natural search space. Zero solutions
are allowed here; the signed rejection theorem requires a nonzero right side. -/
theorem solution_degree_le [CharZero K] (p A B f : K[X])
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (he : A * f - B * taylor (-1) f = p) :
    f.natDegree ≤ degreeBound p A B := by
  by_cases hf0 : f = 0
  · simp [hf0]
  have h := solution_intDegree_le p A B f hA0 hB0 hf0 he
  unfold degreeBound
  omega

/-- A nonzero right-hand side forces the paper's bound to be nonnegative. -/
theorem paperDegreeBound_nonneg_of_solution [CharZero K] (p A B f : K[X])
    (hp : p ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (he : A * f - B * taylor (-1) f = p) : 0 ≤ paperDegreeBound p A B := by
  have hf : f ≠ 0 := by
    intro h
    simp [h] at he
    exact hp he.symm
  have hd := solution_intDegree_le p A B f hA hB hf he
  omega

/-- The paper's rejection rule: if `k < 0`, no polynomial certificate exists. -/
theorem no_polynomial_solution_of_degreeBound_neg [CharZero K] (p A B : K[X])
    (hp : p ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) (hk : paperDegreeBound p A B < 0) :
    ¬∃ f : K[X], A * f - B * taylor (-1) f = p := by
  rintro ⟨f, hf⟩
  exact (not_le_of_gt hk) (paperDegreeBound_nonneg_of_solution p A B f hp hA hB hf)

end Gosper
