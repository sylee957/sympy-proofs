module

public import SympyProofs.Gosper.Basic

/-! # Product sums: equation (11) and the common form of the applications -/

@[expose] public section
noncomputable section

namespace Gosper

variable {K : Type*} [Field K]

/-- Product from `j = 1` to `n`, with the empty product equal to one. -/
def productRatio (u v : ℕ → K) (n : ℕ) : K :=
  ∏ j ∈ Finset.range n, u (j + 1) / v (j + 1)

@[simp] theorem productRatio_zero (u v : ℕ → K) : productRatio u v 0 = 1 := by
  simp [productRatio]

theorem productRatio_succ (u v : ℕ → K) (n : ℕ) :
    productRatio u v (n + 1) = productRatio u v n * (u (n + 1) / v (n + 1)) := by
  simp only [productRatio, Finset.prod_range_succ]

theorem productRatio_eq_div (u v : ℕ → K) (n : ℕ) :
    productRatio u v n = (∏ j ∈ Finset.range n, u (j + 1)) /
      (∏ j ∈ Finset.range n, v (j + 1)) := by
  simp [productRatio, Finset.prod_div_distrib]

/-- Equation (11), valid for an arbitrary function. Equations (3a) and (3b)
are its quadratic and cubic specializations. -/
theorem sum_product_offset (u : ℕ → K) (c : K) (hc : c ≠ 0) (m : ℕ)
    (hv : ∀ j ∈ Finset.range m, u (j + 1) + c ≠ 0) :
    ∑ n ∈ Finset.range m,
      productRatio u (fun j => u j + c) n / (u (n + 1) + c) =
      (1 - productRatio u (fun j => u j + c) m) / c := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih (fun j hj => hv j (Finset.mem_range.mpr
      (Nat.lt_succ_of_lt (Finset.mem_range.mp hj)))), productRatio_succ]
    have hm := hv m (Finset.mem_range.mpr (Nat.lt_succ_self m))
    field_simp
    ring

/-- A recurrence certificate for the products in equations (3c), (12), (15),
and (16). Only denominators in the requested finite interval must be nonzero. -/
theorem sum_product_certificate (u v F : ℕ → K) (D : K) (hD : D ≠ 0) (m : ℕ)
    (hv : ∀ j ≤ m, v (j + 1) ≠ 0)
    (hF : ∀ n < m, u (n + 1) * F (n + 1) - v (n + 2) * F n = D) :
    ∑ n ∈ Finset.range m, productRatio u v n / (v (n + 1) * v (n + 2)) =
      (F m * productRatio u v m / v (m + 1) - F 0 / v 1) / D := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih (fun j hj => hv j (by omega))
      (fun n hn => hF n (by omega)), productRatio_succ]
    have hm := hv m (by omega)
    have hm1 := hv (m + 1) (by omega)
    have he := hF m (by omega)
    field_simp
    linear_combination -(productRatio u v m) * he

end Gosper
