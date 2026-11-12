module

public import SympyProofs.LinearAlgebra.Permanent.Basic

/-! The product formula for permanents retains terms with repeated columns. -/

@[expose] public section

namespace Matrix

/-- Expand a product of rectangular matrices by choosing a column of `A` for each
column of `A * B`. The choices need not be injective. -/
theorem permanent_mul_eq_sum {m n R : Type*} [CommSemiring R]
    [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix n m R) (B : Matrix m n R) :
    (A * B).permanent =
      ∑ f : n → m, (A.submatrix id f).permanent * ∏ j, B (f j) j := by
  classical
  simp only [permanent, mul_apply, Fintype.prod_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  simp only [Finset.prod_mul_distrib, submatrix_apply, id_eq, Finset.sum_mul]

/-- The failure of multiplicativity consists exactly of the repeated-column terms. -/
theorem permanent_mul_eq_mul_add_sum {n R : Type*} [CommSemiring R]
    [Fintype n] [DecidableEq n] (A B : Matrix n n R) :
    (A * B).permanent = A.permanent * B.permanent +
      ∑ f ∈ Finset.univ.filter (fun f : n → n => ¬Function.Injective f),
        (A.submatrix id f).permanent * ∏ j, B (f j) j := by
  classical
  have hinj : (∑ f ∈ Finset.univ.filter (Function.Injective : (n → n) → Prop),
      (A.submatrix id f).permanent * ∏ j, B (f j) j) = A.permanent * B.permanent := by
    change _ = A.permanent * (∑ σ : Equiv.Perm n, ∏ j, B (σ j) j)
    rw [Finset.mul_sum]
    symm
    apply Finset.sum_bij (fun (σ : Equiv.Perm n) _ => (σ : n → n))
    · intro σ _
      simp [σ.injective]
    · intro σ _ τ _ h
      exact Equiv.ext (congrFun h)
    · intro f hf
      have hi : Function.Injective f := (Finset.mem_filter.mp hf).2
      exact ⟨Equiv.ofBijective f ⟨hi, Finite.injective_iff_surjective.mp hi⟩,
        Finset.mem_univ _, rfl⟩
    · intro σ _
      rw [permanent_permute_rows]
  rw [permanent_mul_eq_sum, ← hinj]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

end Matrix
