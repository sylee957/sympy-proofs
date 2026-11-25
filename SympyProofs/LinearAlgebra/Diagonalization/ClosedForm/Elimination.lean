module

public import SympyProofs.LinearAlgebra.Diagonalization.ClosedForm.Meadow
public import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Fixed column elimination by total division -/

@[expose] public section
noncomputable section

namespace SympyProofs.Diagonalization.Meadow

open Matrix
variable {K : Type*} [Field K] {n : ℕ}

/-- The functional y ↦ ∑ᵢ (xᵢ)⁻¹ yᵢ. Its value on x counts the nonzero coordinates. -/
def dual (x : Fin n → K) : (Fin n → K) →ₗ[K] K :=
  dotProductBilin K K (fun i => (x i)⁻¹)

/-- Remove the component detected by the reciprocal coordinates of x. -/
def eliminate (x y : Fin n → K) : Fin n → K := y - (dual x y / dual x x) • x

/-- Process each column once, retaining zeros in their original positions. -/
def reduce : {m : ℕ} → (Fin m → Fin n → K) → Fin m → Fin n → K
  | 0, u => u
  | _ + 1, u => Fin.cons (u 0) (reduce (fun j => eliminate (u 0) (u j.succ)))

theorem reduce_mem {m : ℕ} (u : Fin m → Fin n → K) (S : Submodule K (Fin n → K)) :
    (∀ j, reduce u j ∈ S) ↔ ∀ j, u j ∈ S := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [reduce, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, ih]
    constructor
    · rintro ⟨h, ht⟩
      refine ⟨h, fun i => ?_⟩
      simpa [eliminate] using S.add_mem (ht i) (S.smul_mem (dual (u 0) (u i.succ) / dual (u 0) (u 0)) h)
    · rintro ⟨h, ht⟩
      exact ⟨h, fun i => S.sub_mem (ht i) (S.smul_mem _ h)⟩

theorem dual_self_ne [CharZero K] {x : Fin n → K} (hx : x ≠ 0) : dual x x ≠ 0 := by
  classical
  let s := Finset.univ.filter fun i => x i ≠ 0
  have hs : s.Nonempty := by
    by_contra h
    apply hx
    funext i
    by_contra hi
    exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  have h : dual x x = (s.card : K) := by
    change (∑ i, (x i)⁻¹ * x i) = _
    rw [show (s.card : K) = ∑ i ∈ s, (1 : K) by simp, Finset.sum_filter]
    exact Finset.sum_congr rfl fun i _ => by by_cases hi : x i = 0 <;> simp [hi]
  rw [h]
  exact_mod_cast hs.card_pos.ne'

private theorem dual_eliminate [CharZero K] (x y : Fin n → K) :
    dual x (eliminate x y) = 0 := by
  by_cases h : x = 0
  · simp [h, dual]
  · simp [eliminate, div_mul_cancel₀ _ (dual_self_ne h)]

/-- In a zero linear combination only the zero columns can have a nonzero coefficient. -/
theorem reduce_relation [CharZero K] {m : ℕ} (u : Fin m → Fin n → K) (c : Fin m → K)
    (hz : ∑ j, c j • reduce u j = 0) : ∀ j, reduce u j ≠ 0 → c j = 0 := by
  induction m with
  | zero => intro j; exact j.elim0
  | succ m ih =>
    let v := fun j : Fin m => eliminate (u 0) (u j.succ)
    have he : c 0 • u 0 + ∑ j, c j.succ • reduce v j = 0 := by
      simpa only [Fin.sum_univ_succ, reduce, Fin.cons_zero, Fin.cons_succ, v] using hz
    have hk := (reduce_mem v (dual (u 0)).ker).mpr (fun j => dual_eliminate _ _)
    have h0 : u 0 ≠ 0 → c 0 = 0 := by
      intro hu
      have h := congrArg (dual (u 0)) he
      simp only [map_add, map_sum, map_smul, smul_eq_mul, map_zero,
        show ∀ j, dual (u 0) (reduce v j) = 0 from hk, mul_zero, Finset.sum_const_zero,
        add_zero] at h
      exact (mul_eq_zero.mp h).resolve_right (dual_self_ne hu)
    have hc : c 0 • u 0 = 0 := by by_cases h : u 0 = 0 <;> simp [h, h0]
    rw [hc, zero_add] at he
    exact Fin.cases h0 (ih v (fun j => c j.succ) he)

/-- Sum over the ordered support of a finite family. -/
theorem sum_indices {V : Type*} [AddCommMonoid V] (s : Finset (Fin n)) (f : Fin n → V)
    (h : ∀ i, i ∉ s → f i = 0) : ∑ i, f i = ∑ j, f (s.orderEmbOfFin rfl j) := by
  calc
    _ = ∑ i ∈ s, f i := (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => h i hi)).symm
    _ = _ := by
      conv_lhs => rw [← s.map_orderEmbOfFin_univ rfl, Finset.sum_map]
      rfl

/-- The number of nonzero residual columns is the rank of the original matrix. -/
theorem support_card [DecidableEq K] [CharZero K] (M : Matrix (Fin n) (Fin n) K) :
    (Finset.univ.filter fun i => reduce M.col i ≠ 0).card = M.rank := by
  classical
  let u := reduce M.col
  let s := Finset.univ.filter fun i => u i ≠ 0
  let g := s.orderEmbOfFin rfl
  have hmem (i) : i ∈ s ↔ u i ≠ 0 := by simp [s]
  have hout (i) (hi : i ∉ s) : u i = 0 := by simpa [hmem] using hi
  have hind : LinearIndependent K (fun i => u (g i)) := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hz i
    let w := Function.extend g c (fun _ => 0)
    have hw (j) : w (g j) = c j := g.injective.extend_apply _ _ _
    have he : ∑ j, w j • u j = 0 := by
      rw [sum_indices s _ (fun j hj => by simp [hout j hj])]
      simpa only [← hw] using hz
    rw [← hw]
    exact reduce_relation M.col w he _ ((hmem _).mp (s.orderEmbOfFin_mem _ _))
  have hspan : Submodule.span K (Set.range (fun i => u (g i))) =
      Submodule.span K (Set.range M.col) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact (reduce_mem M.col (Submodule.span K (Set.range M.col))).mpr
        (fun j => Submodule.subset_span ⟨j, rfl⟩) (g i)
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      apply (reduce_mem M.col _).mp _ i
      intro j
      by_cases hj : j ∈ s
      · have hj' : j ∈ Set.range g := (s.range_orderEmbOfFin rfl).symm ▸ hj
        obtain ⟨k, hk⟩ := hj'
        exact Submodule.subset_span ⟨k, congrArg u hk⟩
      · change u j ∈ _
        rw [hout _ hj]
        exact Submodule.zero_mem _
  rw [Matrix.rank_eq_finrank_span_cols, ← hspan]
  simpa only [Fintype.card_fin] using (finrank_span_eq_card hind).symm

end SympyProofs.Diagonalization.Meadow
