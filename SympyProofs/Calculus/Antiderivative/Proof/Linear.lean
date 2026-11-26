module

public import SympyProofs.Calculus.Antiderivative.Program.Linear
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.GetD
import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.Algebra.Field.IsField
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Homogeneous row elimination and back-substitution over any extension of the constants. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Linear

variable {F k : Type} [Field F] [Field k] (f : F →+* k)

/-- The vector of the first `m` entries, with zero padding and coefficients extended by `f`. -/
def vector (m : ℕ) (r : List F) : Fin m → k := fun i => f (r.getD i 0)

/-- The linear functional on `m` unknowns given by one homogeneous row. -/
def functional (m : ℕ) (r : List F) : (Fin m → k) →ₗ[k] k :=
  ∑ i : Fin m, f (r.getD i 0) • LinearMap.proj i

@[simp] theorem functional_apply (m : ℕ) (r : List F) (v : Fin m → k) :
    functional f m r v = ∑ i : Fin m, f (r.getD i 0) * v i := by
  simp [functional]

theorem functional_snoc {m : ℕ} (r : List F) (v : Fin m → k) (a : k) :
    functional f (m + 1) r (Fin.snoc v a) = functional f m r v + f (r.getD m 0) * a := by
  simp [Fin.sum_univ_castSucc]

theorem vector_append {m : ℕ} (v : List F) (h : v.length = m) (a : F) :
    vector f (m + 1) (v ++ [a]) = Fin.snoc (vector f m v) (f a) := by
  ext i
  induction i using Fin.lastCases with
  | last => simp [vector, h]
  | cast i =>
    rw [Fin.snoc_castSucc]
    apply congrArg f
    exact List.getD_append _ _ _ _ (h ▸ i.isLt)

theorem functional_take (m : ℕ) (r : List F) : functional f m (r.take m) = functional f m r := by
  apply LinearMap.ext
  intro v
  simp [List.getD_eq_getElem?_getD]

theorem functional_eliminateAt (p r : List F) (m : ℕ) :
    functional f m (eliminateAt p m m r) =
      functional f m r - (f (r.getD m 0) / f (p.getD m 0)) • functional f m p := by
  apply LinearMap.ext
  intro v
  simp [eliminateAt, functional_apply, List.getD_eq_getElem?_getD,
    sub_mul, mul_assoc, Finset.sum_sub_distrib, Finset.mul_sum]

/-- A vector solves the projected system exactly when it extends by one coordinate
to a solution of the original system. -/
theorem eliminate_spec [DecidableEq F] (m : ℕ) (rows : List (List F)) (v : Fin m → k) :
    (∀ r ∈ eliminate m rows, functional f m r v = 0) ↔
      ∃ a : k, ∀ r ∈ rows, functional f (m + 1) r (Fin.snoc v a) = 0 := by
  rw [eliminate]
  split
  · rename_i h
    have hzero (r : List F) (hr : r ∈ rows) : r.getD m 0 = 0 := by
      simpa using List.find?_eq_none.mp h r hr
    simp only [List.forall_mem_map, functional_take, functional_snoc]
    constructor
    · intro hv
      exact ⟨0, fun r hr => by rw [hv r hr, mul_zero, add_zero]⟩
    · rintro ⟨a,ha⟩ r hr
      simpa only [hzero r hr, map_zero, zero_mul, add_zero] using ha r hr
  · rename_i p hp
    have hp0 : p.getD m 0 ≠ 0 := by simpa using List.find?_some hp
    have hp' : f (p.getD m 0) ≠ 0 := (map_ne_zero_iff _ f.injective).mpr hp0
    have hmem := List.mem_of_find?_eq_some hp
    simp only [List.forall_mem_map, functional_eliminateAt, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, functional_snoc]
    constructor
    · intro h
      use -functional f m p v / f (p.getD m 0)
      intro r hr
      have he := h r hr
      rw [sub_eq_zero.mp he]
      ring
    · rintro ⟨a,ha⟩ r hr
      have hs := ha r hr
      have ht := ha p hmem
      field_simp
      linear_combination f (p.getD m 0) * hs - f (r.getD m 0) * ht

/-- Every generated vector has the requested width. -/
theorem length_of_mem_kernel [DecidableEq F] (rows : List (List F)) (m : ℕ) (v : List F)
    (hv : v ∈ kernel rows m) : v.length = m := by
  induction m generalizing rows v with
  | zero => simp [kernel] at hv
  | succ m ih =>
    rw [kernel] at hv
    split at hv
    · rcases List.mem_cons.mp hv with rfl | hv
      · simp [unit]
      · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
        simp [ih _ _ ha]
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
      simp [ih _ _ ha]

/-- The computed dot product is the model linear functional on that vector. -/
theorem map_dot (r v : List F) : f (dot r v) = functional f v.length r (vector f v.length v) := by
  induction v generalizing r with
  | nil => simp [dot]
  | cons a v ih =>
    cases r with
    | nil => simp [dot]
    | cons b r =>
      have h := ih r
      simp only [functional_apply, vector] at h
      simp [dot, functional_apply, vector, Fin.sum_univ_succ, dot] at h ⊢
      exact h

/-- Adjoin one coordinate to each vector using a linear functional. -/
def extend {m : ℕ} (L : (Fin m → k) →ₗ[k] k) : (Fin m → k) →ₗ[k] (Fin (m + 1) → k) where
  toFun v := Fin.snoc v (L v)
  map_add' u v := by ext i; induction i using Fin.lastCases <;> simp
  map_smul' c v := by ext i; induction i using Fin.lastCases <;> simp

/-- Select the pivot value forced by the last equation. -/
def backSubst (m : ℕ) (p : List F) : (Fin m → k) →ₗ[k] k :=
  -(f (p.getD m 0))⁻¹ • functional f m p

theorem backSubst_apply (m : ℕ) (p : List F) (v : Fin m → k) :
    backSubst f m p v = -(functional f m p v) / f (p.getD m 0) := by
  simp [backSubst, div_eq_inv_mul]

private theorem extend_member {m : ℕ} (p v : List F) (hv : v.length = m) :
    vector f (m + 1) (v ++ [-dot p v / p.getD m 0]) =
      extend (backSubst f m p) (vector f m v) := by
  rw [vector_append f _ hv]
  change Fin.snoc _ _ = Fin.snoc _ _
  rw [map_div₀, map_neg, map_dot, hv, backSubst_apply]

private theorem vector_unit_last (m : ℕ) :
    vector f (m + 1) (unit (m + 1) m : List F) = Fin.snoc 0 1 := by
  ext i
  induction i using Fin.lastCases with
  | last => simp [vector, unit]
  | cast j =>
    simp [vector, unit, List.getElem?_range (j.isLt.trans (Nat.lt_succ_self m)), j.isLt.ne]

/-- The linear span of the computed kernel over a field extending its coefficients. -/
def generated [DecidableEq F] (rows : List (List F)) (m : ℕ) : Submodule k (Fin m → k) :=
  Submodule.span k (vector f m '' {r | r ∈ kernel rows m})

/-- Every output row is a vector of the generated subspace. -/
theorem vector_mem_generated [DecidableEq F] (rows : List (List F)) (m : ℕ) {v : List F}
    (h : v ∈ kernel rows m) : vector f m v ∈ generated f rows m :=
  Submodule.subset_span ⟨v, h, rfl⟩

private theorem map_mem_generated [DecidableEq F] {rows : List (List F)} {m : ℕ}
    {N : Type} [AddCommMonoid N] [Module k N] (L : (Fin m → k) →ₗ[k] N) {T : Submodule k N}
    (hL : ∀ a ∈ kernel rows m, L (vector f m a) ∈ T) {v : Fin m → k}
    (hv : v ∈ generated f rows m) : L v ∈ T := by
  have H : generated f rows m ≤ T.comap L := Submodule.span_le.mpr (by
    rintro _ ⟨a, ha, rfl⟩
    exact hL a ha)
  exact H hv

/-- The computed generators span every solution, including solutions over a larger field. -/
theorem mem_generated_of_solution [DecidableEq F] (rows : List (List F)) (m : ℕ) (v : Fin m → k)
    (hv : ∀ r ∈ rows, functional f m r v = 0) : v ∈ generated f rows m := by
  induction m generalizing rows with
  | zero =>
    have hz : v = 0 := Subsingleton.elim _ _
    rw [hz]
    exact Submodule.zero_mem _
  | succ m ih =>
    let w : Fin m → k := fun i => v i.castSucc
    have hsnoc : Fin.snoc w (v (Fin.last m)) = v := by
      ext i
      induction i using Fin.lastCases <;> simp [w]
    have hw := ih (eliminate m rows) w ((eliminate_spec f m rows w).mpr
      ⟨v (Fin.last m), fun r hr => by rw [hsnoc]; exact hv r hr⟩)
    cases hp : rows.find? (fun r => r.getD m 0 != 0) with
    | none =>
      simp only [eliminate, hp] at hw
      have h₁ : extend (0 : (Fin m → k) →ₗ[k] k) w ∈ generated f rows (m + 1) := by
        apply map_mem_generated f _ _ hw
        intro a ha
        have hm : a ++ [0] ∈ kernel rows (m + 1) := by
          simp only [kernel, hp]
          exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
        simpa [vector_append f _ (length_of_mem_kernel _ _ _ ha), extend] using
          vector_mem_generated f _ _ hm
      have h₂ : Fin.snoc (0 : Fin m → k) (1 : k) ∈ generated f rows (m + 1) := by
        rw [← vector_unit_last (F := F) f]
        apply vector_mem_generated
        simp only [kernel, hp, List.mem_cons_self]
      have he : v = extend (0 : (Fin m → k) →ₗ[k] k) w +
          v (Fin.last m) • Fin.snoc (0 : Fin m → k) (1 : k) := by
        ext i
        induction i using Fin.lastCases <;> simp [extend, w]
      rw [he]
      exact Submodule.add_mem _ h₁ (Submodule.smul_mem _ _ h₂)
    | some p =>
      simp only [eliminate, hp] at hw
      have hp0 : p.getD m 0 ≠ 0 := by simpa using List.find?_some hp
      have hpn : f (p.getD m 0) ≠ 0 := (map_ne_zero_iff _ f.injective).mpr hp0
      have eqn := hv p (List.mem_of_find?_eq_some hp)
      rw [← hsnoc, functional_snoc] at eqn
      have hx : backSubst f m p w = v (Fin.last m) := by
        rw [backSubst_apply, div_eq_iff hpn]
        linear_combination -eqn
      have he : extend (backSubst f m p) w = v := by
        change (Fin.snoc w (backSubst f m p w) : Fin (m+1) → k) = v
        rw [hx, hsnoc]
      rw [← he]
      apply map_mem_generated f _ _ hw
      intro a ha
      have hm : a ++ [-dot p a / p.getD m 0] ∈ kernel rows (m + 1) := by
        simp only [kernel, hp]
        exact List.mem_map.mpr ⟨a,ha,rfl⟩
      rw [← extend_member f _ _ (length_of_mem_kernel _ _ _ ha)]
      exact vector_mem_generated f _ _ hm

/-- Each generator satisfies all homogeneous rows. -/
theorem kernel_sound [DecidableEq F] (rows : List (List F)) (m : ℕ)
    {a : List F} (ha : a ∈ kernel rows m) {r : List F} (hr : r ∈ rows) :
    functional f m r (vector f m a) = 0 := by
  induction m generalizing rows a r with
  | zero => simp
  | succ m ih =>
    rw [kernel] at ha
    split at ha
    · rename_i hp
      have hz : r.getD m 0 = 0 := by simpa using List.find?_eq_none.mp hp r hr
      rcases List.mem_cons.mp ha with rfl | ha
      · rw [vector_unit_last, functional_snoc, hz, map_zero, map_zero, zero_mul, add_zero]
      · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ha
        have h := ih _ hg (List.mem_map_of_mem (f := List.take m) hr)
        rw [functional_take] at h
        rw [vector_append f _ (length_of_mem_kernel _ _ _ hg), functional_snoc, h,
          map_zero, mul_zero, zero_add]
    · rename_i p hp
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ha
      have h := ih _ hg (List.mem_map_of_mem (f := eliminateAt p m m) hr)
      rw [functional_eliminateAt, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        sub_eq_zero] at h
      rw [extend_member f _ _ (length_of_mem_kernel _ _ _ hg)]
      change functional f (m+1) r (Fin.snoc _ _) = _
      rw [functional_snoc, backSubst_apply, h]
      ring

/-- The span over any model field of the computed basis is exactly the solution space. -/
theorem generated_iff [DecidableEq F] (rows : List (List F)) (m : ℕ) (v : Fin m → k) :
    v ∈ generated f rows m ↔ ∀ r ∈ rows, functional f m r v = 0 := by
  refine ⟨fun h r hr => ?_, mem_generated_of_solution f rows m v⟩
  have hle : generated f rows m ≤ LinearMap.ker (functional f m r) :=
    Submodule.span_le.mpr (by rintro _ ⟨a,ha,rfl⟩; exact kernel_sound f _ _ ha hr)
  exact hle h

private theorem vector_div (m : ℕ) (a : List F) (d : F) :
    vector f m (a.map (· / d)) = (f d)⁻¹ • vector f m a := by
  ext i
  simp only [vector, Pi.smul_apply, smul_eq_mul, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases a[(i : ℕ)]? <;> simp [div_eq_inv_mul]

private theorem vector_first (m : ℕ) (a : List F) : vector f (m+1) a 0 = f (a.headD 0) := by
  cases a <;> rfl

/-- A normalized result has the requested length, first coefficient one and satisfies every row. -/
theorem normalized_sound [DecidableEq F] (rows : List (List F)) (m : ℕ) {v : List F}
    (hv : normalized rows m = some v) :
    v.length = m ∧ v.headD 0 = 1 ∧ ∀ r ∈ rows, functional f m r (vector f m v) = 0 := by
  cases hg : (kernel rows m).find? (fun g => g.headD 0 != 0) with
  | none => rw [normalized, hg] at hv; cases hv
  | some g =>
    have hn : g.headD 0 ≠ 0 := by simpa using List.find?_some hg
    have hm := List.mem_of_find?_eq_some hg
    rw [normalized, hg] at hv
    obtain rfl : g.map (· / g.headD 0) = v := Option.some.inj hv
    refine ⟨by simp [length_of_mem_kernel rows m g hm], ?_, ?_⟩
    · cases g <;> simp_all
    · intro r hr
      rw [vector_div, map_smul, kernel_sound f rows m hm hr, smul_zero]

/-- Failure to normalize means no solution with first coordinate one exists in any extension. -/
theorem normalized_none_iff [DecidableEq F] (rows : List (List F)) (m : ℕ) :
    normalized rows (m + 1) = none ↔
      ¬ ∃ v : Fin (m+1) → k, v 0 = 1 ∧ ∀ r ∈ rows, functional f (m+1) r v = 0 := by
  constructor
  · rintro h ⟨v,hv,hs⟩
    have hnone : (kernel rows (m+1)).find? (fun g => g.headD 0 != 0) = none := by
      cases he : (kernel rows (m+1)).find? (fun g => g.headD 0 != 0) <;>
        simp_all [normalized]
    have hz : generated f rows (m+1) ≤ LinearMap.ker (LinearMap.proj (R := k)
        (φ := fun _ : Fin (m+1) => k) 0) := Submodule.span_le.mpr (by
      rintro _ ⟨g,hg,rfl⟩
      have h₀ : g.headD 0 = 0 := by simpa using List.find?_eq_none.mp hnone g hg
      exact (vector_first f m g).trans (by rw [h₀, map_zero]))
    exact one_ne_zero (hv.symm.trans (hz ((generated_iff f rows (m+1) v).mpr hs)))
  · intro hn
    cases hr : normalized rows (m+1) with
    | none => rfl
    | some g =>
      have h := normalized_sound f rows (m+1) hr
      exact False.elim (hn ⟨vector f (m+1) g,
        (vector_first f m g).trans (by rw [h.2.1, map_one]), h.2.2⟩)

end SympyProofs.Calculus.Antiderivative.Linear
