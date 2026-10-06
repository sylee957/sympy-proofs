import SympyProofs.ComplexRouthHurwitz.FractionFree.Determinants

/-! Integral minors for the degree-zero first elimination of the G-sequence. -/
namespace RouthHurwitz.ComplexRouth.FractionFree.Arithmetic
open Matrix Finset
variable {K : Type*} [Field K]

private def initialFactor (a : K) (r : ℕ) : K :=
  if r = 0 then 1 else if lower r then a else a⁻¹

private theorem initialFactor_prod (a : K) (ha : a ≠ 0) (k : ℕ) :
    ∏ r ∈ Finset.range (2*k+1), initialFactor a r = 1 := by
  induction k with
  | zero => simp [initialFactor]
  | succ k ih =>
    rw [show 2*(k+1)+1 = (2*k+1)+1+1 by omega, prod_range_succ, prod_range_succ, ih]
    have h : lower (2*k+2) ↔ ¬ lower (2*k+1) := by unfold lower; omega
    simp only [initialFactor, show 2*k+1 ≠ 0 by omega, show 2*k+1+1 ≠ 0 by omega,
      ite_false, h, one_mul]
    split_ifs <;> simp_all

/-- Although the upper seed contains `1/a`, its subresultant minors are integral:
paired row scalings cancel that denominator against the first-elimination factors. -/
theorem mapped_initial_minor {R : Type*} [CommRing R] (f : R →+* K)
    (U V : ℕ → R) (a b : R) (ha : f a ≠ 0) (hU : U 0 = a) (hV : V 0 = b)
    (k j : ℕ) :
    ∃ z : R, (minor (fun j => f (U j) / f a)
      (fun j => f (a*V (j+1)-b*U (j+1))) k j).det = f z := by
  let u := fun j => f (U j) / f a
  let v := fun j => f (a*V (j+1)-b*U (j+1))
  let M := minor u v k j
  let S := Finset.univ.filter (fun r : Fin (2*k+1) => r.val ≠ 0 ∧ lower r.val)
  let src : Fin (2*k+1) → Fin (2*k+1) := fun r =>
    if hr : r ∈ S then ⟨if r.val%4=0 then r.val-1 else r.val+1, by
      have hh := (mem_filter.mp hr).2
      dsimp [lower] at hh
      split_ifs <;> omega⟩ else r
  have hs (r) (hr : r ∈ S) : src r ∉ S := by
    have hh := (mem_filter.mp hr).2
    intro hm
    have hx := (mem_filter.mp hm).2.2
    simp only [src, hr, dite_true, Fin.val_mk] at hx
    dsimp [lower] at *
    split_ifs at hx <;> omega
  let T : Matrix (Fin (2*k+1)) (Fin (2*k+1)) R := fun r c =>
    let l := if c.val=2*k then c.val+j else c.val
    if r.val=0 then a*V (l+1)-b*U (l+1)
    else if lower r.val then
      if shift r.val-1 ≤ l then V (l-(shift r.val-1)) else 0
    else if shift r.val ≤ l then U (l-shift r.val) else 0
  have he : (fun r c => if r ∈ S then M r c + (f a*f b)*M (src r) c else M r c) =
      (fun r c => initialFactor (f a) r.val * f (T r c)) := by
    ext r c
    let l := if c.val=2*k then c.val+j else c.val
    by_cases h0 : r.val = 0
    · have hr : r = 0 := Fin.ext h0
      subst r
      simp [M, minor, entry, shift, lower, S, T, initialFactor, v]
    · by_cases hl : lower r.val
      · have hr : r ∈ S := mem_filter.mpr ⟨mem_univ _, h0, hl⟩
        have hsrc : ¬ lower (src r).val := by
          have hh := hs r hr
          have hshift : shift r.val > 0 := by dsimp [shift, lower] at *; omega
          simp only [src, hr, dite_true, Fin.val_mk]
          dsimp [lower] at *; split_ifs <;> omega
        have hshift : shift (src r).val = shift r.val-1 := by
          simp only [src, hr, dite_true, Fin.val_mk]
          dsimp [shift, lower] at *; split_ifs <;> omega
        have hp : 0 < shift r.val := by dsimp [shift, lower] at *; omega
        change (if r ∈ S then M r c + (f a*f b)*M (src r) c else M r c) = _
        simp only [hr, ite_true, M, minor, entry, hl, hsrc, ite_false, hshift,
          initialFactor, h0, T]
        change (if shift r.val ≤ l then v (l-shift r.val) else 0) +
          (f a*f b)*(if shift r.val-1 ≤ l then u (l-(shift r.val-1)) else 0) =
          f a*f (if shift r.val-1 ≤ l then V (l-(shift r.val-1)) else 0)
        by_cases hc : shift r.val ≤ l
        · have hc' : shift r.val-1 ≤ l := by omega
          simp only [hc, hc', ite_true, u, v, map_sub, map_mul,
            show l-(shift r.val-1)=l-shift r.val+1 by omega]
          field_simp; ring
        · by_cases hc' : shift r.val-1 ≤ l
          · have hh : l = shift r.val-1 := by omega
            simp [hh, show ¬ shift r.val ≤ shift r.val-1 by omega, u, v, hU, hV, ha]
          · simp [hc, hc', map_zero]
      · have hr : r ∉ S := by simp [S, hl]
        simp only [hr, ite_false, M, minor, entry, hl, initialFactor, h0, T]
        split_ifs <;> simp [u, div_eq_mul_inv, mul_comm]
  have hd := det_shear M S src (fun _ => f a*f b) hs
  rw [he] at hd
  rw [show (fun r c => initialFactor (f a) r.val * f (T r c)) =
    Matrix.of (fun r c => initialFactor (f a) r.val * (T.map f) r c) from rfl, det_mul_column] at hd
  have hf : (∏ r : Fin (2*k+1), initialFactor (f a) r.val) = 1 := by
    rw [Fin.prod_univ_eq_prod_range]
    exact initialFactor_prod _ ha k
  rw [hf, one_mul] at hd
  refine ⟨T.det, ?_⟩
  exact hd.symm.trans (f.map_det T).symm

end RouthHurwitz.ComplexRouth.FractionFree.Arithmetic
