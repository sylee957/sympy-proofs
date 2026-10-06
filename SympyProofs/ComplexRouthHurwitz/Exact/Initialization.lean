import SympyProofs.ComplexRouthHurwitz.Exact.Coefficients

/-! Denotation and integral subresultant seeds for the first Gaussian elimination. -/
namespace RouthHurwitz.ComplexRouth.Exact.Gaussian
open Polynomial FractionFree FractionFree.Arithmetic
noncomputable section
open Classical
local notation "f" => GaussianInt.toComplex

@[simp] theorem map_phase (z : GaussianInt) : f (phase z) = FractionFree.phase (f z) := by
  have hr : (f z).re = (z.re:ℝ) := GaussianInt.intCast_re z |>.symm
  have hi : (f z).im = (z.im:ℝ) := GaussianInt.intCast_im z |>.symm
  have hr0 : (z.re:ℝ)=0 ↔ z.re=0 := by exact_mod_cast (Iff.rfl : z.re=0 ↔ z.re=0)
  have hrn : (z.re:ℝ)<0 ↔ z.re<0 := by exact_mod_cast (Iff.rfl : z.re<0 ↔ z.re<0)
  have hin : (z.im:ℝ)<0 ↔ z.im<0 := by exact_mod_cast (Iff.rfl : z.im<0 ↔ z.im<0)
  simp only [phase, FractionFree.phase, hr, hi, hr0, hrn, hin]
  split_ifs <;> simp [GaussianInt.toComplex_def]

@[simp] theorem map_initialRows {N} (a : Rows.Row N) (n : ℕ) :
    mapPair (initialRows a n) = FractionFree.initialRows (mapRow a) n := by
  have hs := map_scan a n
  have hu := congrArg Coefficients.Pair.upper hs
  have hv := congrArg Coefficients.Pair.lower hs
  simp only [mapPair] at hu hv
  have hz : (Coefficients.entry (mapRow a) n).im = ((Rows.entry a n).im:ℝ) := by
    rw [map_entry, GaussianInt.intCast_im]
  have hz0 : ((Rows.entry a n).im:ℝ)=0 ↔ (Rows.entry a n).im=0 := by
    exact_mod_cast (Iff.rfl : (Rows.entry a n).im=0 ↔ (Rows.entry a n).im=0)
  simp only [mapPair, initialRows, FractionFree.initialRows, hz, hz0, hu]
  congr 1
  by_cases hb : (Rows.entry a n).im=0
  · simpa only [hb, ite_true] using hv
  · simp only [hb, ite_false]
    apply Vector.ext; intro j hj
    have hvj := congrArg (fun x : Coefficients.Row N => x[j]) hv
    have huj := congrArg (fun x : Coefficients.Row N => x[j]) hu
    simp only [mapRow_get] at hvj huj
    simp only [mapRow_get, Vector.getElem_ofFn, Fin.getElem_fin, map_sub, map_mul,
      map_intCast]
    rw [← hvj, ← huj, map_entry]
    rw [← GaussianInt.intCast_re]
    simp only [Complex.ofReal_intCast, show f (⟨0,1⟩:GaussianInt) = Complex.I by simp [GaussianInt.toComplex_def]]

@[simp] theorem map_initialDivisor {N} (a : Rows.Row N) (n : ℕ) :
    (initialDivisor a n : ℝ) = FractionFree.initialDivisor (mapRow a) n := by
  simp only [initialDivisor, FractionFree.initialDivisor, map_entry,
    ← GaussianInt.intCast_im, ← GaussianInt.intCast_re, Int.cast_eq_zero]
  split_ifs <;> simp

/-- The first divisor is justified by integral minors of the unscaled split rows. -/
theorem initial_segment {N n} (a : Rows.Row N) (hn : 0<n) (hN : n<N)
    (ha : (Rows.entry a n).re ≠ 0) :
    let r := initialRows a n
    Segment f (descending (Coefficients.entry (mapRow r.upper)) n)
      (descending (Coefficients.entry (mapRow r.lower)) (n-1)) (initialDivisor a n:ℂ) := by
  dsimp only
  by_cases hb : (Rows.entry a n).im=0
  · simp only [initialDivisor, hb, ite_true, Int.cast_one]
    exact Segment.start (mapped_descending _ _) (mapped_descending _ _)
  let r := Rows.scan a n
  let A : GaussianInt := ((Rows.entry a n).re:GaussianInt)
  let B : GaussianInt := (Rows.entry a n).im*(⟨0,1⟩:GaussianInt)
  let U := descending (Rows.entry r.upper) n
  let V := descending (Rows.entry r.lower) n
  have hU : U 0=A := by simp [U,A,r,Rows.entry,Rows.scan,hN]
  have hV : V 0=B := by simp [V,B,r,Rows.entry,Rows.scan,hN]
  have hA : f A ≠ 0 := by
    simp only [A, map_intCast, Int.cast_ne_zero]
    exact ha
  have hs := Segment.start_initial f U V A B hA hU hV
  have hu : descending (Coefficients.entry (mapRow (initialRows a n).upper)) n =
      (fun j => f (U j)) := by
    funext j
    simp only [initialRows, descending, U, r, map_entry]
    split_ifs <;> simp
  have hv : descending (Coefficients.entry (mapRow (initialRows a n).lower)) (n-1) =
      (fun j => f (A*V (j+1)-B*U (j+1))) := by
    funext j
    by_cases hj : j≤n-1
    · have hjN : n-1-j<N := by omega
      dsimp only [initialRows]
      simp only [hb, ite_false]
      simp only [descending, hj, ite_true,
        show j+1≤n by omega, show n-(j+1)=n-1-j by omega, U,V,A,B,
        map_entry, Rows.entry, dite_eq_left hjN, Vector.getElem_ofFn, Fin.getElem_fin]
      rfl
    · have hj' : ¬j+1≤n := by omega
      simp [descending, hj, hj', U,V]
  rw [hu,hv]
  simpa only [initialDivisor,hb,ite_false,A,map_intCast] using hs

end
end RouthHurwitz.ComplexRouth.Exact.Gaussian
