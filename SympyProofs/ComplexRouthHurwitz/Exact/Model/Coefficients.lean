import SympyProofs.ComplexRouthHurwitz.Exact.Model.Basic
import SympyProofs.ComplexRouthHurwitz.FractionFree.Descending

/-! The ring-valued coefficient operations commute with complex denotation. -/
namespace RouthHurwitz.ComplexRouth.Exact.Gaussian.Model
open Polynomial
open scoped ComplexConjugate
noncomputable section
open Classical
local notation "f" => GaussianInt.toComplex

/-- Coordinatewise denotation; never called by the Gaussian runner. -/
def mapRow {N : ℕ} (a : Rows.Row N) : Coefficients.Row N := Vector.ofFn (fun j => f a[j])
def mapPair {N : ℕ} (r : Rows.Pair N) : Coefficients.Pair N := ⟨mapRow r.upper, mapRow r.lower⟩

@[simp] theorem mapRow_get {N} (a : Rows.Row N) (j : ℕ) (hj : j < N) :
    (mapRow a)[j] = f a[j] := by simp [mapRow]
@[simp] theorem map_entry {N} (a : Rows.Row N) (j : ℕ) :
    Coefficients.entry (mapRow a) j = f (Rows.entry a j) := by
  simp [Coefficients.entry, Rows.entry]; split_ifs <;> simp
@[simp] theorem map_zero (N) : mapRow (Rows.zero N) = Coefficients.zero N := by
  ext j hj; simp [mapRow, Rows.zero, Coefficients.zero]
@[simp] theorem map_one (N) : mapRow (Rows.one N) = Coefficients.one N := by
  ext j hj; simp [mapRow, Rows.one, Coefficients.one]
@[simp] theorem map_add {N} (a b : Rows.Row N) :
    mapRow (Rows.add a b) = Coefficients.add (mapRow a) (mapRow b) := by
  ext j hj; simp [mapRow, Rows.add, Coefficients.add]
@[simp] theorem map_derivative {N} (a : Rows.Row N) :
    mapRow (Rows.derivative a) = Coefficients.derivative (mapRow a) := by
  ext j hj; simp [mapRow, Rows.derivative, Coefficients.derivative, ← map_entry]
@[simp] theorem map_eval {N} (a : Rows.Row N) (z : GaussianInt) :
    f (Rows.eval a z) = Coefficients.eval (mapRow a) (f z) := by
  simp [Rows.eval, Coefficients.eval, mapRow]

@[simp] theorem map_real (z : GaussianInt) : f (z.re : GaussianInt) = ((f z).re : ℂ) := by
  simp only [_root_.map_intCast, ← GaussianInt.intCast_re, Complex.ofReal_intCast]
@[simp] theorem map_imag (z : GaussianInt) :
    f ((z.im : GaussianInt)*(⟨0,1⟩ : GaussianInt)) = (f z).im*Complex.I := by
  rw [_root_.map_mul, _root_.map_intCast, show f (⟨0,1⟩ : GaussianInt) = Complex.I by simp [GaussianInt.toComplex_def]]
  simp only [← GaussianInt.intCast_im, Complex.ofReal_intCast]

@[simp] theorem map_scan {N} (a : Rows.Row N) (n : ℕ) :
    mapPair (Rows.scan a n) = Coefficients.scan (mapRow a) n := by
  unfold mapPair Rows.scan Coefficients.scan
  congr 1
  all_goals
    apply Vector.ext; intro j hj
    simp only [mapRow, Vector.getElem_ofFn, Fin.getElem_fin]
    split_ifs <;> first | exact map_real _ | exact map_imag _

@[simp] theorem mapRow_eq_zero {N} (a : Rows.Row N) :
    mapRow a = Coefficients.zero N ↔ a = Rows.zero N := by
  constructor
  · intro h; apply Vector.ext; intro j hj
    apply GaussianInt.toComplex_injective
    have he := congrArg (fun v : Vector ℂ N => v[j]) h
    simpa [mapRow, Coefficients.zero, Rows.zero] using he
  · rintro rfl; exact map_zero N

@[simp] theorem map_I : f (⟨0,1⟩ : GaussianInt) = Complex.I := by
  simp [GaussianInt.toComplex_def]

@[simp] theorem map_repairOffset {N} (d : ℕ) (u v : Rows.Row N) :
    Coefficients.repairOffset d (mapRow u) (mapRow v) = Rows.repairOffset d u v := by
  have he (j : ℕ) :
      Coefficients.eval (mapRow u) ((j:ℂ)*Complex.I) *
        Coefficients.eval (Coefficients.derivative (mapRow v)) ((j:ℂ)*Complex.I) -
      Coefficients.eval (Coefficients.derivative (mapRow u)) ((j:ℂ)*Complex.I) *
        Coefficients.eval (mapRow v) ((j:ℂ)*Complex.I) =
      f (Rows.eval u ((j:GaussianInt)*⟨0,1⟩)*Rows.eval (Rows.derivative v) ((j:GaussianInt)*⟨0,1⟩)-
        Rows.eval (Rows.derivative u) ((j:GaussianInt)*⟨0,1⟩)*Rows.eval v ((j:GaussianInt)*⟨0,1⟩)) := by
    simp only [_root_.map_sub, _root_.map_mul, map_eval, map_derivative, _root_.map_natCast, map_I]
  simp only [Rows.repairOffset, Coefficients.repairOffset, he, ne_eq, GaussianInt.toComplex_eq_zero]

@[simp] theorem map_reciprocal {N} (a : Rows.Row N) (m : ℕ) (t : ℤ) :
    mapRow (Rows.reciprocal a m t) = Coefficients.reciprocal (mapRow a) m t := by
  apply Vector.ext; intro i hi
  simp only [mapRow, Rows.reciprocal, Coefficients.reciprocal, Vector.getElem_ofFn, Fin.getElem_fin]
  split_ifs <;> simp only [_root_.map_zero, _root_.map_mul, _root_.map_sum,
    _root_.map_pow, _root_.map_intCast, _root_.map_natCast, map_I,
    GaussianInt.toComplex_star, map_eval, Coefficients.eval, mapRow,
    Fin.getElem_fin, Vector.getElem_ofFn, Complex.ofReal_intCast]

@[simp] theorem map_repair {N} (d : ℕ) (u v : Rows.Row N) :
    mapPair (Rows.repair d u v) = Coefficients.repair d (mapRow u) (mapRow v) := by
  simp only [Rows.repair, Coefficients.repair, mapRow_eq_zero, map_entry, ← zero_real_iff]
  split_ifs
  · simp [mapPair]
  · simp only [map_scan, map_reciprocal, map_add, map_repairOffset, Int.cast_natCast]
  · rfl

/-- The cell numerator before exact division by the previous squared pivot. -/
def cellNumerator {N} (d : ℕ) (u v : Rows.Row N) (j : Fin N) : GaussianInt :=
  let A := (Rows.entry u (d+1)).re
  let B := (Rows.entry v d).re
  ((B:GaussianInt)^2*u[j] - ((B:GaussianInt)*Rows.entry u d -
      (A:GaussianInt)*Rows.entry v (d-1))*v[j] -
      (A:GaussianInt)*(B:GaussianInt)*(if j.val=0 then 0 else Rows.entry v (j.val-1)))

theorem field_cell {N} (d : ℕ) (D : ℤ) (u v : Rows.Row N) (j : Fin N) :
    f (cellNumerator d u v j) / (D:ℂ) =
      (FractionFree.nextLower d (D:ℝ) (mapRow u) (mapRow v))[j] := by
  simp only [cellNumerator, FractionFree.nextLower, Vector.getElem_ofFn, Fin.getElem_fin,
    _root_.map_mul, _root_.map_sub, _root_.map_pow, map_entry, map_real,
    mapRow_get, Complex.ofReal_intCast]
  have he : f (if j.val=0 then 0 else Rows.entry v (j.val-1)) =
      if j.val=0 then 0 else f (Rows.entry v (j.val-1)) := by split_ifs <;> simp
  rw [he]

/-- Divisibility follows from the mapped subresultant row, not from rounding. -/
theorem cell_divides {N} (d : ℕ) (D : ℤ) (u v : Rows.Row N) (hD : D ≠ 0)
    (hm : FractionFree.Arithmetic.MappedRow f
      (Coefficients.entry (FractionFree.nextLower d (D:ℝ) (mapRow u) (mapRow v)))) (j : Fin N) :
    (D:GaussianInt) ∣ cellNumerator d u v j := by
  obtain ⟨q,hq⟩ := hm j.val
  simp only [Coefficients.entry, dite_eq_left j.isLt] at hq
  have he := (field_cell d D u v j).trans hq
  have hd : (D:ℂ) ≠ 0 := Int.cast_ne_zero.mpr hD
  have he' := (div_eq_iff hd).mp he
  refine ⟨q, GaussianInt.toComplex_injective ?_⟩
  rw [_root_.map_mul, _root_.map_intCast, he', mul_comm]

@[simp] theorem map_nextLower {N} (d : ℕ) (D : ℤ) (u v : Rows.Row N) (hD : D ≠ 0)
    (hm : FractionFree.Arithmetic.MappedRow f
      (Coefficients.entry (FractionFree.nextLower d (D:ℝ) (mapRow u) (mapRow v)))) :
    mapRow (nextLower d D u v) = FractionFree.nextLower d (D:ℝ) (mapRow u) (mapRow v) := by
  apply Vector.ext; intro j hj
  simp only [mapRow_get, nextLower, Vector.getElem_ofFn, Fin.getElem_fin]
  change f (cellNumerator d u v ⟨j,hj⟩ / (D:GaussianInt)) = _
  rw [denote_exact_quotient _ _ (Int.cast_ne_zero.mpr hD) (cell_divides d D u v hD hm ⟨j,hj⟩),
    _root_.map_intCast]
  exact field_cell d D u v ⟨j,hj⟩

/-- Any Gaussian vector supplies a ring-valued seed for a fresh segment. -/
theorem mapped_descending {N} (a : Rows.Row N) (d : ℕ) :
    FractionFree.Arithmetic.MappedRow f (FractionFree.descending (Coefficients.entry (mapRow a)) d) := by
  intro j
  refine ⟨FractionFree.descending (Rows.entry a) d j, ?_⟩
  simp only [FractionFree.descending]
  split_ifs <;> simp

end
end RouthHurwitz.ComplexRouth.Exact.Gaussian.Model
