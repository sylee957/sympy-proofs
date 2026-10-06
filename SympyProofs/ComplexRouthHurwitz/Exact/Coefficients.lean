import SympyProofs.ComplexRouthHurwitz.Exact.Basic
import SympyProofs.ComplexRouthHurwitz.Exact.Model.Coefficients

/-! Lossless row encoding and the exact integer elimination identity. -/
namespace RouthHurwitz.ComplexRouth.Exact.Gaussian
open Polynomial Model

@[simp] theorem encode_decode {N} (n : ℕ) (a : Row N) : encode n (decode n a) = a := by
  ext j hj
  simp [encode, decode, scalar]
  split_ifs <;> simp_all

@[simp] theorem decode_entry {N} (n : ℕ) (a : Row N) (j : ℕ) :
    Rows.entry (decode n a) j = scalar (n%2 == j%2) (entry a j) := by
  simp only [Rows.entry, entry]
  split_ifs <;> (simp [decode, scalar]; try rfl)

@[simp] theorem decode_pivot {N} (n : ℕ) (a : Row N) :
    (Rows.entry (decode n a) n).re = entry a n := by simp [scalar]

@[simp] theorem decode_zero (n N : ℕ) :
    decode n (Vector.replicate N 0) = Rows.zero N := by
  apply Vector.ext; intro j hj
  simp [decode, scalar, Rows.zero]
  rfl

@[simp] theorem decode_eq_zero {N} (n : ℕ) (a : Row N) :
    decode n a = Rows.zero N ↔ a = Vector.replicate N 0 := by
  constructor
  · intro h
    have := congrArg (encode n) h
    rw [encode_decode] at this
    exact this.trans (by apply Vector.ext; intro j hj; simp [encode, Rows.zero])
  · rintro rfl; exact decode_zero n N

/-- Coordinate encoding of a symmetric polynomial is lossless. -/
theorem decode_encode_symmetric {N} (n : ℕ) (a : Rows.Row N) (p : ℂ[X])
    (ha : mapRow a = Coefficients.pack N p) (hp : Symmetric p n) :
    decode n (encode n a) = a := by
  apply Vector.ext; intro j hj
  have hc := congrArg (fun q : ℂ[X] => q.coeff j) hp
  simp only [reflect_coeff, coeff_C_mul] at hc
  have he := congrArg (fun v : Vector ℂ N => v[j]) ha
  simp only [mapRow_get, Coefficients.pack, Vector.getElem_ofFn] at he
  rw [← he] at hc
  have hjpow : (-1 : ℂ)^j = (-1 : ℂ)^(j%2) := (neg_one_pow_eq_pow_mod_two j)
  have hnpow : (-1 : ℂ)^n = (-1 : ℂ)^(n%2) := (neg_one_pow_eq_pow_mod_two n)
  rw [hjpow, hnpow] at hc
  have hjmod := Nat.mod_lt j (by omega : 0 < 2)
  have hnmod := Nat.mod_lt n (by omega : 0 < 2)
  simp only [decode, encode, Vector.getElem_ofFn, Fin.getElem_fin, scalar]
  rcases (show n%2=0 ∨ n%2=1 by omega) with hn | hn <;>
    rcases (show j%2=0 ∨ j%2=1 by omega) with hj' | hj'
  all_goals
    simp only [hn, hj', pow_zero, pow_one, mul_one, one_mul, mul_neg_one,
      neg_one_mul] at hc
    have hre := congrArg Complex.re hc
    have him := congrArg Complex.im hc
    simp only [Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im,
      ← GaussianInt.intCast_re, ← GaussianInt.intCast_im] at hre him
    simp only [hn, hj', beq_self_eq_true, ↓reduceIte, Nat.reduceBEq,
      Bool.false_eq_true, Nat.zero_ne_one, Nat.one_ne_zero]
    apply Zsqrtd.ext <;> (dsimp; try rfl)
    all_goals norm_cast at hre him
    all_goals omega

/-- Selecting a real or imaginary component commutes with an exact real divisor. -/
theorem component_div (z : GaussianInt) (D : ℤ) (hD : D ≠ 0)
    (hz : (D : GaussianInt) ∣ z) (real : Bool) :
    (if real then z.re else z.im) / D =
      if real then (z / (D : GaussianInt)).re else (z / (D : GaussianInt)).im := by
  obtain ⟨q, rfl⟩ := hz
  have hd : (D : GaussianInt) ≠ 0 := Int.cast_ne_zero.mpr hD
  rw [mul_div_cancel_left₀ q hd]
  cases real <;> simp [hD]

theorem numerator_spec {N} (d : ℕ) (hd : 0 < d) (u v : Row N) (j : Fin N) :
    numerator d u v j =
      if (d-1)%2 = j.val%2 then
        (cellNumerator d (decode (d+1) u) (decode d v) j).re
      else (cellNumerator d (decode (d+1) u) (decode d v) j).im := by
  have hdpar : (d-1)%2 = (d+1)%2 := by omega
  have hdiff : (d+1)%2 ≠ d%2 := by omega
  simp only [cellNumerator, decode_entry]
  simp only [numerator, decode,
    Vector.getElem_ofFn, Fin.getElem_fin, scalar, hdpar]
  rcases (show d%2=0 ∨ d%2=1 by omega) with hm | hm <;>
    rcases (show j.val%2=0 ∨ j.val%2=1 by omega) with hjm | hjm
  all_goals
    have hdp : (d+1)%2 = 1-d%2 := by omega
    by_cases hj : j.val=0
    · simp [hm, hdp, hj, pow_two]; ring
    · have hjp : (j.val-1)%2 = 1-j.val%2 := by omega
      simp [hm, hjm, hdp, hj, hjp, pow_two]; ring

theorem nextLower_encode {N} (d : ℕ) (hd : 0 < d) (D : ℤ) (hD : D ≠ 0)
    (u v : Row N)
    (hex : ∀ j, (D : GaussianInt) ∣ cellNumerator d (decode (d+1) u) (decode d v) j) :
    nextLower d D u v = encode (d-1) (Model.nextLower d D (decode (d+1) u) (decode d v)) := by
  apply Vector.ext; intro j hj
  simp only [nextLower, encode, Model.nextLower, Vector.getElem_ofFn, Fin.getElem_fin]
  change numerator d u v ⟨j,hj⟩ / D =
    if (d-1)%2=j%2 then (cellNumerator d (decode (d+1) u) (decode d v) ⟨j,hj⟩ / (D:GaussianInt)).re
    else (cellNumerator d (decode (d+1) u) (decode d v) ⟨j,hj⟩ / (D:GaussianInt)).im
  rw [numerator_spec d hd]
  simpa only [decide_eq_true_eq] using component_div _ D hD (hex ⟨j,hj⟩) (decide ((d-1)%2=j%2))

theorem scan_spec {N} (a : Rows.Row N) (n : ℕ) (hn : 0 < n) :
    (scan a n).upper = encode n (Rows.scan a n).upper ∧
    (scan a n).lower = encode (n-1) (Rows.scan a n).lower := by
  constructor
  · apply Vector.ext; intro j hj
    simp [scan, Rows.scan, encode]
    split_ifs <;> simp_all
  · apply Vector.ext; intro j hj
    have hm : ((n-1)%2 = j%2) ↔ ¬ (n%2 = j%2) := by omega
    by_cases hp : n%2 = j%2 <;> simp [scan, Rows.scan, encode, hm, hp]

theorem initialRows_spec {N} (a : Rows.Row N) (n : ℕ) (hn : 0 < n) :
    (initialRows a n).upper = encode n (Model.initialRows a n).upper ∧
    (initialRows a n).lower = encode (n-1) (Model.initialRows a n).lower := by
  have hpar : (n-1)%2 ≠ n%2 := by omega
  constructor
  · apply Vector.ext; intro j hj
    simp [initialRows, scan, Model.initialRows, Rows.scan, encode]
    split_ifs <;> simp_all
  · apply Vector.ext; intro j hj
    by_cases hz : (Rows.entry a n).im = 0 <;>
      by_cases hjp : n%2 = j%2
    all_goals
      have hm : ((n-1)%2 = j%2) ↔ ¬ (n%2 = j%2) := by omega
      simp [initialRows, scan, Model.initialRows, Rows.scan, encode,
        hz, hjp, hm, sub_eq_add_neg]

theorem derivative_spec {N} (d : ℕ) (u : Row N) :
    derivative u = encode d (Rows.derivative (decode (d+1) u)) := by
  apply Vector.ext; intro j hj
  simp only [derivative, encode, Rows.derivative, Vector.getElem_ofFn,
    Fin.getElem_fin, decode_entry]
  by_cases h : d%2=j%2
  · have hs : (d+1)%2=(j+1)%2 := by omega
    simp [h,hs,scalar]
  · have hs : (d+1)%2≠(j+1)%2 := by omega
    simp [h,hs,scalar]

theorem repair_spec {N} (d : ℕ) (u v : Row N) :
    (repair d u v).upper = encode (d+1) (Rows.repair d (decode (d+1) u) (decode d v)).upper ∧
    (repair d u v).lower = encode d (Rows.repair d (decode (d+1) u) (decode d v)).lower := by
  unfold repair
  by_cases hz : v=Vector.replicate N 0
  · simp only [hz, ite_true, Rows.repair, decode_eq_zero, encode_decode]
    exact ⟨True.intro, derivative_spec d u⟩
  · by_cases hp : entry v d=0
    · simp only [hz, hp, ite_false, ite_true, Rows.repair, decode_eq_zero, decode_pivot]
      simpa only [Nat.add_sub_cancel] using
        scan_spec (Rows.reciprocal (Rows.add (decode (d+1) u) (decode d v)) (d+1)
          (Rows.repairOffset d (decode (d+1) u) (decode d v))) (d+1) (by omega)
    · simp only [hz,hp,ite_false,Rows.repair,decode_eq_zero,decode_pivot,encode_decode]
      constructor <;> trivial

end RouthHurwitz.ComplexRouth.Exact.Gaussian
