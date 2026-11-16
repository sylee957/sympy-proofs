module

public import SympyProofs.Quaternion.FromRotationMatrix.ScaledSign

/-!
# Cayley's method for a quaternion from a scaled rotation matrix

`fromScaledRotationMatrixCayley` takes the absolute value of each component from a whole
row of the symmetric matrix `4 q qᵀ`, where `fromScaledRotationMatrix` uses one diagonal
entry.

* The diagonal of `4 q qᵀ` uses the scaling factor `det(M) ^ (1/3)`, as in
  `fromScaledRotationMatrix`.
* Row `i` of `4 q qᵀ` is `4 qᵢ` times the quaternion, whose norm is the square root of the
  scaling factor. Each absolute value is therefore the length of a row divided by four
  times that square root.

The absolute values carry no signs. Here the signs are taken as in
`fromScaledRotationMatrix`, by `leadingSign` of `FromRotationMatrix/LeadingSign.lean`.

The division is by zero only for the zero matrix, where every row vanishes and the value is
`0` as it should be.

* `RepresentsScaledRotation.fromScaledRotationMatrixCayley_eq`: on every represented
  matrix the value is that of `fromScaledRotationMatrix`.
* `RepresentsScaledRotation.eq_fromScaledRotationMatrixCayley`: a sign-normalized
  quaternion representing `M` is `fromScaledRotationMatrixCayley M`.
* `fromScaledRotationMatrixCayley_represents`: if any quaternion represents `M`, the value
  does.
* `fromScaledRotationMatrixCayley_eq_fromRotationMatrix`: on `SO(3)`, where the scaling
  factor is `1`, it is `fromRotationMatrix`.

The two formulas differ away from scaled rotations and in how rounding errors affect them,
which is why this form is preferred in numerical work.
-/

@[expose] public section

namespace SympyQuaternion

open Matrix Quaternion

/-! ## The formula -/

/-- Cayley's method: each absolute value is the length of a row of `4 q qᵀ` divided by four
times the norm of the quaternion. The signs are those of `fromScaledRotationMatrix`. -/
noncomputable def fromScaledRotationMatrixCayley (M : Matrix (Fin 3) (Fin 3) ℝ) : ℍ[ℝ] :=
  let scale := M.det ^ ((1 : ℝ) / 3)
  -- The diagonal of `4 q qᵀ`: `4a²`, `4b²`, `4c²`, `4d²`.
  let aa := scale + M 0 0 + M 1 1 + M 2 2
  let bb := scale + M 0 0 - M 1 1 - M 2 2
  let cc := scale - M 0 0 + M 1 1 - M 2 2
  let dd := scale - M 0 0 - M 1 1 + M 2 2
  -- The off-diagonal entries: `4ab`, `4ac`, `4ad`, `4bc`, `4bd`, `4cd`.
  let ab := M 2 1 - M 1 2
  let ac := M 0 2 - M 2 0
  let ad := M 1 0 - M 0 1
  let bc := M 0 1 + M 1 0
  let bd := M 0 2 + M 2 0
  let cd := M 1 2 + M 2 1
  -- The absolute values of the four components: the length of each row, divided by four
  -- times the norm of the quaternion.
  let absA := √(aa ^ 2 + ab ^ 2 + ac ^ 2 + ad ^ 2) / (4 * √scale)
  let absB := √(ab ^ 2 + bb ^ 2 + bc ^ 2 + bd ^ 2) / (4 * √scale)
  let absC := √(ac ^ 2 + bc ^ 2 + cc ^ 2 + cd ^ 2) / (4 * √scale)
  let absD := √(ad ^ 2 + bd ^ 2 + cd ^ 2 + dd ^ 2) / (4 * √scale)
  -- The sign of each component relative to the first nonzero earlier one.
  let signB := leadingSign [ab]
  let signC := leadingSign [ac, bc]
  let signD := leadingSign [ad, bd, cd]
  ⟨absA, absB * signB, absC * signC, absD * signD⟩

/-! ## Agreement with `fromScaledRotationMatrix` -/

private theorem sqrt_div_four_mul_sqrt_eq {s t n : ℝ} (hn : 0 ≤ n) (h : s = 4 * t * n)
    (h0 : n = 0 → t = 0) : √s / (4 * √n) = √t / 2 := by
  rcases hn.eq_or_lt with rfl | hpos
  · simp [h0 rfl]
  · have h4 : √(4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.sqrt_mul_self (by norm_num)]
    have hs : √n ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    rw [h, Real.sqrt_mul' _ hpos.le, Real.sqrt_mul (by norm_num), h4]
    field_simp
    ring

/-- On every represented matrix, Cayley's method returns the value of
`fromScaledRotationMatrix`. -/
theorem RepresentsScaledRotation.fromScaledRotationMatrixCayley_eq {q : ℍ[ℝ]}
    {M : Matrix (Fin 3) (Fin 3) ℝ} (h : RepresentsScaledRotation q M) :
    fromScaledRotationMatrixCayley M = fromScaledRotationMatrix M := by
  obtain rfl := representsScaledRotation_iff.1 h
  have hk : (toScaledRotationMatrix q).det ^ ((1 : ℝ) / 3) = normSq q := by
    rw [det_toScaledRotationMatrix, one_div]
    exact Real.pow_rpow_inv_natCast normSq_nonneg (by norm_num)
  have hN := normSq_def' (a := q)
  -- The ten entries of `4 q qᵀ` in terms of the components of `q`.
  have haa : normSq q + toScaledRotationMatrix q 0 0 + toScaledRotationMatrix q 1 1 +
      toScaledRotationMatrix q 2 2 = 4 * (q.re * q.re) := by
    rw [hN]; simp [toScaledRotationMatrix]; ring
  have hbb : normSq q + toScaledRotationMatrix q 0 0 - toScaledRotationMatrix q 1 1 -
      toScaledRotationMatrix q 2 2 = 4 * (q.imI * q.imI) := by
    rw [hN]; simp [toScaledRotationMatrix]; ring
  have hcc : normSq q - toScaledRotationMatrix q 0 0 + toScaledRotationMatrix q 1 1 -
      toScaledRotationMatrix q 2 2 = 4 * (q.imJ * q.imJ) := by
    rw [hN]; simp [toScaledRotationMatrix]; ring
  have hdd : normSq q - toScaledRotationMatrix q 0 0 - toScaledRotationMatrix q 1 1 +
      toScaledRotationMatrix q 2 2 = 4 * (q.imK * q.imK) := by
    rw [hN]; simp [toScaledRotationMatrix]; ring
  have hab : toScaledRotationMatrix q 2 1 - toScaledRotationMatrix q 1 2 =
      4 * (q.re * q.imI) := by simp [toScaledRotationMatrix]; ring
  have hac : toScaledRotationMatrix q 0 2 - toScaledRotationMatrix q 2 0 =
      4 * (q.re * q.imJ) := by simp [toScaledRotationMatrix]; ring
  have had : toScaledRotationMatrix q 1 0 - toScaledRotationMatrix q 0 1 =
      4 * (q.re * q.imK) := by simp [toScaledRotationMatrix]; ring
  have hbc : toScaledRotationMatrix q 0 1 + toScaledRotationMatrix q 1 0 =
      4 * (q.imI * q.imJ) := by simp [toScaledRotationMatrix]; ring
  have hbd : toScaledRotationMatrix q 0 2 + toScaledRotationMatrix q 2 0 =
      4 * (q.imI * q.imK) := by simp [toScaledRotationMatrix]; ring
  have hcd : toScaledRotationMatrix q 1 2 + toScaledRotationMatrix q 2 1 =
      4 * (q.imJ * q.imK) := by simp [toScaledRotationMatrix]; ring
  -- Each row has squared length four times its diagonal entry times the squared norm,
  -- and it vanishes when the quaternion does.
  have ra := sqrt_div_four_mul_sqrt_eq (n := normSq q)
    (s := (4 * (q.re * q.re)) ^ 2 + (4 * (q.re * q.imI)) ^ 2 + (4 * (q.re * q.imJ)) ^ 2 +
      (4 * (q.re * q.imK)) ^ 2) (t := 4 * (q.re * q.re)) normSq_nonneg
    (by rw [hN]; ring) (fun h0 => by rw [normSq_eq_zero.1 h0]; simp)
  have rb := sqrt_div_four_mul_sqrt_eq (n := normSq q)
    (s := (4 * (q.re * q.imI)) ^ 2 + (4 * (q.imI * q.imI)) ^ 2 + (4 * (q.imI * q.imJ)) ^ 2 +
      (4 * (q.imI * q.imK)) ^ 2) (t := 4 * (q.imI * q.imI)) normSq_nonneg
    (by rw [hN]; ring) (fun h0 => by rw [normSq_eq_zero.1 h0]; simp)
  have rc := sqrt_div_four_mul_sqrt_eq (n := normSq q)
    (s := (4 * (q.re * q.imJ)) ^ 2 + (4 * (q.imI * q.imJ)) ^ 2 + (4 * (q.imJ * q.imJ)) ^ 2 +
      (4 * (q.imJ * q.imK)) ^ 2) (t := 4 * (q.imJ * q.imJ)) normSq_nonneg
    (by rw [hN]; ring) (fun h0 => by rw [normSq_eq_zero.1 h0]; simp)
  have rd := sqrt_div_four_mul_sqrt_eq (n := normSq q)
    (s := (4 * (q.re * q.imK)) ^ 2 + (4 * (q.imI * q.imK)) ^ 2 + (4 * (q.imJ * q.imK)) ^ 2 +
      (4 * (q.imK * q.imK)) ^ 2) (t := 4 * (q.imK * q.imK)) normSq_nonneg
    (by rw [hN]; ring) (fun h0 => by rw [normSq_eq_zero.1 h0]; simp)
  simp only [fromScaledRotationMatrixCayley, fromScaledRotationMatrix, hk, haa, hbb, hcc, hdd,
    hab, hac, had, hbc, hbd, hcd, ra, rb, rc, rd]

/-! ## The formula meets the specification -/

/-- A sign-normalized quaternion representing `M` is `fromScaledRotationMatrixCayley M`. -/
theorem RepresentsScaledRotation.eq_fromScaledRotationMatrixCayley {q : ℍ[ℝ]}
    {M : Matrix (Fin 3) (Fin 3) ℝ} (h : RepresentsScaledRotation q M)
    (n : IsSignNormalized q) : q = fromScaledRotationMatrixCayley M := by
  rw [h.fromScaledRotationMatrixCayley_eq]
  exact h.eq_fromScaledRotationMatrix n

/-- If any quaternion represents `M`, then `fromScaledRotationMatrixCayley M` does. -/
theorem fromScaledRotationMatrixCayley_represents {q : ℍ[ℝ]} {M : Matrix (Fin 3) (Fin 3) ℝ}
    (h : RepresentsScaledRotation q M) :
    RepresentsScaledRotation (fromScaledRotationMatrixCayley M) M := by
  rw [h.fromScaledRotationMatrixCayley_eq]
  exact fromScaledRotationMatrix_represents h

/-- If any quaternion represents `M ≠ 0`, then `fromScaledRotationMatrixCayley M` is
sign-normalized. -/
theorem fromScaledRotationMatrixCayley_isSignNormalized {q : ℍ[ℝ]}
    {M : Matrix (Fin 3) (Fin 3) ℝ} (h : RepresentsScaledRotation q M) (hM : M ≠ 0) :
    IsSignNormalized (fromScaledRotationMatrixCayley M) := by
  rw [h.fromScaledRotationMatrixCayley_eq]
  exact fromScaledRotationMatrix_isSignNormalized h hM

/-! ## Rotations -/

/-- On `SO(3)` the value is that of `fromRotationMatrix`. -/
theorem fromScaledRotationMatrixCayley_eq_fromRotationMatrix
    {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M ∈ specialOrthogonalGroup (Fin 3) ℝ) :
    fromScaledRotationMatrixCayley M = fromRotationMatrix M := by
  obtain ⟨q, hq⟩ := exists_representsRotation_iff.2 hM
  rw [hq.representsScaledRotation.fromScaledRotationMatrixCayley_eq,
    fromScaledRotationMatrix_eq_fromRotationMatrix hM]

end SympyQuaternion
