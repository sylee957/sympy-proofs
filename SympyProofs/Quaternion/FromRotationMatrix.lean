module

public import SympyProofs.Quaternion.FromRotationMatrix.LeadingSign
public import SympyProofs.Quaternion.FromRotationMatrix.Sign
public import SympyProofs.Quaternion.FromRotationMatrix.ScaledSign
public import SympyProofs.Quaternion.FromRotationMatrix.Shepperd
public import SympyProofs.Quaternion.FromRotationMatrix.ScaledCayley

/-!
# Formulas for a quaternion from a rotation matrix

Each formula reads the same ten entries of the symmetric matrix `4 q qᵀ`, which are linear
in the entries of the matrix, and is proved against the specifications `RepresentsRotation`
and `RepresentsScaledRotation`.

| Name | Definition | File | Input |
|---|---|---|---|
| Sign | `fromRotationMatrix` | `Sign.lean` | rotation |
| Scaled sign | `fromScaledRotationMatrix` | `ScaledSign.lean` | scaled rotation |
| Shepperd | `fromRotationMatrixShepperd` | `Shepperd.lean` | rotation |
| Scaled Cayley | `fromScaledRotationMatrixCayley` | `ScaledCayley.lean` | scaled rotation |

* **Sign.** SymPy's `Quaternion.from_rotation_matrix` with `sign` replaced by `leadingSign`
  of `LeadingSign.lean`: absolute values from the diagonal of `4 q qᵀ`, signs from the first
  nonzero product with an earlier component.
* **Scaled sign.** The same with SymPy's scaling factor `det(M) ^ (1/3)`.
* **Shepperd.** The row of `4 q qᵀ` with the largest diagonal entry, divided by twice the
  square root of that entry.
* **Scaled Cayley.** Absolute values from the lengths of the rows of `4 q qᵀ`, with the
  scaling factor, and the signs of the scaled sign formula.

The sign, scaled sign and scaled Cayley formulas return the sign-normalized quaternion, the
one whose first nonzero component is positive. Shepperd's returns that quaternion or its
negative. So on scaled rotations the scaled sign and scaled Cayley formulas agree, and on
rotations all four agree, Shepperd's up to sign.
-/
