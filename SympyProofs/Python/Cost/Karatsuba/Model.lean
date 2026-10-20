module

public import SympyProofs.Python.Cost.Karatsuba.Work
public import SympyProofs.Python.Cost.Models
public import SympyProofs.Python.Cost.Bounds

/-!
# A selectable Karatsuba multiplication policy

Only multiplication changes: the charge uses the smaller of the schoolbook
rectangle and a dyadically padded Karatsuba envelope. Division, exponentiation,
allocation, scans, and control retain their existing reference charges. In
particular small-operand products cannot become more expensive through padding.
Realization by an integer implementation is separate from bounds on this policy.
-/

@[expose] public section
namespace Python.Cost.Models

def karatsuba : Model
  | .integer e =>
      if e.op = .mul then
        1 + min (width (e.args[0]?.getD 0) * width (e.args[1]?.getD 0))
          (Karatsuba.work (max (width (e.args[0]?.getD 0)) (width (e.args[1]?.getD 0)))) +
          width e.result
      else schoolbook (.integer e)
  | e => schoolbook e

theorem karatsuba_le_schoolbook (e : Event) : karatsuba e ≤ schoolbook e := by
  cases e with
  | integer e =>
    simp only [karatsuba]
    split_ifs with h
    · simp only [schoolbook, integerSchoolbook, h]
      have := min_le_left (width (e.args[0]?.getD 0) * width (e.args[1]?.getD 0))
        (Karatsuba.work (max (width (e.args[0]?.getD 0)) (width (e.args[1]?.getD 0))))
      omega
    · rfl
  | buffer => rfl
  | sequence => rfl
  | control => rfl

@[simp] theorem karatsuba_integer_of_ne_mul (e : IntegerEvent) (h : e.op ≠ .mul) :
    karatsuba (.integer e) = schoolbook (.integer e) := by simp [karatsuba, h]

end Python.Cost.Models
