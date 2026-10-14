import SympyProofs.LambertW.RealLower
import Mathlib.Data.EReal.Basic

/-!
# Lambert W on the extended reals

`principal` extends the principal branch to `[-exp (-1), +∞]`, with value
`+∞` at `+∞`. `lower` extends the lower branch to `[-exp (-1), 0]`, with
value `-∞` at zero. The real endpoint limits justify these choices.

Outside these domains the values are only totalization conventions: finite
inputs inherit the real definitions (except for the lower branch at zero),
and invalid infinite inputs are assigned zero.
-/

namespace LambertW.EReal

/-- The Real.principal branch with its limiting value at positive infinity. -/
noncomputable def principal : EReal → EReal :=
  EReal.rec 0 (fun x => (Real.principal x : EReal)) ⊤

/-- The Real.lower branch with its limiting value at zero. -/
noncomputable def lower : EReal → EReal := by
  classical
  exact EReal.rec 0 (fun x => if x = 0 then ⊥ else (Real.lower x : EReal)) 0

@[simp] theorem principal_coe (x : ℝ) :
    principal (x : EReal) = (Real.principal x : EReal) := rfl

@[simp] theorem principal_top : principal ⊤ = ⊤ := rfl

@[simp] theorem principal_zero : principal 0 = 0 := by
  simpa using principal_coe 0

@[simp] theorem lower_zero : lower 0 = ⊥ := by
  change (if (0 : ℝ) = 0 then (⊥ : EReal) else (Real.lower 0 : EReal)) = ⊥
  simp

theorem lower_coe {x : ℝ} (hx : x ≠ 0) :
    lower (x : EReal) = (Real.lower x : EReal) := by
  simp [lower, hx]

@[simp] theorem principal_neg_exp_neg_one :
    principal ((-Real.exp (-1) : ℝ) : EReal) = (-1 : EReal) := by
  rw [principal_coe, Real.principal_neg_exp_neg_one]
  simp

@[simp] theorem lower_neg_exp_neg_one :
    lower ((-Real.exp (-1) : ℝ) : EReal) = (-1 : EReal) := by
  rw [lower_coe (neg_ne_zero.mpr (Real.exp_ne_zero _)), Real.lower_neg_exp_neg_one]
  simp

/-- The defining equation for valid finite Real.principal-branch inputs. -/
theorem principal_mul_exp {x : ℝ} (hx : -Real.exp (-1) ≤ x) :
    principal (x : EReal) * (Real.exp (Real.principal x) : EReal) = (x : EReal) := by
  rw [principal_coe, ← EReal.coe_mul, Real.principal_mul_exp hx]

/-- The defining equation for valid finite Real.lower-branch inputs, excluding zero. -/
theorem lower_mul_exp {x : ℝ} (hx : x ∈ Set.Ico (-Real.exp (-1)) 0) :
    lower (x : EReal) * (Real.exp (Real.lower x) : EReal) = (x : EReal) := by
  rw [lower_coe (ne_of_lt hx.2), ← EReal.coe_mul, Real.lower_mul_exp hx]

end LambertW.EReal
