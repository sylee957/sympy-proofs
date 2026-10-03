import SympyProofs.RouthHurwitz.Exact.Loop
import SympyProofs.RouthHurwitz.Imperative.Rows

/-! Proof-only descriptions of the inline loop locals, shared by the algebraic
and root-count invariants. The executable runner does not call these definitions. -/
namespace RouthHurwitz.FractionFree.Proofs
open Polynomial Imperative Imperative.Bounds
variable {K : Type*} [Field K] [LinearOrder K]

-- Field notation for the shared coefficient-domain loop; no second transition.
abbrev Locals (n : ℕ) := Exact.Proofs.Locals K n

abbrev initialLocals (p : Polynomial K) : Locals (K := K) p.natDegree :=
  Exact.Proofs.start p.natDegree p.coeff

abbrev step (n k : ℕ) (s : Locals (K := K) n) : Locals (K := K) n :=
  Exact.Proofs.step n k s

/-- Initial locals expressed using polynomial rows for the field invariants. -/
theorem initialLocals_eq (p : Polynomial K) :
    initialLocals p = Id.run (do
      let upper := initial p 0
      let (lower, valid) : Vector K (width p.natDegree) × Bool :=
        repair p.natDegree ⟨width p.natDegree, Nat.lt_succ_self _⟩ upper (initial p 1)
      return (upper, lower, [upper, lower],
        if upper[0]'(width_pos _) * lower[0]'(width_pos _) < 0 then 1 else 0, !valid, (1 : K), (1 : K))) := by
  rfl

end RouthHurwitz.FractionFree.Proofs
