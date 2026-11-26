module

public import SympyProofs.Calculus.Antiderivative.Proof.AnalyticField
public import SympyProofs.Calculus.Antiderivative.Proof.StepModel

/-! Specializing a fraction from the lower tower is independent of the newest coordinate. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Model

open MvPolynomial

variable {k : Type} [Field k] {n : ℕ}
variable {p : Fin (n+1) → k} {c : k}

/-- Evaluate the last polynomial variable at the specified point. -/
private noncomputable def dropLast (p : Fin (n+1) → k) :
    MvPolynomial (Fin (n+1)) k →+* MvPolynomial (Fin n) k :=
  eval₂Hom MvPolynomial.C (Fin.lastCases (MvPolynomial.C (p (Fin.last n))) MvPolynomial.X)

private theorem dropLast_rename (q : MvPolynomial (Fin n) k) :
    dropLast p (rename Fin.castSucc q) = q := by
  induction q using MvPolynomial.induction_on with
  | C => simp [dropLast]
  | add x y hx hy => simp [hx, hy]
  | mul_X x i hx => simp only [map_mul, rename_X, hx]; simp [dropLast]

private theorem eval_dropLast (q : MvPolynomial (Fin (n+1)) k) :
    eval (p ∘ Fin.castSucc) (dropLast p q) = eval p q := by
  induction q using MvPolynomial.induction_on with
  | C => simp [dropLast]
  | add x y hx hy => simp [hx, hy]
  | mul_X x i hx =>
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      (simp only [map_mul, hx]; simp [dropLast])

/-- A point value determines a cross-multiplied identity even in a fraction presentation
whose denominator happens to vanish at that point. -/
theorem HasValue.eval_fraction {m : ℕ} {p : Fin m → k} {x : M k m} {a b : MvPolynomial (Fin m) k}
    {c : k} (h : HasValue p x c) (hrep : polynomial k a = x * polynomial k b) :
    eval p a = c * eval p b := by
  obtain ⟨u,v,hx,hv,hu⟩ := h
  have e : a * v = u * b := by
    apply IsFractionRing.injective _ (M k m)
    change polynomial k (a*v) = polynomial k (u*b)
    simp only [polynomial,map_mul] at hrep hx ⊢
    rw [hrep,hx]
    ring
  have he := congrArg (eval p) e
  simp only [map_mul,hu] at he
  apply mul_right_cancel₀ hv
  linear_combination he

/-- A lower fraction is regular with value `c` precisely when the same is true after lifting. -/
theorem hasValue_include_iff {x : M k n} :
    HasValue p (includeVars (Nat.le_succ n) x) c ↔ HasValue (p ∘ Fin.castSucc) x c := by
  let L := includeVars (R := k) (Nat.le_succ n)
  have lift_poly (q : MvPolynomial (Fin n) k) :
      L (polynomial k q) = polynomial k (rename Fin.castSucc q) :=
    includeVars_polynomial _ q
  constructor
  · rintro ⟨u,v,hx,hv,hu⟩
    obtain ⟨a,b,hb,hrep⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin n) k) x
    have hb' : polynomial k b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    change polynomial k a / polynomial k b = x at hrep
    have hab := (eq_div_iff hb').mp hrep.symm
    have up : polynomial k (u * rename Fin.castSucc b) =
        polynomial k (rename Fin.castSucc a * v) := by
      change (algebraMap _ _) _ = (algebraMap _ _) _
      rw [map_mul,map_mul]
      change polynomial k u * polynomial k _ = polynomial k _ * polynomial k v
      rw [← lift_poly,← lift_poly,← hab,map_mul,hx]
      ring
    have ed := congrArg (dropLast p) (IsFractionRing.injective _ (M k (n+1)) up)
    simp only [map_mul,dropLast_rename] at ed
    refine ⟨dropLast p u,dropLast p v,?_,by rwa [eval_dropLast],by simpa only [eval_dropLast]⟩
    apply mul_right_cancel₀ hb'
    simp only [polynomial] at hab ⊢
    rw [← map_mul,ed,map_mul,← hab]
    ring
  · rintro ⟨a,b,hx,hb,ha⟩
    refine ⟨rename Fin.castSucc a,rename Fin.castSucc b,?_,by rwa [eval_rename],
      by simpa only [eval_rename]⟩
    rw [← lift_poly,← lift_poly,hx,map_mul]

end SympyProofs.Calculus.Antiderivative.Model
