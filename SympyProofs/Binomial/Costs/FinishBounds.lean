module

public import SympyProofs.Binomial.Costs.BalancedFactors
public import SympyProofs.Binomial.Costs.FactorBounds
public import SympyProofs.Binomial.Costs.PrimeExponentAsymptotics

/-! Product tree, valuation, and final shift under the full input-size invariant. -/

@[expose] public section
open Python.Cost Python.Cost.Models PythonInt
namespace SympyBinomial.PrimeExponent
variable (I : Type) [PythonInt I]

private theorem factor_index_width (n : ℕ) (s : ℕ) (hs : s ≤ 2*n+1) :
    width (s : ℤ) ≤ 6*inputWidth n := by
  let W := inputWidth n
  have hw : 1 ≤ W := inputWidth_pos n
  have hm := width_mul (2 : ℤ) (n : ℤ)
  have ha := width_add (2*(n : ℤ)) 1
  have h2 : width (2 : ℤ) = 2 := by decide
  have h1 : width (1 : ℤ) = 1 := by decide
  rw [h2] at hm
  rw [h1] at ha
  have hmono : width (s : ℤ) ≤ width ((2*n+1 : ℕ) : ℤ) :=
    width_mono (by simpa only [Int.natAbs_natCast] using hs)
  norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hmono
  have hmax : max (width (2*(n : ℤ))) 1 ≤ 2+W := max_le hm (by omega)
  change _ ≤ 6*W
  omega

/-- The tree's actual cost and returned width, using the total factor payload. -/
theorem product_finish_bounded (n k : ℕ) (hk : k ≤ n) (factors : Array I)
    (hs : factors.size ≤ factorBits n k) (hb : Sequence.inputBits factors ≤ factorBits n k) :
    Bounded schoolbook (balancedFactorsM (m := CostT Id) I factors)
      (fun r => width (toInt r) ≤ 4*(n+1)) (73792*(n+1)^2) := by
  have hf := factorBits_le_upper n k hk
  have hw : 1 ≤ inputWidth n := inputWidth_pos n
  have h := balancedFactorsM_bounded I factors (6*inputWidth n) (by omega)
    (factor_index_width n factors.size (hs.trans hf))
  apply h.mono
  · intro r hr; omega
  · have hS : Sequence.inputBits factors+1 ≤ 2*(n+1) := by omega
    have hsize : factors.size+1 ≤ 2*(n+1) := by omega
    have hsq : (Sequence.inputBits factors+1)^2 ≤ 4*(n+1)^2 := by nlinarith only [hS]
    have hW : inputWidth n^2 ≤ 8*(n+1) :=
      (Nat.pow_le_pow_right hw (by omega : 2 ≤ 3)).trans (inputWidth_cube_le n)
    have hmul := Nat.mul_le_mul hW hsize
    nlinarith only [hsq,hmul]

/-- Restore the power of two, including all three popcounts and the output shift. -/
theorem valuation_shift_bounded (n k : ℕ) (hk : k ≤ n) (value : I)
    (hv : width (toInt value) ≤ 4*(n+1)) :
    Bounded schoolbook (do
      let shift ← valuationM (m := CostT Id) I (n:I) (k:I)
      Python.Cost.Int.shiftLeft value shift) (fun _ => True) (64*(n+1)) := by
  let E := (n.choose k).factorization 2
  let shift := valuation I (n:I) (k:I)
  have he : toInt shift = (E : ℤ) := by
    simpa only [toNat_natCast] using valuation_eq_factorization I (n:I) (k:I) (by simp) (by simpa using hk)
  have hE : E ≤ n := Nat.factorization_choose_le_log.trans (Nat.log_le_self 2 n)
  have hshift : width (toInt shift) ≤ inputWidth n := by
    rw [he]
    apply width_mono
    simpa only [Int.natAbs_natCast] using hE
  have hval : Bounded schoolbook (valuationM (m := CostT Id) I (n:I) (k:I))
      (fun r => r = shift) (29*inputWidth n) := by
    apply (show RunsWith schoolbook (valuationM (m := CostT Id) I (n:I) (k:I)) shift
      (charge schoolbook (valuationEvents I (n:I) (k:I))) from fun initial => valuation_run I (n:I) (k:I) schoolbook initial).bounded
      (post := fun r => r = shift) rfl
    have h := valuation_schoolbook_le I (n:I) (k:I)
    have hkn : width (k : ℤ) ≤ inputWidth n := width_mono (by simpa only [Int.natAbs_natCast] using hk)
    have hcost : charge schoolbook (valuationEvents I (n:I) (k:I)) ≤
        29*max (inputWidth n) (width (k:ℤ)) := by
      simpa only [valuationCost,valuation_run,Nat.zero_add,toInt_natCast,inputWidth] using h
    exact hcost.trans (Nat.mul_le_mul_left 29 (max_le (le_refl _) hkn))
  have hresult : width (toInt (value <<< shift)) ≤ 5*(n+1) := by
    rw [toInt_shiftLeft _ _ (by rw [he]; exact_mod_cast Nat.zero_le E),he,Int.toNat_natCast]
    have hpow : width ((2 : ℤ)^E) = E+1 := by
      simp only [width,Int.natAbs_pow,show (2 : ℤ).natAbs = 2 from rfl,Nat.size_pow,Nat.max_eq_right (by omega : 1 ≤ E+1)]
    have h := width_mul (toInt value) ((2:ℤ)^E)
    rw [hpow] at h
    omega
  have hs : Bounded schoolbook (Python.Cost.Int.shiftLeft value shift) (fun _ => True) (35*(n+1)) := by
    apply (RunsWith.perform _ _).bounded trivial
    simp only [schoolbook,integerSchoolbook,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
    have hw := inputWidth_le n
    omega
  have hall := hval.bind (next := fun shift => Python.Cost.Int.shiftLeft value shift)
    (post' := fun _ => True) (d := 35*(n+1)) (by intro r hr; subst r; exact hs)
  exact hall.mono (fun _ _ => trivial) (by have h := inputWidth_le n; omega)
end SympyBinomial.PrimeExponent
