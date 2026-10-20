module

public import SympyProofs.Binomial.Costs.KaratsubaFactors
public import SympyProofs.Binomial.Costs.KaratsubaProduct
public import SympyProofs.Binomial.Costs.FinishBounds
public import SympyProofs.Binomial.Costs.PrimeExponentErasure

/-! # A complete execution budget with Karatsuba multiplication -/

@[expose] public section
open Python.Cost Python.Cost.Models Python.Cost.Karatsuba PythonInt
namespace SympyBinomial.PrimeExponent
variable (I : Type) [PythonInt I]

/-- Valuation and shift, allowing an arbitrary bound on the product's width. -/
theorem valuation_shift_bounded_width (model : Model) (hmodel : ∀ e, model e ≤ schoolbook e)
    (n k V : ℕ) (hk : k ≤ n) (value : I) (hv : width (toInt value) ≤ V) :
    Bounded model (do
      let shift ← valuationM (m := CostT Id) I (n:I) (k:I)
      Python.Cost.Int.shiftLeft value shift) (fun _ => True) (64*(n+1)+2*V) := by
  let E := (n.choose k).factorization 2
  let shift := valuation I (n:I) (k:I)
  have he : toInt shift = (E:ℤ) := by
    simpa only [toNat_natCast] using valuation_eq_factorization I (n:I) (k:I)
      (by simp) (by simpa using hk)
  have hE : E ≤ n := Nat.factorization_choose_le_log.trans (Nat.log_le_self 2 n)
  have hshift : width (toInt shift) ≤ inputWidth n := by
    rw [he]
    exact width_mono (by simpa using hE)
  have hval : Bounded model (valuationM (m := CostT Id) I (n:I) (k:I))
      (fun r => r = shift) (29*inputWidth n) := by
    apply (show RunsWith model (valuationM (m := CostT Id) I (n:I) (k:I)) shift
      (charge model (valuationEvents I (n:I) (k:I))) from
        fun initial => valuation_run I (n:I) (k:I) model initial).bounded
      (post := fun r => r = shift) rfl
    have hle : charge model (valuationEvents I (n:I) (k:I)) ≤
        charge schoolbook (valuationEvents I (n:I) (k:I)) :=
      List.sum_le_sum (fun _ _ => hmodel _)
    apply hle.trans
    have h := valuation_schoolbook_le I (n:I) (k:I)
    have hkn : width (k:ℤ) ≤ inputWidth n := width_mono (by simpa using hk)
    have hc : charge schoolbook (valuationEvents I (n:I) (k:I)) ≤
        29*max (inputWidth n) (width (k:ℤ)) := by
      simpa only [valuationCost,valuation_run,Nat.zero_add,toInt_natCast,inputWidth] using h
    exact hc.trans (Nat.mul_le_mul_left _ (max_le (le_refl _) hkn))
  have hresult : width (toInt (value <<< shift)) ≤ V+n+1 := by
    rw [toInt_shiftLeft _ _ (by rw [he]; positivity),he,Int.toNat_natCast]
    have hpow : width ((2:ℤ)^E) = E+1 := by
      simp only [width,Int.natAbs_pow,show (2:ℤ).natAbs=2 from rfl,Nat.size_pow,
        Nat.max_eq_right (by omega : 1 ≤ E+1)]
    have h := width_mul (toInt value) ((2:ℤ)^E)
    rw [hpow] at h
    omega
  have hs : Bounded model (Python.Cost.Int.shiftLeft value shift) (fun _ => True)
      (2*V+3*(n+1)) := by
    apply (RunsWith.perform _ _).bounded trivial
    apply (hmodel _).trans
    simp only [schoolbook,integerSchoolbook,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some]
    have := inputWidth_le n
    omega
  have h := hval.bind (next := fun shift => Python.Cost.Int.shiftLeft value shift)
    (post' := fun _ => True) (d := 2*V+3*(n+1)) (by intro r hr; subst r; exact hs)
  exact h.mono (fun _ _ => trivial) (by have := inputWidth_le n; omega)

def karatsubaBudget (n : ℕ) : ℕ :=
  256*(n.sqrt+1)*(n+1+inputWidth n^2)+32768*(n+1)*inputWidth n^3+
    200001*work (n.primeCounting+1)*work (inputWidth n)

/-- Every generated phase is charged: sieve, scans, consumer, product, and final shift. -/
theorem primeExponentsM_karatsuba_budgeted (B : Type) [PythonByteArray B]
    (n k : ℕ) (hk : k ≤ n) :
    Bounded karatsuba (primeExponentsM (m := CostT Id) I B (n:I) (k:I))
      (fun _ => True) (karatsubaBudget n) := by
  let W := inputWidth n
  let N := n+1
  let P := n.primeCounting
  let Q := 200001*work (P+1)*work W+128*(6*W)^2*(P+1)
  let F := 64*N+4*(P+1)*W
  have hw : 1 ≤ W := inputWidth_pos n
  have hpn : P ≤ N := Nat.count_le Nat.Prime
  have hkn : width (toInt (k:I)) ≤ W := by
    rw [toInt_natCast]; exact width_mono (by simpa using hk)
  have hz : width (toInt (0:I)) ≤ W := by simpa [width] using hw
  apply Bounded.mono (post := fun _ => True)
    (budget := (W+1)+(1+(collectionBudget n+(1+(Q+F))))) ?_ (fun _ _ => trivial) ?_
  · rw [primeExponentsM_eq]
    simp only [toNat_natCast]
    apply (Python.Cost.Int.eq_bounded_of_le karatsuba karatsuba_le_schoolbook (k:I) 0 W hkn hz).bind
    intro test _
    cases test
    · simp only [Bool.false_eq_true,↓reduceIte]
      have he : Bounded karatsuba (Sequence.empty (m := CostT Id) (α := I))
          (fun factors => factors = #[]) 1 := (RunsWith.perform _ _).bounded rfl (by rfl)
      apply he.bind
      intro factors hf
      subst factors
      apply (factors_bounded_count I B karatsuba karatsuba_le_schoolbook n k hk).bind
      intro factors hf
      have hstop : Bounded karatsuba (MonadCost.emit (.control "for.stop")) (fun _ => True) 1 :=
        (RunsWith.emit _).bounded trivial (by rfl)
      apply hstop.bind
      intro _ _
      have hprod := balancedFactorsM_karatsuba_bounded I factors W (6*W) hw (by omega)
        (factor_index_width n factors.size (by omega)) hf.2
      have hprod' : Bounded karatsuba (balancedFactorsM (m := CostT Id) I factors)
          (fun r => width (toInt r) ≤ 2*(P+1)*W) Q := by
        apply hprod.mono
        · intro r hr; exact hr.trans (by gcongr; exact hf.1)
        · dsimp [Q]
          gcongr
          · exact work_mono (by omega)
          · omega
      apply hprod'.bind
      intro value hv
      have h := valuation_shift_bounded_width I karatsuba karatsuba_le_schoolbook
        n k (2*(P+1)*W) hk value hv
      convert h using 1
      dsimp [F,N]
      ring
    · simp only [↓reduceIte]
      exact (Bounded.pure (post := fun _ => True) (1:I) trivial).mono
        (fun _ _ => trivial) (Nat.zero_le _)
  · have hW : W ≤ W^3 := Nat.le_self_pow (by omega) W
    have hW2 : W^2 ≤ W^3 := Nat.pow_le_pow_right hw (by omega)
    have h1 : 1 ≤ W^3 := Nat.one_le_pow 3 W hw
    have hN : 1 ≤ N := by dsimp [N]; omega
    have hP : P+1 ≤ 2*N := by omega
    have hidx := Nat.mul_le_mul hW2 hP
    have hval := Nat.mul_le_mul hW hP
    have hlin := Nat.mul_le_mul_left N hW2
    have hconst := Nat.mul_le_mul_left N h1
    have hstart := Nat.mul_le_mul_right (N+W^2) (show 1 ≤ n.sqrt+1 by omega)
    have hWn := inputWidth_le n
    dsimp only [Q,F,collectionBudget,karatsubaBudget]
    change (W+1)+(1+(128*(n.sqrt+1)*(N+W^2)+4*(N+W^2)+
      N*(64*(1+W^2)+128*W^3)+(1+(200001*work (P+1)*work W+
      128*(6*W)^2*(P+1)+(64*N+4*(P+1)*W))))) ≤
      256*(n.sqrt+1)*(N+W^2)+32768*N*W^3+200001*work (P+1)*work W
    nlinarith only [hidx,hval,hlin,hconst,hstart,hWn,hN]

/-- Correct value and full generated execution budget under the faster policy. -/
theorem primeExponentsM_karatsuba_correct_bounded (B : Type) [PythonByteArray B]
    (n k : ℕ) (hk : k ≤ n) :
    Bounded karatsuba (primeExponentsM (m := CostT Id) I B (n:I) (k:I))
      (fun r => toInt r = (n.choose k:ℤ)) (karatsubaBudget n) := by
  intro initial
  obtain ⟨r,c,hr,_,hc⟩ := primeExponentsM_karatsuba_budgeted I B n k hk initial
  refine ⟨r,c,hr,?_,hc⟩
  have h := primeExponentsM_run_eq_choose I B (n:I) (k:I) (by simp) (by simpa using hk)
    karatsuba initial
  simpa only [hr,toNat_natCast] using h

end SympyBinomial.PrimeExponent
