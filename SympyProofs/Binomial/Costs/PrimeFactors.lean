module

public import SympyProofs.Binomial.Costs.Quotient
public import SympyProofs.Python.Cost.IntBounds
public import SympyProofs.Python.Cost.Asymptotics
/-!
# Resource contract for one generated prime

This composes the quotient-loop contract with the power, zero test, and append.
Both branches return the exact expected factor array. The allocation charge is
included even though the input array size does not affect its amortized policy.
-/

@[expose] public section

open PythonInt Python.Cost Python.Cost.Models
namespace SympyBinomial.PrimeExponent
variable (I : Type) [PythonInt I]
/-- An actual prime-consumer step, including the optional power and allocation. -/
theorem primeFactorM_bounded (n k p : ℕ) (hk : k ≤ n) (hp : p.Prime) (hpn : p ≤ n)
    (factors : Array I) :
    Bounded schoolbook (primeFactorM (m := CostT Id) I (n : I) (k : I) p factors)
      (fun r => r = if (n.choose k).factorization p = 0 then factors
        else factors.push ((p ^ (n.choose k).factorization p : ℕ) : I))
      (128*inputWidth n^3) := by
  let E := (n.choose k).factorization p
  let W := inputWidth n
  have hw : 1 ≤ W := inputWidth_pos n
  have hn : 0 < n := lt_of_lt_of_le hp.pos hpn
  have hew : width (toInt (E : I)) ≤ W := by
    rw [toInt_natCast]
    apply width_mono
    simpa only [Int.natAbs_natCast] using
      (Nat.factorization_choose_le_log (n := n) (k := k) (p := p)).trans (Nat.log_le_self p n)
  have hzero : width (toInt (0 : I)) ≤ W := by simpa [width] using hw
  have hpow : Bounded schoolbook (Python.Cost.Int.pow (p : I) (E : I))
      (fun r => r = ((p^E : ℕ) : I)) (4*W^3) := by
    have hr : (p : I) ^ (E : I) = ((p^E : ℕ) : I) := by
      apply toInt_injective
      rw [toInt_pow _ _ (by simp), toInt_natCast, toInt_natCast, Int.toNat_natCast,
        toInt_natCast, Nat.cast_pow]
    apply (RunsWith.perform _ ((p : I)^(E : I))).bounded (post := fun r => r = ((p^E : ℕ) : I)) hr
    simpa only [hr, toInt_natCast] using primePower_schoolbook_le n k p hn hpn
  rw [primeFactorM_eq]
  apply Bounded.mono (budget := 1+(64*W^3+((W+1)+(4*W^3+2)))) ?_
    (by intro _ h; exact h) (by
      have hc : W ≤ W^3 := Nat.le_self_pow (by omega) W
      nlinarith only [hc,hw])
  have hstart : Bounded schoolbook (MonadCost.emit (.control "for.next")) (fun _ => True) 1 :=
    (RunsWith.emit _).bounded trivial (by rfl)
  apply hstart.bind
  intro _ _
  apply (quotientExponentM_bounded I n k p hk hp hpn).bind
  intro e he
  have heq : e = (E : I) := toInt_injective (he.trans (toInt_natCast E).symm)
  subst e
  apply (Python.Cost.Int.eq_bounded (E : I) 0 W hew hzero).bind
  intro test ht
  subst test
  by_cases hz : E = 0
  · simp only [hz, show (n.choose k).factorization p = 0 from hz, Nat.cast_zero,
      beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact (Bounded.pure (post := fun r => r = factors) factors rfl).mono
      (fun _ h => h) (Nat.zero_le _)
  · have hzI : (E : I) ≠ 0 := by
      intro h
      have ht := congrArg toInt h
      simp only [toInt_natCast,toInt_zero] at ht
      omega
    simp only [show (n.choose k).factorization p ≠ 0 from hz,
      beq_eq_false_iff_ne.mpr hzI, Bool.not_false, ↓reduceIte]
    apply hpow.bind
    intro value hv
    subst value
    exact (RunsWith.perform _ _).bounded
      (post := fun r => r = factors.push ((p^E : ℕ) : I)) rfl (by rfl)

/-- A uniform cubic bit-width bound on every valid prime-consumer call. -/
theorem primeFactorM_isBigO {X : Type} (l : Filter X) (n k p : X → ℕ)
    (hk : ∀ x, k x ≤ n x) (hp : ∀ x, (p x).Prime) (hpn : ∀ x, p x ≤ n x)
    (factors : X → Array I) :
    (fun x => ((CostT.run
      (primeFactorM (m := CostT Id) I (n x : I) (k x : I) (p x) (factors x)) schoolbook).2 : ℝ)) =O[l]
      (fun x => ((inputWidth (n x)^3 : ℕ) : ℝ)) :=
  nat_isBigO_of_le_mul 128 (fun x =>
    (primeFactorM_bounded I (n x) (k x) (p x) (hk x) (hp x) (hpn x) (factors x)).cost_le)

end SympyBinomial.PrimeExponent
