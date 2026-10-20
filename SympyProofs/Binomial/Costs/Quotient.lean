module

public import SympyProofs.Binomial.Costs.PrimeExponent
public import SympyProofs.Binomial.Costs.OperandBounds
public import SympyProofs.Python.Cost.IntBounds
public import SympyProofs.Python.Cost.LoopBounds
/-!
# Cost and value of the executed Legendre loop

The invariant tracks the carry and the remaining bit length, as well as the
factorial multiplicities. Every nonzero iteration removes a bit and adds at most
one to the exponent. The contract includes initialization and the final exit test.
`quotientStepM` is extracted from the generated kernel and shared with its erasure
proof; the operation contracts below apply directly to that extracted transition.
-/

@[expose] public section

open PythonInt Python.Cost Python.Cost.Models
namespace SympyBinomial.PrimeExponent
variable (I : Type) [PythonInt I]
private abbrev QState := I × I × I × I
private def qstate (a b c e : I) : QState I :=
  (a, b, c, e)
variable (model : Model) (hmodel : ∀ e, model e ≤ schoolbook e)
include hmodel in
private theorem qstep_zero (p b c e : I) :
    Bounded model (quotientStepM (m := CostT Id) I p (qstate I 0 b c e))
      (fun r => r = ForInStep.done (qstate I 0 b c e)) 2 := by
  have h : RunsWith model (quotientStepM (m := CostT Id) I p (qstate I 0 b c e))
      (.done (qstate I 0 b c e)) (model (.integer ⟨.eq, [0, 0], 1⟩)) := by
    intro initial
    simp [quotientStepM, qstate, CostT.run, perform, MonadCost.emit]
    rfl
  exact h.bounded rfl ((hmodel _).trans (by decide))

include hmodel in
private theorem qstep_bound (p a b c e : I) (w : ℕ)
    (hp : width (toInt p) ≤ w) (ha : width (toInt a) ≤ w)
    (hb : width (toInt b) ≤ w) (hc : width (toInt c) ≤ w)
    (he : width (toInt e) ≤ w)
    (had : width (toInt (a/p)) ≤ w) (hbd : width (toInt (b/p)) ≤ w)
    (hcd : width (toInt (c/p)) ≤ w) (hane : a ≠ 0) :
    Bounded model (quotientStepM (m := CostT Id) I p (qstate I a b c e))
      (fun r => r = ForInStep.yield (qstate I (a/p) (b/p) (c/p) (e+(a/p-b/p-c/p))))
      (3*w^2+16*w+16) := by
  have hw : 1 ≤ w := (one_le_width _).trans ha
  have hz : width (toInt (0 : I)) ≤ w := by simpa [width] using hw
  have hd₁ : width (toInt (a/p-b/p)) ≤ w+1 := by
    rw [toInt_sub]
    exact (width_sub _ _).trans (Nat.add_le_add_right (max_le had hbd) 1)
  have hd₂ : width (toInt (a/p-b/p-c/p)) ≤ w+2 := by
    rw [toInt_sub]
    have h := width_sub (toInt (a/p-b/p)) (toInt (c/p))
    omega
  apply Bounded.mono (budget := (w+1)+((1+w*w+3*w)+((1+w*w+3*w)+
    ((1+w*w+3*w)+((2*w+2)+((2*(w+1)+2)+((2*(w+2)+2)+0))))))) ?_
    (by intro _ h; exact h) (by nlinarith [Nat.zero_le w])
  unfold quotientStepM
  simp only [LawfulMonad.bind_assoc]
  refine Bounded.bind (post := fun test => test = (a != 0)) ?_ ?_
  · apply (RunsWith.perform _ _).bounded (post := fun test => test = (a != 0)) rfl
    apply (hmodel _).trans
    change 1 + max (width (toInt a)) (width (toInt (0 : I))) ≤ w+1
    omega
  intro test ht
  subst test
  simp only [qstate, bne, beq_eq_false_iff_ne.mpr hane, Bool.not_false, ↓reduceIte]
  apply (Python.Cost.Int.div_bounded_of_le model hmodel a p w ha hp had).bind
  intro x hx
  subst x
  apply (Python.Cost.Int.div_bounded_of_le model hmodel b p w hb hp hbd).bind
  intro y hy
  subst y
  apply (Python.Cost.Int.div_bounded_of_le model hmodel c p w hc hp hcd).bind
  intro z hz
  subst z
  apply (Python.Cost.Int.sub_bounded_of_le model hmodel (a/p) (b/p) w had hbd).bind
  intro d hd
  subst d
  apply (Python.Cost.Int.sub_bounded_of_le model hmodel (a/p-b/p) (c/p) (w+1) hd₁ (by omega)).bind
  intro d hd
  subst d
  apply (Python.Cost.Int.add_bounded_of_le model hmodel e (a/p-b/p-c/p) (w+2) (by omega) hd₂).bind
  intro f hf
  subst f
  exact Bounded.pure _ rfl


private def QInv (n w p target a b c e : ℕ) : Prop :=
  a ≤ n ∧ b+c ≤ a ∧ a ≤ b+c+1 ∧ e+a.size ≤ w ∧
    (e : ℤ) + a.factorial.factorization p - b.factorial.factorization p -
      c.factorial.factorization p = (target : ℤ)

private theorem QInv.next {n w p target a b c e : ℕ} (h : QInv n w p target a b c e)
    (hp : p.Prime) (ha : 0 < a) :
    QInv n w p target (a/p) (b/p) (c/p) (e+(a/p-b/p-c/p)) := by
  obtain ⟨han, hlo, hhi, he, ht⟩ := h
  obtain ⟨hlo', hhi'⟩ := carry_div a b c p hp.pos hlo hhi
  have hsize := size_div_lt a p ha hp.two_le
  refine ⟨(Nat.div_le_self _ _).trans han, hlo', hhi', ?_, ?_⟩
  · omega
  · rw [factorial_exponent_step a p hp, factorial_exponent_step b p hp,
      factorial_exponent_step c p hp] at ht
    push_cast at ht ⊢
    omega

private theorem nat_width_le (a n : ℕ) (ha : a ≤ n) :
    width (a : ℤ) ≤ inputWidth n := width_mono (by simpa using ha)

private theorem width_self (w : ℕ) : width (w : ℤ) ≤ w+1 := by
  rw [width_eq_log2_succ, Int.natAbs_natCast, Nat.log2_eq_log_two]
  exact Nat.add_le_add_right (Nat.log_le_self 2 w) 1

private theorem div_cast (a p : ℕ) (hp : 0 < p) :
    (a : I)/(p : I) = ((a/p : ℕ) : I) := by
  apply toInt_injective
  simpa using toInt_div_natCast (I := I) a p (by omega)

include hmodel in
private theorem qstep_nat (n p a b c e : ℕ) (hp : p.Prime) (hpn : p ≤ n)
    (ha : 0 < a) (h : QInv n (inputWidth n) p target a b c e) :
    Bounded model (quotientStepM (m := CostT Id) I (p : I) (qstate I (a : I) (b : I) (c : I) (e : I)))
      (fun r => r = ForInStep.yield (qstate I ((a/p : ℕ) : I) ((b/p : ℕ) : I)
        ((c/p : ℕ) : I) ((e+(a/p-b/p-c/p) : ℕ) : I)))
      (3*(inputWidth n+1)^2+16*(inputWidth n+1)+16) := by
  have hb : b ≤ n := by have := h.2.1; have := h.1; omega
  have hc : c ≤ n := by have := h.2.1; have := h.1; omega
  have he : e ≤ inputWidth n := by have := h.2.2.2.1; omega
  have widths (a : ℕ) (ha : a ≤ n) : width (toInt (a : I)) ≤ inputWidth n+1 := by
    rw [toInt_natCast]
    exact (nat_width_le a n ha).trans (by omega)
  have hew : width (toInt (e : I)) ≤ inputWidth n+1 := by
    rw [toInt_natCast]
    exact (width_mono (x := (e : ℤ)) (y := (inputWidth n : ℤ)) (by simpa only [Int.natAbs_natCast] using he)).trans (width_self _)
  have hw := qstep_bound I model hmodel (p : I) (a : I) (b : I) (c : I) (e : I) (inputWidth n+1)
    (widths p hpn) (widths a h.1) (widths b hb) (widths c hc) hew
    (by rw [div_cast I a p hp.pos]; exact widths _ ((Nat.div_le_self _ _).trans h.1))
    (by rw [div_cast I b p hp.pos]; exact widths _ ((Nat.div_le_self _ _).trans hb))
    (by rw [div_cast I c p hp.pos]; exact widths _ ((Nat.div_le_self _ _).trans hc))
    (by intro hz; have hi := congrArg toInt hz; simp only [toInt_natCast, toInt_zero] at hi; omega)
  have hcarries := carry_div a b c p hp.pos h.2.1 h.2.2.1
  have heq : (e : I)+((a : I)/(p : I)-(b : I)/(p : I)-(c : I)/(p : I)) =
      ((e+(a/p-b/p-c/p) : ℕ) : I) := by
    rw [div_cast I a p hp.pos, div_cast I b p hp.pos, div_cast I c p hp.pos]
    apply toInt_injective
    simp only [toInt_add, toInt_sub, toInt_natCast]
    omega
  rw [heq] at hw
  simpa only [div_cast I a p hp.pos, div_cast I b p hp.pos, div_cast I c p hp.pos,
    Nat.add_assoc, Nat.reduceAdd] using hw


include hmodel in
/-- The executed quotient loop returns the exact prime multiplicity within a cubic bit budget. -/
theorem quotientExponentM_bounded_of_le (n k p : ℕ) (hk : k ≤ n) (hp : p.Prime) (hpn : p ≤ n) :
    Bounded model (quotientExponentM (m := CostT Id) I (n : I) (k : I) (p : I))
      (fun e => toInt e = ((n.choose k).factorization p : ℤ))
      (64*inputWidth n^3) := by
  let W := inputWidth n
  let target := (n.choose k).factorization p
  let inv (s : QState I) := ∃ a b c e : ℕ,
    s = qstate I (a : I) (b : I) (c : I) (e : I) ∧ QInv n W p target a b c e
  let post (s : QState I) := ∃ e : ℕ,
    s = qstate I 0 0 0 (e : I) ∧ e = target
  let rank (s : QState I) := (toNat s.1).size
  have hbody (s : QState I) (hs : inv s) :
      Bounded model (quotientStepM (m := CostT Id) I (p : I) s)
        (fun r => match r with
          | .done t => post t
          | .yield t => inv t ∧ rank t < rank s) ((3*(W+1)^2+16*(W+1)+16)) := by
    obtain ⟨a,b,c,e,rfl,h⟩ := hs
    by_cases ha : a = 0
    · subst a
      have hb : b = 0 := by have := h.2.1; omega
      have hc : c = 0 := by have := h.2.1; omega
      subst b; subst c
      have ht : e = target := by
        have ht := h.2.2.2.2
        simpa [QInv] using ht
      simp only [Nat.cast_zero]
      apply (qstep_zero I model hmodel (p : I) 0 0 (e : I)).mono
      · intro r hr; subst r; exact ⟨e, rfl, ht⟩
      · nlinarith [Nat.zero_le W]
    · have hstep := qstep_nat I model hmodel n p a b c e hp hpn (by omega) h
      apply hstep.mono
      · intro r hr
        subst r
        refine ⟨⟨a/p,b/p,c/p,e+(a/p-b/p-c/p),rfl,QInv.next h hp (by omega)⟩, ?_⟩
        change (toNat ((a/p : ℕ) : I)).size < (toNat (a : I)).size
        simpa only [toNat_natCast] using size_div_lt a p (by omega) hp.two_le
      · rfl
  have hi : inv (qstate I (n : I) (k : I) ((n-k : ℕ) : I) 0) := by
    refine ⟨n,k,n-k,0,by simp only [Nat.cast_zero],le_refl _,by omega,by omega,?_,?_⟩
    · simpa only [W, inputWidth, width, Int.natAbs_natCast, Nat.zero_add] using (le_max_right 1 n.size)
    · simpa using factorial_exponent_sub n k p hk
  have hloop := Bounded.loop (model := model) (quotientStepM (m := CostT Id) I (p : I)) inv post rank ((3*(W+1)^2+16*(W+1)+16)) (fun s hs => (hbody s hs).mono (by intro r hr; cases r <;> exact hr) (le_refl _)) _ hi
  have hreturn := hloop.bind (next := fun s => pure s.2.2.2)
    (post' := fun e => toInt e = (target : ℤ)) (d := 0) (by
      intro s hs
      obtain ⟨e,rfl,he⟩ := hs
      exact Bounded.pure (e : I) (by simpa only [he] using toInt_natCast (I := I) e))
  have hinit := Python.Cost.Int.sub_bounded_of_le model hmodel (n : I) (k : I) W
    (by simp only [toInt_natCast]; rfl)
    (by simpa only [toInt_natCast] using nat_width_le k n hk)
  have hsub : (n : I)-(k : I) = ((n-k : ℕ) : I) := by
    apply toInt_injective
    simp only [toInt_sub,toInt_natCast]
    omega
  rw [quotientExponentM_eq]
  refine Bounded.mono (post := fun e => toInt e = (target : ℤ))
    (budget := (2*W+2)+((rank (qstate I (n : I) (k : I) ((n-k : ℕ) : I) 0)+1)*
      (3*(W+1)^2+16*(W+1)+16)+0)) ?_ (fun e he => he) ?_
  · apply hinit.bind
    intro c hc
    subst c
    rw [hsub]
    exact hreturn
  have hrank : rank (qstate I (n : I) (k : I) ((n-k : ℕ) : I) 0) = n.size := by
    simp only [rank, qstate, toNat_natCast]
  rw [hrank]
  change (2*W+2)+((n.size+1)*((3*(W+1)^2+16*(W+1)+16))+0) ≤ 64*W^3
  have hw : 1 ≤ W := inputWidth_pos n
  have hs : n.size ≤ W := by simpa only [W,inputWidth,width,Int.natAbs_natCast] using (le_max_right 1 n.size)
  have hw2 : 2 ≤ W := by
    have h : width (2 : ℤ) ≤ W := nat_width_le 2 n (hp.two_le.trans hpn)
    have htwo : width (2 : ℤ) = 2 := by decide
    omega
  have hfirst : (n.size+1)*(3*(W+1)^2+16*(W+1)+16) ≤
      (W+1)*(3*(W+1)^2+16*(W+1)+16) := Nat.mul_le_mul_right _ (by omega)
  have hsq : 2*W^2 ≤ W^3 := by nlinarith only [Nat.mul_le_mul_right (W*W) hw2]
  have hlin : 4*W ≤ W^3 := by nlinarith only [hsq,Nat.mul_le_mul_right W hw2]
  have hconst : 8 ≤ W^3 := by nlinarith only [hlin,hw2]
  nlinarith only [hfirst,hsq,hlin,hconst]

/-- Schoolbook specialization of the policy-parametric quotient-loop contract. -/
theorem quotientExponentM_bounded (n k p : ℕ) (hk : k ≤ n) (hp : p.Prime) (hpn : p ≤ n) :
    Bounded schoolbook (quotientExponentM (m := CostT Id) I (n : I) (k : I) (p : I))
      (fun e => toInt e = ((n.choose k).factorization p : ℤ)) (64*inputWidth n^3) :=
  quotientExponentM_bounded_of_le I schoolbook (fun _ => le_refl _) n k p hk hp hpn

end SympyBinomial.PrimeExponent
