module

public import SympyProofs.Python.Cost.Karatsuba.Model
public import SympyProofs.Python.Cost.SequenceBounds

/-! # Executed multiplication and fixed-size product leaves under the Karatsuba policy -/

@[expose] public section
namespace Python.Cost.Karatsuba
open PythonInt Models
variable {I : Type} [PythonInt I]

theorem mul_bounded (a b : I) (wa wb : ℕ)
    (ha : width (toInt a) ≤ wa) (hb : width (toInt b) ≤ wb) :
    Bounded karatsuba (Python.Cost.Int.mul a b)
      (fun r => width (toInt r) ≤ wa+wb) (1+work (max wa wb)+wa+wb) := by
  apply (RunsWith.perform _ _).bounded
  · simpa only [toInt_mul] using (width_mul (toInt a) (toInt b)).trans (Nat.add_le_add ha hb)
  · change 1 + min _ (work (max (width (toInt a)) (width (toInt b)))) +
        width (toInt (a*b)) ≤ _
    have hwork := work_mono (max_le_max ha hb)
    have hresult : width (toInt (a*b)) ≤ wa+wb := by
      simpa only [toInt_mul] using (width_mul (toInt a) (toInt b)).trans (Nat.add_le_add ha hb)
    have hmin := min_le_right (width (toInt a)*width (toInt b))
      (work (max (width (toInt a)) (width (toInt b))))
    omega

private theorem leaf_fold (xs : List I) (s : I) (t w : ℕ) (hw : 1 ≤ w)
    (ht : t+xs.length ≤ 33) (hs : width (toInt s) ≤ t*w)
    (hx : ∀ x ∈ xs, width (toInt x) ≤ w) :
    Bounded karatsuba
      (xs.foldlM (fun s x => do
        MonadCost.emit (.control "prod.next")
        Python.Cost.Int.mul s x) s)
      (fun r => width (toInt r) ≤ (t+xs.length)*w)
      (xs.length*(4*work (64*w))) := by
  induction xs generalizing s t with
  | nil => simpa using (Bounded.pure s hs : Bounded karatsuba _ _ 0)
  | cons x xs ih =>
    have hm := mul_bounded s x (t*w) w hs (hx x (by simp))
    have he : Bounded karatsuba (MonadCost.emit (.control "prod.next")) (fun _ => True) 1 :=
      (RunsWith.emit _).bounded trivial (by rfl)
    have hstep := he.bind (next := fun _ => Python.Cost.Int.mul s x) (fun _ _ => hm)
    have hstep' : Bounded karatsuba
        (do MonadCost.emit (.control "prod.next"); Python.Cost.Int.mul s x)
        (fun r => width (toInt r) ≤ (t+1)*w) (4*work (64*w)) := by
      apply hstep.mono
      · intro r hr; nlinarith only [hr]
      · have ht' : t ≤ 32 := by simp only [List.length_cons] at ht; omega
        have hcap : max (t*w) w ≤ 64*w := by
          apply max_le <;> nlinarith
        have hwork := work_mono hcap
        have hb := bits_le_work (64*w)
        have hp := work_pos (64*w)
        nlinarith only [hwork, hb, hp, Nat.mul_le_mul_right w ht', hw]
    have h := hstep'.bind (fun r hr => ih r (t+1) (by simp only [List.length_cons] at ht; omega) hr
      (by intro y hy; exact hx y (by simp [hy])))
    simpa only [List.foldlM_cons, List.length_cons, Nat.add_assoc,
      Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.add_comm, Nat.add_left_comm] using h

/-- The actual sequential leaf, including loop control, costs a constant multiple
of the Karatsuba envelope when it has at most 32 bounded-width factors. -/
theorem prod_leaf_bounded (xs : Array I) (w : ℕ) (hw : 1 ≤ w)
    (hlen : xs.size ≤ 32) (hx : ∀ x ∈ xs, width (toInt x) ≤ w) :
    Bounded karatsuba (Sequence.prod (m := CostT Id) xs)
      (fun r => width (toInt r) ≤ (xs.size+1)*w) (100000*work w) := by
  have hf := leaf_fold xs.toList (1:I) 1 w hw (by simp only [Array.length_toList]; omega)
    (by simpa [width] using hw) (by simpa using hx)
  have hstop (r : I) : Bounded karatsuba
      (do MonadCost.emit (.control "prod.stop"); pure r) (fun v => v = r) 1 :=
    (RunsWith.bind (RunsWith.emit _) (RunsWith.pure r)).bounded rfl (by rfl)
  have h := hf.bind (post' := fun r => width (toInt r) ≤ (xs.size+1)*w)
    (fun r hr => (hstop r).mono (by intro v hv; subst v; simpa [Nat.add_comm] using hr)
      (le_refl _))
  rw [Array.foldlM_toList] at h
  apply h.mono (fun _ hr => hr)
  have hwork := work_mul_le 64 w
  have h64 : work 64 = 729 := by decide
  rw [h64] at hwork
  have hp := work_pos w
  simp only [Array.length_toList]
  have hc := Nat.mul_le_mul_right (4*work (64*w)) hlen
  nlinarith only [hc,hwork,hp]

end Python.Cost.Karatsuba
