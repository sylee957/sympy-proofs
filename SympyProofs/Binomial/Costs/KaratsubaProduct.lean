module

public import SympyProofs.Binomial.Costs.BalancedFactors
public import SympyProofs.Python.Cost.Karatsuba.Bounds

/-!
# Karatsuba bound for the generated product tree

The tree splits by factor count. A depth bound and a bound on each factor's
width pay for every multiplication, including the sequential leaves. This
proof uses the generated recursion equation; it introduces no reference loop.
-/

@[expose] public section
open PythonInt Python.Cost Python.Cost.Models Python.Cost.Karatsuba
namespace SympyBinomial.PrimeExponent
variable (I : Type) [PythonInt I]

private theorem extract_width (xs : Array I) (lo hi w : ℕ)
    (hx : ∀ x ∈ xs, width (toInt x) ≤ w) :
    ∀ x ∈ xs.extract lo hi, width (toInt x) ≤ w := by
  intro x h
  obtain ⟨j, hj, hval⟩ := Array.mem_extract_iff_getElem.mp h
  rw [← hval]
  exact hx _ (Array.getElem_mem ..)

private theorem rec_karatsuba_bounded (xs : Array I) (w v d : ℕ)
    (hw : 1 ≤ w) (hv : 6 ≤ v) (hsize : width (xs.size : ℤ) ≤ v)
    (hx : ∀ x ∈ xs, width (toInt x) ≤ w)
    (lo hi : ℕ) (hlo : lo < hi) (hhi : hi ≤ xs.size) (hd : hi-lo ≤ 2^d) :
    Bounded karatsuba (balancedFactorsM.rec (m := CostT Id) I xs 32 (by omega) lo hi)
      (fun r => width (toInt r) ≤ 2*(hi-lo)*w)
      (200000*3^d*work w+64*v^2*(2*(hi-lo)-1)) := by
  induction d generalizing lo hi with
  | zero =>
    have hlen : hi-lo = 1 := by norm_num at hd; omega
    have hs : (xs.extract lo hi).size = hi-lo := by simp [Nat.min_eq_left hhi]
    have hlw : width (lo:ℤ) ≤ v := (width_mono (by simp; omega)).trans hsize
    have hhw : width (hi:ℤ) ≤ v := (width_mono (by simpa using hhi)).trans hsize
    have hcw : width ((hi-lo:ℕ):ℤ) ≤ v := by simp [hlen,width]; omega
    have h32 : width (32:ℤ) ≤ v := by
      have : width (32:ℤ)=6 := by decide
      omega
    rw [balancedFactorsM_rec_eq]
    simp only [show hi-lo ≤ 32 by omega, ↓reduceIte]
    have hsub := (Index.sub_bounded hi lo v hhw hlw).reprice_perform (karatsuba_le_schoolbook _)
    have hle := (Index.le_bounded (hi-lo) 32 v hcw h32).reprice_perform (karatsuba_le_schoolbook _)
    have hslice : Bounded karatsuba (Sequence.slice xs lo hi)
        (fun r => r = xs.extract lo hi) (1+2*(hi-lo)) :=
      (RunsWith.perform _ _).bounded rfl (by change 1+_+_ ≤ _; rw [hs]; omega)
    have h := hsub.bind fun _ _ => hle.bind fun _ _ =>
      hslice.bind fun ys hys => by
        subst ys
        exact prod_leaf_bounded _ w hw (by omega) (extract_width I xs lo hi w hx)
    apply h.mono
    · intro r hr; rw [hs,hlen] at hr; rw [hlen]; omega
    · have hp := work_pos w
      simp only [pow_zero, hlen]
      nlinarith
  | succ d ih =>
    have hs : (xs.extract lo hi).size = hi-lo := by simp [Nat.min_eq_left hhi]
    have hlw : width (lo:ℤ) ≤ v := (width_mono (by simp; omega)).trans hsize
    have hhw : width (hi:ℤ) ≤ v := (width_mono (by simpa using hhi)).trans hsize
    have hcw : width ((hi-lo:ℕ):ℤ) ≤ v :=
      (width_mono (by simp)).trans hhw
    have h32 : width (32:ℤ) ≤ v := by
      have : width (32:ℤ)=6 := by decide
      omega
    have hsub := (Index.sub_bounded hi lo v hhw hlw).reprice_perform (karatsuba_le_schoolbook _)
    have hle := (Index.le_bounded (hi-lo) 32 v hcw h32).reprice_perform (karatsuba_le_schoolbook _)
    rw [balancedFactorsM_rec_eq]
    by_cases hcut : hi-lo ≤ 32
    · simp only [hcut, ↓reduceIte]
      have hslice : Bounded karatsuba (Sequence.slice xs lo hi)
          (fun r => r = xs.extract lo hi) (1+2*(hi-lo)) :=
        (RunsWith.perform _ _).bounded rfl (by change 1+_+_ ≤ _; rw [hs]; omega)
      have h := hsub.bind fun _ _ => hle.bind fun _ _ =>
        hslice.bind fun ys hys => by
          subst ys
          exact prod_leaf_bounded _ w hw (by omega) (extract_width I xs lo hi w hx)
      apply h.mono
      · intro r hr
        rw [hs] at hr
        have : (hi-lo+1)*w ≤ 2*(hi-lo)*w := Nat.mul_le_mul_right _ (by omega)
        exact hr.trans this
      · have hp : 1 ≤ 3^(d+1) := Nat.succ_le_of_lt (by positivity)
        have hc := Nat.mul_le_mul_right (work w) (Nat.mul_le_mul_left 200000 hp)
        have hn := Nat.mul_le_mul_left (64*v^2) (show 1 ≤ 2*(hi-lo)-1 by omega)
        nlinarith only [hc,hn,hcut,hv]
    · simp only [hcut, ↓reduceIte]
      let mid := (lo+hi)/2
      have hml : lo < mid := by dsimp [mid]; omega
      have hmh : mid < hi := by dsimp [mid]; omega
      have hdl : mid-lo ≤ 2^d := by dsimp [mid]; rw [pow_succ] at hd; omega
      have hdr : hi-mid ≤ 2^d := by dsimp [mid]; rw [pow_succ] at hd; omega
      have hleft := ih lo mid hml (by omega) hdl
      have hright := ih mid hi hmh hhi hdr
      have hsumw : width ((lo+hi:ℕ):ℤ) ≤ v+1 := by
        simpa only [Nat.cast_add] using (width_add (lo:ℤ) hi).trans
          (Nat.add_le_add_right (max_le hlw hhw) 1)
      have hadd := (Index.add_bounded lo hi v hlw hhw).reprice_perform (karatsuba_le_schoolbook _)
      have hdiv := (Index.div_bounded (lo+hi) 2 (v+1) 2 hsumw (by decide)).reprice_perform
        (karatsuba_le_schoolbook _)
      have hmul (a b : I) (ha : width (toInt a) ≤ 2*(mid-lo)*w)
          (hb : width (toInt b) ≤ 2*(hi-mid)*w) :
          Bounded karatsuba (Python.Cost.Int.mul a b)
            (fun r => width (toInt r) ≤ 2*(hi-lo)*w) (8*3^d*work w) := by
        apply (mul_bounded a b _ _ ha hb).mono
        · intro r hr
          have he : (mid-lo)+(hi-mid)=hi-lo := by omega
          nlinarith only [hr, congrArg (fun q => 2*q*w) he]
        · have hcap : max (2*(mid-lo)*w) (2*(hi-mid)*w) ≤ (2*2^d)*w := by
            apply max_le <;> nlinarith only [Nat.mul_le_mul_right (2*w) hdl,
              Nat.mul_le_mul_right (2*w) hdr]
          have hc := (work_mono hcap).trans (work_mul_le (2*2^d) w)
          have he : work (2*2^d) = 3*3^d := by rw [← pow_succ',work_two_pow,pow_succ']
          rw [he] at hc
          have hb := Nat.mul_le_mul (show 2^d ≤ 3^d from Nat.pow_le_pow_left (by omega) d)
            (bits_le_work w)
          have hp : 1 ≤ 3^d*work w := Nat.succ_le_of_lt (by have := work_pos w; positivity)
          have hl := Nat.mul_le_mul_right (2*w) hdl
          have hr := Nat.mul_le_mul_right (2*w) hdr
          nlinarith only [hc,hb,hp,hl,hr]
      have h := hsub.bind fun _ _ => hle.bind fun _ _ => hadd.bind fun _ _ =>
        hdiv.bind fun _ _ => hleft.bind fun a ha => hright.bind fun b hb => hmul a b ha hb
      apply h.mono (fun _ hr => hr)
      have hnodes : (2*(mid-lo)-1)+(2*(hi-mid)-1)+1=2*(hi-lo)-1 := by omega
      have hnode := congrArg (fun q => 64*v^2*q) hnodes
      have hcontrol : (2*v+1)+(v+1)+(2*v+2)+(1+(v+1)*2+2*(v+1)+2) ≤ 64*v^2 := by nlinarith
      have hp : 0 ≤ 3^d*work w := Nat.zero_le _
      rw [pow_succ (3:ℕ) d]
      nlinarith only [hnode,hcontrol,hp]

/-- Complete generated tree, uniformly in the number and maximum width of its factors. -/
theorem balancedFactorsM_karatsuba_bounded (xs : Array I) (w v : ℕ)
    (hw : 1 ≤ w) (hv : 6 ≤ v) (hsize : width (xs.size:ℤ) ≤ v)
    (hx : ∀ x ∈ xs, width (toInt x) ≤ w) :
    Bounded karatsuba (balancedFactorsM (m := CostT Id) I xs)
      (fun r => width (toInt r) ≤ 2*(xs.size+1)*w)
      (200001*work xs.size*work w+128*v^2*(xs.size+1)) := by
  by_cases hz : xs.size = 0
  · have he := Array.eq_empty_of_size_eq_zero hz
    subst xs
    have hrun : RunsWith karatsuba (balancedFactorsM (m := CostT Id) I (#[]:Array I)) (1:I) 13 := by
      intro initial
      change CostT.run (balancedFactorsM.rec (m := CostT Id) I #[] 32 (by omega) 0 0)
        karatsuba (initial+1) = _
      rw [balancedFactorsM_rec_eq]
      simp only [Nat.sub_zero, Nat.zero_le, ↓reduceIte]
      rfl
    apply hrun.bounded
    · simp only [Array.size_empty, toInt_one]
      have : width (1:ℤ)=1 := by decide
      omega
    · have hp := work_pos w
      norm_num only [Array.size_empty, work, pow_zero, Nat.mul_one, Nat.one_mul, Nat.zero_add]
      change 13 ≤ 200001*work w+128*v^2
      nlinarith only [hp]
  · have hrec := rec_karatsuba_bounded I xs w v (Nat.clog 2 xs.size) hw hv hsize hx 0 xs.size
      (by omega) (le_refl _) (by simpa using Nat.le_pow_clog (by omega : 1 < 2) xs.size)
    have hlen : Bounded karatsuba (Sequence.length xs) (fun r => r = xs.size) 1 :=
      (RunsWith.perform _ _).bounded rfl (by rfl)
    have h := hlen.bind (next := fun _ => balancedFactorsM.rec I xs 32 (by omega) 0 xs.size)
      (fun _ _ => hrec)
    apply h.mono
    · intro r hr
      simp only [Nat.sub_zero] at hr
      exact hr.trans (Nat.mul_le_mul_right _ (by omega))
    · simp only [Nat.sub_zero]
      change 1+(200000*work xs.size*work w+64*v^2*(2*xs.size-1)) ≤ _
      have hn := Nat.mul_le_mul_left (64*v^2) (show 2*xs.size-1 ≤ 2*(xs.size+1) by omega)
      have hp : 1 ≤ work xs.size*work w := Nat.succ_le_of_lt (by have := work_pos xs.size; have := work_pos w; positivity)
      nlinarith only [hn,hp]

end SympyBinomial.PrimeExponent
