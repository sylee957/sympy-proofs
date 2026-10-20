module

public import SympyProofs.Binomial.Costs.PrimeExponent
public import SympyProofs.Python.Cost.SequenceBounds
public import SympyProofs.Python.Cost.IndexBounds
/-!
# Bounds for the executed balanced product

The quadratic potential pays for multiplication across every split. The second
term pays for storage-index arithmetic at all tree nodes. These contracts refer
to `balancedFactorsM` itself, including leaf slices and loop control.
-/

@[expose] public section

open PythonInt Python.Cost Python.Cost.Models
namespace SympyBinomial.PrimeExponent
variable (I : Type) [PythonInt I]
private theorem bits_ge_size (xs : Array I) : xs.size ≤ Sequence.inputBits xs := by
  have h := List.sum_le_sum (l := xs.toList) (f := fun _ => 1)
    (g := fun x => width (toInt x)) (fun x _ => one_le_width (toInt x))
  simpa [Sequence.inputBits] using h
private theorem bits_split (xs : Array I) (lo mid hi : ℕ) (hl : lo ≤ mid) (hh : mid ≤ hi) :
    Sequence.inputBits (xs.extract lo mid) + Sequence.inputBits (xs.extract mid hi) =
      Sequence.inputBits (xs.extract lo hi) := by
  unfold Sequence.inputBits
  rw [← List.sum_append, ← List.map_append, ← Array.toList_append,
    Array.extract_append_extract, Nat.min_eq_left hl, Nat.max_eq_right hh]

omit [PythonInt I] in
private theorem slice_bound (xs : Array I) (lo hi : ℕ) :
    Bounded schoolbook (Sequence.slice xs lo hi) (fun r => r = xs.extract lo hi)
      (1 + 2*(xs.extract lo hi).size) := by
  exact (RunsWith.perform _ _).bounded (post := fun r => r = xs.extract lo hi) rfl (by simp [schoolbook]; omega)

private theorem rec_bounded (xs : Array I) (lo hi w : ℕ)
    (hlo : lo < hi) (hhi : hi ≤ xs.size) (hw : 6 ≤ w)
    (hsize : width (xs.size : ℤ) ≤ w) :
    Bounded schoolbook (balancedFactorsM.rec (m := CostT Id) I xs 32 (by omega) lo hi)
      (fun r => width (toInt r) ≤ 2 * Sequence.inputBits (xs.extract lo hi))
      (16 * Sequence.inputBits (xs.extract lo hi)^2 + 64*w^2*(2*(hi-lo)-1)) := by
  let S := Sequence.inputBits (xs.extract lo hi)
  have hspan : (xs.extract lo hi).size = hi-lo := by simp [Nat.min_eq_left hhi]
  have hS : 1 ≤ S := by have := bits_ge_size I (xs.extract lo hi); omega
  have hlow : width (lo : ℤ) ≤ w := (width_mono (by simp; omega)).trans hsize
  have hhigh : width (hi : ℤ) ≤ w := (width_mono (by simpa using hhi)).trans hsize
  have hcount : width ((hi-lo : ℕ) : ℤ) ≤ w :=
    (width_mono (by simpa only [Int.natAbs_natCast] using Nat.sub_le hi lo)).trans hhigh
  have h32 : width (32 : ℤ) ≤ w := by
    have he : width (32 : ℤ) = 6 := by decide
    omega
  have hsub := Index.sub_bounded hi lo w hhigh hlow
  have hle := Index.le_bounded (hi-lo) 32 w hcount h32
  rw [balancedFactorsM_rec_eq]
  by_cases hcut : hi-lo ≤ 32
  · simp only [hcut, ↓reduceIte]
    have hleaf := (slice_bound I xs lo hi).bind (fun ys hys => by
      subst ys
      exact Sequence.prod_bounded (xs.extract lo hi))
    refine Bounded.mono (post := fun r => width (toInt r) ≤ 1+S)
      (budget := (2*w+1)+((w+1)+((1+2*(xs.extract lo hi).size)+(S+2)^2))) ?_ ?_ ?_
    · apply hsub.bind
      intro _ _
      apply hle.bind
      intro _ _
      exact hleaf
    · intro r hr
      dsimp only [S] at hS
      omega
    · rw [hspan]
      have hsquare : (S+2)^2 ≤ 9*S^2 := by nlinarith
      have hnodes : 1 ≤ 2*(hi-lo)-1 := by omega
      have hp := Nat.mul_le_mul_left (64*w^2) hnodes
      nlinarith [Nat.zero_le (S*S)]
  · simp only [hcut, ↓reduceIte]
    let mid := (lo+hi)/2
    have hml : lo < mid := by dsimp [mid]; omega
    have hmh : mid < hi := by dsimp [mid]; omega
    have hsumw : width ((lo+hi : ℕ) : ℤ) ≤ w+1 := by
      simpa only [Nat.cast_add] using (width_add (lo : ℤ) hi).trans
        (Nat.add_le_add_right (max_le hlow hhigh) 1)
    have h2 : width (2 : ℤ) ≤ 2 := by decide
    have hadd := Index.add_bounded lo hi w hlow hhigh
    have hdiv := Index.div_bounded (lo+hi) 2 (w+1) 2 hsumw h2
    have hl := rec_bounded xs lo mid w hml (by omega) hw hsize
    have hr := rec_bounded xs mid hi w hmh hhi hw hsize
    let L := Sequence.inputBits (xs.extract lo mid)
    let R := Sequence.inputBits (xs.extract mid hi)
    have hL : 1 ≤ L := by
      have h := bits_ge_size I (xs.extract lo mid)
      simp only [Array.size_extract, Nat.min_eq_left (show mid ≤ xs.size by omega)] at h
      omega
    have hR : 1 ≤ R := by
      have h := bits_ge_size I (xs.extract mid hi)
      simp only [Array.size_extract, Nat.min_eq_left hhi] at h
      omega
    have hLR : L+R = S := bits_split I xs lo mid hi (by omega) (by omega)
    have hmul (a b : I) (ha : width (toInt a) ≤ 2*L) (hb : width (toInt b) ≤ 2*R) :
        Bounded schoolbook (Python.Cost.Int.mul a b) (fun r => width (toInt r) ≤ 2*S)
          (9*L*R) := by
      have h := (Sized.value a ha).mul (Sized.value b hb)
      apply Bounded.mono h
      · intro r hr
        change width (toInt r) ≤ 2*L+2*R at hr
        omega
      · have h₁ := Nat.mul_le_mul_left L hR
        have h₂ := Nat.mul_le_mul_right R hL
        have h₃ : 1 ≤ L*R := by nlinarith
        nlinarith
    refine Bounded.mono (post := fun r => width (toInt r) ≤ 2*S)
      (budget := (2*w+1)+((w+1)+((2*w+2)+((1+(w+1)*2+2*(w+1)+2)+
        (16*L^2+64*w^2*(2*(mid-lo)-1)+(16*R^2+64*w^2*(2*(hi-mid)-1)+9*L*R))))))
      ?_ (fun _ hr => hr) ?_
    · apply hsub.bind
      intro _ _
      apply hle.bind
      intro _ _
      apply hadd.bind
      intro _ _
      apply hdiv.bind
      intro _ _
      exact hl.bind (fun a ha => hr.bind (fun b hb => hmul a b ha hb))
    have hlen : (2*(mid-lo)-1)+(2*(hi-mid)-1)+1 = 2*(hi-lo)-1 := by omega
    have hwidth : (2*w+1)+(w+1)+(2*w+2)+(1+(w+1)*2+2*(w+1)+2) ≤ 64*w^2 := by nlinarith
    have hcross : 16*L^2+16*R^2+9*L*R ≤ 16*S^2 := by
      rw [← hLR]
      nlinarith only [Nat.zero_le (L*R)]
    have hnodes := congrArg (fun x => 64*w^2*x) hlen
    simp only [Nat.mul_add, Nat.mul_one] at hnodes
    nlinarith only [hcross, hwidth, hnodes]
termination_by hi-lo
decreasing_by all_goals omega

/-- The complete costed product tree has a quadratic bit budget plus its index work. -/
theorem balancedFactorsM_bounded (xs : Array I) (w : ℕ) (hw : 6 ≤ w)
    (hsize : width (xs.size : ℤ) ≤ w) :
    Bounded schoolbook (balancedFactorsM (m := CostT Id) I xs)
      (fun r => width (toInt r) ≤ 2*(Sequence.inputBits xs + 1))
      (16*(Sequence.inputBits xs + 1)^2 + 128*w^2*(xs.size+1)) := by
  by_cases hzero : xs.size = 0
  · have he : xs = #[] := Array.eq_empty_of_size_eq_zero hzero
    subst xs
    have hrun : RunsWith schoolbook (balancedFactorsM (m := CostT Id) I (#[] : Array I))
        (1 : I) 13 := by
      intro initial
      change CostT.run (balancedFactorsM.rec (m := CostT Id) I #[] 32 (by omega) 0 0)
        schoolbook (initial + 1) = _
      rw [balancedFactorsM_rec_eq]
      simp only [Nat.sub_zero, Nat.zero_le, ↓reduceIte]
      rfl
    apply hrun.bounded
    · simp [toInt_one, width, Sequence.inputBits]
    · simp only [Sequence.inputBits, List.map_nil, List.sum_nil,
        Array.size_empty]
      nlinarith
  · have hr := rec_bounded I xs 0 xs.size w (by omega) (le_refl _) hw hsize
    have hlen : Bounded schoolbook (Sequence.length xs) (fun r => r = xs.size) 1 :=
      (RunsWith.perform _ xs.size).bounded (post := fun r => r = xs.size) rfl (by rfl)
    have h := hlen.bind (next := fun _ => balancedFactorsM.rec I xs 32 (by omega) 0 xs.size)
      (fun _ _ => hr)
    apply h.mono
    · intro r hr
      simpa using hr.trans (show 2*Sequence.inputBits (xs.extract 0 xs.size) ≤
        2*(Sequence.inputBits xs+1) by simp)
    · simp only [Array.extract_size, Nat.sub_zero]
      have hnodes : 2*xs.size-1 ≤ 2*(xs.size+1) := by omega
      have hmul := Nat.mul_le_mul_left (64*w^2) hnodes
      nlinarith only [hmul, Nat.zero_le (Sequence.inputBits xs)]

/-- Asymptotics of the executed tree, uniformly for arbitrary factor arrays. -/
theorem balancedFactorsM_isBigO {X : Type} (l : Filter X) (xs : X → Array I) :
    (fun x => ((CostT.run (balancedFactorsM (m := CostT Id) I (xs x)) schoolbook).2 : ℝ)) =O[l]
      (fun x => (((Sequence.inputBits (xs x)+1)^2 +
        (max 6 (width ((xs x).size : ℤ)))^2*((xs x).size+1) : ℕ) : ℝ)) := by
  apply nat_isBigO_of_le_mul 128
  intro x
  have h := (balancedFactorsM_bounded I (xs x) (max 6 (width ((xs x).size : ℤ)))
    (le_max_left _ _) (le_max_right _ _)).cost_le
  nlinarith only [h, Nat.zero_le ((Sequence.inputBits (xs x)+1)^2)]

end SympyBinomial.PrimeExponent
