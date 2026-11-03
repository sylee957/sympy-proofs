module

public import SympyProofs.Sum.Gosper.Algorithm.Algorithm
public import SympyProofs.Sum.Gosper.Backend.Normalization
public import SympyProofs.Sum.Gosper.Normalization

/-! Ring-valued normalization preserves the ratio and removes all relevant shifts. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial

/-- Every component of the normalization state is nonzero. -/
def normalFormNonzero {R : Type*} [CommRing R] (s : R[X] × R[X] × R[X]) : Prop :=
  s.1 ≠ 0 ∧ s.2.1 ≠ 0 ∧ s.2.2 ≠ 0

/-- The normalized ratio identity and shift-coprimality over a field. -/
def normalFormValid {F : Type*} [Field F] (P Q : F[X]) (s : F[X] × F[X] × F[X]) : Prop :=
  normalFormNonzero s ∧ Gosper.ShiftCoprime s.1 s.2.1 ∧
    P * (s.2.1 * s.2.2) = Q * (s.1 * taylor 1 s.2.2)

variable {K R : Type} [CommRing K] [IsDomain K] [CommRing R] [Algebra K R]

/-- The imperative update multiplies the shifts from `-1` through `-j`. -/
private theorem normalization_product_loop (c d : R[X]) (j : ℕ) :
    (forIn [:j] c (fun (k : ℕ) c => pure (ForInStep.yield
      (c * taylor (-((k : R) + 1)) d))) : Id R[X]) =
      pure (c * taylor (-1) (Gosper.shiftProduct d j)) := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range', List.forIn_pure_yield_eq_foldl]
  change (List.range j).foldl (fun c (k : ℕ) => c * taylor (-((k : R) + 1)) d) c =
    c * taylor (-1) (Gosper.shiftProduct d j)
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      Gosper.shiftProduct_succ, taylor_mul, taylor_taylor]
    simp only [mul_assoc, neg_add_rev]

/-- Exact cancellation preserves the ratio without any division by coefficients. -/
private theorem normalization_factor_step [IsDomain R] (P Q : R[X]) (s : R[X] × R[X] × R[X])
    (hs : normalFormNonzero s)
    (he : P * (s.2.1 * s.2.2) = Q * (s.1 * taylor 1 s.2.2))
    (j : ℕ) (d a q : R[X]) (ha : s.1 = d * a) (hq : taylor (j : R) s.2.1 = d * q) :
    let b := taylor (-(j : R)) q
    let t : R[X] × R[X] × R[X] :=
      (a, b, s.2.2 * taylor (-1) (Gosper.shiftProduct d j))
    normalFormNonzero t ∧ P * (t.2.1 * t.2.2) = Q * (t.1 * taylor 1 t.2.2) := by
  let b := taylor (-(j : R)) q
  let T := taylor (-1) (Gosper.shiftProduct d j)
  have hd : d ≠ 0 := by intro hz; apply hs.1; simpa [hz] using ha
  have ha0 : a ≠ 0 := by intro hz; apply hs.1; simpa [hz] using ha
  have hq0 : q ≠ 0 := by
    intro hz
    have ht : taylor (j : R) s.2.1 = 0 := by simpa [hz] using hq
    exact hs.2.1 ((taylor_eq_zero _ _).mp ht)
  have hb : s.2.1 = taylor (-(j : R)) d * b := by
    have h := congrArg (taylor (-(j : R))) hq
    simpa [b, taylor_mul, taylor_taylor] using h
  refine ⟨⟨ha0, (taylor_eq_zero _ _).not.mpr hq0,
    mul_ne_zero hs.2.2 ((taylor_eq_zero _ _).not.mpr (Gosper.shiftProduct_ne_zero _ hd j))⟩, ?_⟩
  have hdj : taylor (-(j : R)) d ≠ 0 := (taylor_eq_zero _ _).not.mpr hd
  have ht : T * d = taylor (-(j : R)) d * taylor 1 T := by
    simpa [T, taylor_taylor, mul_comm] using (Gosper.shiftProduct_identity d j).symm
  rw [ha, hb] at he
  change P * (b * (s.2.2 * T)) = Q * (a * taylor 1 (s.2.2 * T))
  apply mul_left_cancel₀ hdj
  rw [taylor_mul]
  linear_combination T * he + (Q * a * taylor 1 s.2.2) * ht

/-- A gcd update preserves the ring identity, clears its selected shift in the fraction
field, and preserves every previously established coprimality condition. -/
theorem normalization_step_spec [IsDomain R] (backend : TermBackend K R) (hbackend : backend.Valid)
    (P Q : R[X]) (s : R[X] × R[X] × R[X]) (hs : normalFormNonzero s)
    (he : P * (s.2.1 * s.2.2) = Q * (s.1 * taylor 1 s.2.2)) (j : ℕ) :
    let d := backend.gcd s.1 (taylor (j : R) s.2.1)
    let t : R[X] × R[X] × R[X] :=
      (backend.exactDiv s.1 d,
        taylor (-(j : R)) (backend.exactDiv (taylor (j : R) s.2.1) d),
        s.2.2 * taylor (-1) (Gosper.shiftProduct d j))
    let ι := algebraMap R (FractionRing R)
    normalFormNonzero t ∧ P * (t.2.1 * t.2.2) = Q * (t.1 * taylor 1 t.2.2) ∧
      IsCoprime (t.1.map ι) (taylor (j : FractionRing R) (t.2.1.map ι)) ∧
      ∀ k : ℕ, IsCoprime (s.1.map ι) (taylor (k : FractionRing R) (s.2.1.map ι)) →
        IsCoprime (t.1.map ι) (taylor (k : FractionRing R) (t.2.1.map ι)) := by
  let d := backend.gcd s.1 (taylor (j : R) s.2.1)
  let a := backend.exactDiv s.1 d
  let q := backend.exactDiv (taylor (j : R) s.2.1) d
  let b := taylor (-(j : R)) q
  let ι := algebraMap R (FractionRing R)
  have hd : d ≠ 0 := backend.gcd_ne_zero hbackend _ _ hs.1
  have ha : s.1 = d * a :=
    (hbackend.exactDiv_mul _ _ hd (hbackend.gcd_dvd_left _ _)).symm
  have hq : taylor (j : R) s.2.1 = d * q :=
    (hbackend.exactDiv_mul _ _ hd (hbackend.gcd_dvd_right _ _)).symm
  have hB : taylor (j : R) s.2.1 ≠ 0 := (taylor_eq_zero _ _).not.mpr hs.2.1
  have hb : s.2.1 = taylor (-(j : R)) d * b := by
    have h := congrArg (taylor (-(j : R))) hq
    simpa [b, taylor_mul, taylor_taylor] using h
  have hf := normalization_factor_step P Q s hs he j d a q ha hq
  refine ⟨hf.1, hf.2, ?_, ?_⟩
  · have hc := backend.exactDiv_gcd_isCoprime hbackend s.1 (taylor (j : R) s.2.1) hs.1 hB
    simpa [Polynomial.map_taylor, taylor_taylor] using hc
  · intro k hk
    have hda : a ∣ s.1 := ⟨_, by rw [ha]; ring⟩
    have hdb : b ∣ s.2.1 := ⟨_, by rw [hb]; ring⟩
    apply IsCoprime.mono ((Polynomial.mapRingHom ι).map_dvd hda)
      ((taylorAlgHom (k : FractionRing R)).toRingHom.map_dvd
        ((Polynomial.mapRingHom ι).map_dvd hdb)) hk

/-- The loop invariant combines the raw ring ratio with coprimality in the fraction field. -/
theorem normalization_foldl_spec (P Q : R[X])
    (step : (R[X] × R[X] × R[X]) → ℕ → (R[X] × R[X] × R[X]))
    (hstep : ∀ s, normalFormNonzero s →
      P * (s.2.1 * s.2.2) = Q * (s.1 * taylor 1 s.2.2) → ∀ j,
      normalFormNonzero (step s j) ∧
        P * ((step s j).2.1 * (step s j).2.2) = Q * ((step s j).1 * taylor 1 (step s j).2.2) ∧
        IsCoprime ((step s j).1.map (algebraMap R (FractionRing R)))
          (taylor (j : FractionRing R) ((step s j).2.1.map (algebraMap R (FractionRing R)))) ∧
        ∀ k : ℕ, IsCoprime (s.1.map (algebraMap R (FractionRing R)))
          (taylor (k : FractionRing R) (s.2.1.map (algebraMap R (FractionRing R)))) →
          IsCoprime ((step s j).1.map (algebraMap R (FractionRing R)))
            (taylor (k : FractionRing R) ((step s j).2.1.map (algebraMap R (FractionRing R)))))
    (s : R[X] × R[X] × R[X]) (roots : List ℕ) (hs : normalFormNonzero s)
    (he : P * (s.2.1 * s.2.2) = Q * (s.1 * taylor 1 s.2.2)) :
    let t := roots.foldl step s
    let ι := algebraMap R (FractionRing R)
    normalFormNonzero t ∧ P * (t.2.1 * t.2.2) = Q * (t.1 * taylor 1 t.2.2) ∧
      ∀ j, j ∈ roots ∨ IsCoprime (s.1.map ι) (taylor (j : FractionRing R) (s.2.1.map ι)) →
        IsCoprime (t.1.map ι) (taylor (j : FractionRing R) (t.2.1.map ι)) := by
  induction roots generalizing s with
  | nil => exact ⟨hs, he, fun j hj => hj.resolve_left List.not_mem_nil⟩
  | cons j roots ih =>
    have h := hstep s hs he j
    obtain ⟨hn, hr, hc⟩ := ih (step s j) h.1 h.2.1
    refine ⟨hn, hr, ?_⟩
    intro k hk
    apply hc k
    rcases hk with hk | hk
    · rcases List.mem_cons.mp hk with rfl | hk
      · exact Or.inr h.2.2.1
      · exact Or.inl hk
    · exact Or.inr (h.2.2.2 k hk)

variable [IsDomain R]

/-- The completed loop keeps its exact ring identity and clears every nonnegative shift. -/
theorem gosperNormal_invariants (backend : TermBackend K R) (hbackend : backend.Valid)
    (P Q : R[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (s : R[X] × R[X] × R[X])
    (h : gosperNormal backend P Q = s) :
    normalFormNonzero s ∧ P * (s.2.1 * s.2.2) = Q * (s.1 * taylor 1 s.2.2) ∧
      Gosper.ShiftCoprime (s.1.map (algebraMap R (FractionRing R)))
        (s.2.1.map (algebraMap R (FractionRing R))) := by
  let initial : R[X] × R[X] × R[X] := (P, Q, 1)
  let step (s : R[X] × R[X] × R[X]) (j : ℕ) : R[X] × R[X] × R[X] :=
    let d := backend.gcd s.1 (taylor (j : R) s.2.1)
    (backend.exactDiv s.1 d,
      taylor (-(j : R)) (backend.exactDiv (taylor (j : R) s.2.1) d),
      s.2.2 * taylor (-1) (Gosper.shiftProduct d j))
  let resultant := backend.resultant (P.map (Polynomial.C : R →+* R[X]))
    (taylor (X : R[X]) (Q.map (Polynomial.C : R →+* R[X])))
  let shifts := backend.naturalRoots resultant
  let roots := (insert 0 shifts).sort (· ≤ ·)
  have hs := normalization_foldl_spec P Q step
    (normalization_step_spec backend hbackend P Q) initial roots
    ⟨hP, hQ, one_ne_zero⟩ (by simp [initial]; ring)
  have he : roots.foldl step initial = s := by
    simp only [gosperNormal, normalization_product_loop] at h
    simpa [roots, shifts, resultant, step, initial] using h
  rw [he] at hs
  refine ⟨hs.1, hs.2.1, ?_⟩
  intro j
  apply hs.2.2 j
  by_cases hj : j ∈ shifts
  · exact Or.inl (by simp [roots, hj])
  · right
    by_contra hn
    exact hj ((backend.mem_naturalRoots_shiftResultant hbackend P Q hP hQ j).mpr hn)

/-- Normalization preserves the ratio and nonzero components over the input ring itself. -/
theorem gosperNormal_sound (backend : TermBackend K R) (hbackend : backend.Valid)
    (P Q : R[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (s : R[X] × R[X] × R[X])
    (h : gosperNormal backend P Q = s) :
    normalFormNonzero s ∧ P * (s.2.1 * s.2.2) = Q * (s.1 * taylor 1 s.2.2) := by
  have hs := gosperNormal_invariants backend hbackend P Q hP hQ s h
  exact ⟨hs.1, hs.2.1⟩

/-- The ring-valued output satisfies the usual field normal-form specification after
its coefficients are embedded into the fraction field. -/
theorem gosperNormal_spec (backend : TermBackend K R) (hbackend : backend.Valid)
    (P Q : R[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (s : R[X] × R[X] × R[X])
    (h : gosperNormal backend P Q = s) :
    let ι := algebraMap R (FractionRing R)
    normalFormValid (P.map ι) (Q.map ι) (s.1.map ι, s.2.1.map ι, s.2.2.map ι) := by
  have hs := gosperNormal_invariants backend hbackend P Q hP hQ s h
  have hi := IsFractionRing.injective R (FractionRing R)
  refine ⟨⟨(Polynomial.map_ne_zero_iff hi).mpr hs.1.1,
    (Polynomial.map_ne_zero_iff hi).mpr hs.1.2.1,
    (Polynomial.map_ne_zero_iff hi).mpr hs.1.2.2⟩, hs.2.2, ?_⟩
  have he := congrArg (Polynomial.map (algebraMap R (FractionRing R))) hs.2.1
  simpa using he

/-- Nonzero ring inputs always produce a valid normal form in their fraction field. -/
theorem gosperNormal_exists (backend : TermBackend K R) (hbackend : backend.Valid)
    (P Q : R[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    ∃ s, gosperNormal backend P Q = s ∧
      normalFormValid (P.map (algebraMap R (FractionRing R)))
        (Q.map (algebraMap R (FractionRing R)))
        (s.1.map (algebraMap R (FractionRing R)),
          s.2.1.map (algebraMap R (FractionRing R)),
          s.2.2.map (algebraMap R (FractionRing R))) :=
  ⟨gosperNormal backend P Q, rfl, gosperNormal_spec backend hbackend P Q hP hQ _ rfl⟩

end Gosper.Algorithm
