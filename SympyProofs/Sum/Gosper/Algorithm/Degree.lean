module

public import SympyProofs.Sum.Gosper.Algorithm.Algorithm
public import SympyProofs.Sum.Gosper.Degree

/-! Correctness of the signed degree bound computed from integral-domain coefficients. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial

variable {K W : Type*} [CommRing K] [IsDomain K] [DecidableEq K]
variable [CommRing W] [IsDomain W]

/-- Equal right-hand-side degrees give the same signed solution bound,
independently of the coefficients and their coefficient ring. -/
theorem degreeBound_rhs_eq (backend : TermBackend K W)
    {R S : Type*} [Semiring R] [Semiring S]
    (A B : K[X]) (C : R[X]) (D : S[X]) (hdegree : C.natDegree = D.natDegree) :
    degreeBound backend A B C = degreeBound backend A B D := by
  simp only [degreeBound, hdegree]

/-- Increasing the right-hand-side degree cannot decrease the solution bound. -/
theorem degreeBound_mono (backend : TermBackend K W)
    {R S : Type*} [Semiring R] [Semiring S]
    (A B : K[X]) (C : R[X]) (D : S[X]) (hdegree : C.natDegree ≤ D.natDegree) :
    degreeBound backend A B C ≤ degreeBound backend A B D := by
  simp only [degreeBound, Id.run, pure]
  split_ifs <;> try omega
  split <;> omega

omit [IsDomain K] [DecidableEq K] in
private theorem top_coeff_ne_zero (A B : K[X])
    (hl : max A.natDegree B.natDegree ≠ 0)
    (hc : A.coeff (max A.natDegree B.natDegree) =
      B.coeff (max A.natDegree B.natDegree)) :
    B.coeff (max A.natDegree B.natDegree) ≠ 0 := by
  intro hb
  rcases max_choice A.natDegree B.natDegree with h | h
  · have hA : A = 0 := leadingCoeff_eq_zero.mp (by simpa [h] using hc.trans hb)
    exact hl (by simpa [hA] using h)
  · have hB : B = 0 := leadingCoeff_eq_zero.mp (by simpa [h] using hb)
    exact hl (by simpa [hB] using h)

variable [Algebra K W]

omit [DecidableEq K] in
/-- Integer-ratio recognition agrees with division after an injective map into a field. -/
private theorem integerRatio_eq_div (backend : TermBackend K W) (hbackend : backend.Valid)
    {L : Type*} [Field L] (f : K →+* L) (hf : Function.Injective f)
    (a b : K) (hb : b ≠ 0) (z : ℤ) :
    backend.integerRatio a b = some z ↔ (z : L) = f a / f b := by
  have hb' : f b ≠ 0 := fun hz => hb ((map_eq_zero_iff f hf).mp hz)
  rw [hbackend.integerRatio_eq_some a b hb z, eq_div_iff hb']
  constructor
  · intro h
    simpa only [map_mul, map_intCast] using (congrArg f h).symm
  · intro h
    apply hf
    simpa only [map_mul, map_intCast] using h.symm

variable [CharZero K] {L : Type*} [Field L] [Algebra K L]

/-- The domain computation agrees with the paper's bound in every faithful field target. -/
theorem degreeBound_eq_paper_map (backend : TermBackend K W) (hbackend : backend.Valid)
    (A B : K[X]) (C : L[X]) (hKL : Function.Injective (algebraMap K L)) :
    degreeBound backend A B C =
      Gosper.paperDegreeBound C (A.map (algebraMap K L)) (B.map (algebraMap K L)) := by
  classical
  let : CharZero L := charZero_of_injective_algebraMap hKL
  let l := max A.natDegree B.natDegree
  have hne (a b : K) : algebraMap K L a ≠ algebraMap K L b ↔ a ≠ b :=
    not_congr hKL.eq_iff
  simp only [degreeBound, Id.run, pure, Gosper.paperDegreeBound,
    Polynomial.natDegree_map_eq_of_injective hKL, coeff_map, hne]
  split_ifs with hc hl
  · rfl
  · rfl
  have hb : B.coeff l ≠ 0 := top_coeff_ne_zero A B hl (not_ne_iff.mp hc)
  have hratio (z : ℤ) :
      backend.integerRatio (B.coeff (l - 1) - A.coeff (l - 1)) (B.coeff l) = some z ↔
        (z : L) = Gosper.exceptionalDegree
          (A.map (algebraMap K L)) (B.map (algebraMap K L)) l := by
    simpa only [Gosper.exceptionalDegree, coeff_map, map_sub] using
      integerRatio_eq_div backend hbackend (algebraMap K L) hKL
        (B.coeff (l - 1) - A.coeff (l - 1)) (B.coeff l) hb z
  change (match backend.integerRatio (B.coeff (l - 1) - A.coeff (l - 1)) (B.coeff l) with
    | some z => max z ((C.natDegree : ℤ) - l + 1)
    | _ => (C.natDegree : ℤ) - l + 1) =
      Gosper.caseTwoDegreeBound C (A.map (algebraMap K L)) (B.map (algebraMap K L)) l
  cases hr : backend.integerRatio (B.coeff (l - 1) - A.coeff (l - 1)) (B.coeff l) with
  | none =>
    apply (Gosper.caseTwoDegreeBound_of_not_integer C _ _ l ?_).symm
    rintro ⟨z, hz⟩
    have h := (hratio z).mpr hz
    rw [hr] at h
    contradiction
  | some z =>
    exact (Gosper.caseTwoDegreeBound_of_integer C _ _ l z ((hratio z).mp hr)).symm

/-- A bound computed in the domain applies to solutions in a faithful field target. -/
theorem solution_degree_le_extension (backend : TermBackend K W) (hbackend : backend.Valid)
    (A B : K[X]) (C x : L[X]) (hKL : Function.Injective (algebraMap K L))
    (hA : A ≠ 0) (hB : B ≠ 0) (hx : x ≠ 0)
    (he : A.map (algebraMap K L) * taylor 1 x - B.map (algebraMap K L) * x = C) :
    (x.natDegree : ℤ) ≤ degreeBound backend A B C := by
  let : CharZero L := charZero_of_injective_algebraMap hKL
  rw [degreeBound_eq_paper_map backend hbackend A B C hKL]
  have ht : taylor (1 : L) x ≠ 0 := (taylor_eq_zero _ _).not.mpr hx
  have he' : A.map (algebraMap K L) * taylor 1 x -
      B.map (algebraMap K L) * taylor (-1) (taylor 1 x) = C := by
    simpa [taylor_taylor] using he
  simpa using Gosper.solution_intDegree_le C
    (A.map (algebraMap K L)) (B.map (algebraMap K L)) (taylor 1 x)
    ((Polynomial.map_ne_zero_iff hKL).mpr hA) ((Polynomial.map_ne_zero_iff hKL).mpr hB) ht he'

/-- The source degree remains a valid bound when evaluation lowers the right-hand-side degree. -/
theorem solution_degree_le_extension_bounded (backend : TermBackend K W)
    (hbackend : backend.Valid) {R : Type*} [Semiring R]
    (A B : K[X]) (C₀ : R[X]) (C x : L[X]) (hKL : Function.Injective (algebraMap K L))
    (hdegree : C.natDegree ≤ C₀.natDegree) (hA : A ≠ 0) (hB : B ≠ 0) (hx : x ≠ 0)
    (he : A.map (algebraMap K L) * taylor 1 x - B.map (algebraMap K L) * x = C) :
    (x.natDegree : ℤ) ≤ degreeBound backend A B C₀ :=
  (solution_degree_le_extension backend hbackend A B C x hKL hA hB hx he).trans
    (degreeBound_mono backend A B C C₀ hdegree)

end Gosper.Algorithm
