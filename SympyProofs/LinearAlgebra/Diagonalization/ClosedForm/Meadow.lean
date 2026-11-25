module

public import SympyProofs.LinearAlgebra.Diagonalization.ClosedForm.Interpolation

/-! # Certifying a direct diagonalization with total division -/

@[expose] public section

noncomputable section
namespace SympyProofs.Diagonalization.Meadow
open Matrix
variable {K : Type*} [Field K] {n : ℕ}

export SympyProofs.Diagonalization (isDiagonalization_iff)

/-- An invertible intertwining pair passes through. All other pairs give zero. -/
def certify (A : Matrix (Fin n) (Fin n) K) (raw : Matrix (Fin n) (Fin n) K × (Fin n → K)) :
    Matrix (Fin n) (Fin n) K × (Fin n → K) :=
  let (P, d) := raw
  let B := A * P - P * diagonal d
  (P.det / P.det * ∏ i, ∏ j, (1 - B i j / B i j)) • (P, d)

open Classical in
theorem certify_eq (A P : Matrix (Fin n) (Fin n) K) (d : Fin n → K) :
    certify A (P, d) = if IsDiagonalization A P d then (P, d) else 0 := by
  classical
  have scalar (x : K) : x / x = if x = 0 then 0 else 1 := by by_cases h : x = 0 <;> simp [h]
  have zeroTest (x : K) : 1 - x / x = if x = 0 then 1 else 0 := by by_cases h : x = 0 <;> simp [h]
  let B := A * P - P * diagonal d
  have hB : (∀ i j, B i j = 0) ↔ A * P = P * diagonal d :=
    ⟨fun h => sub_eq_zero.mp (Matrix.ext h : B = 0),
      fun h i j => by simp [B, h]⟩
  change (P.det / P.det * ∏ i, ∏ j, (1 - B i j / B i j)) • _ = _
  simp only [zeroTest]
  by_cases he : A * P = P * diagonal d
  · simp [hB.mpr he, he, isDiagonalization_iff, scalar]
  · have hf := mt hB.mp he
    push Not at hf
    obtain ⟨i, j, hij⟩ := hf
    have hi : (∏ j, if B i j = 0 then (1 : K) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hij])
    have hall : (∏ i, ∏ j, if B i j = 0 then (1 : K) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hi
    simp [hall, isDiagonalization_iff, he]

def asOption [DecidableEq K] (pair : Matrix (Fin n) (Fin n) K × (Fin n → K)) :=
  if pair.1.det = 0 then none else some pair

section
variable [NeZero n] [DecidableEq K]

theorem asOption_getD (A : Matrix (Fin n) (Fin n) K)
    (raw : Matrix (Fin n) (Fin n) K × (Fin n → K)) :
    (asOption (certify A raw)).getD 0 = certify A raw := by
  obtain ⟨P, d⟩ := raw
  rw [certify_eq]
  split_ifs with h
  · simp [asOption, h.1]
  · simp [asOption]

theorem asOption_sound {A P : Matrix (Fin n) (Fin n) K} {d : Fin n → K}
    {raw : Matrix (Fin n) (Fin n) K × (Fin n → K)}
    (h : asOption (certify A raw) = some (P, d)) : IsDiagonalization A P d := by
  obtain ⟨Q, e⟩ := raw
  rw [certify_eq] at h
  split_ifs at h with hQ
  · simp [asOption, hQ.1] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hQ
  · simp [asOption] at h

theorem asOption_isSome {A : Matrix (Fin n) (Fin n) K}
    {raw : Matrix (Fin n) (Fin n) K × (Fin n → K)}
    (complete : (∃ P d, IsDiagonalization A P d) → IsDiagonalization A raw.1 raw.2) :
    (asOption (certify A raw)).isSome ↔ ∃ P d, IsDiagonalization A P d := by
  obtain ⟨P, d⟩ := raw
  rw [certify_eq]
  split_ifs with h
  · simp [asOption, h.1, show ∃ Q e, IsDiagonalization A Q e from ⟨P, d, h⟩]
  · simp [asOption]
    exact fun Q e he => h (complete ⟨Q, e, he⟩)

end

theorem certify_correct {A : Matrix (Fin n) (Fin n) K}
    {raw : Matrix (Fin n) (Fin n) K × (Fin n → K)}
    (h : IsDiagonalization A raw.1 raw.2) :
    IsDiagonalization A (certify A raw).1 (certify A raw).2 := by
  obtain ⟨P, d⟩ := raw
  simp [certify_eq, h]

theorem certify_eq_zero {A : Matrix (Fin n) (Fin n) K}
    (raw : Matrix (Fin n) (Fin n) K × (Fin n → K))
    (h : ¬ ∃ P d, IsDiagonalization A P d) : certify A raw = 0 := by
  obtain ⟨P, d⟩ := raw
  simp [certify_eq, show ¬ IsDiagonalization A P d from fun hd => h ⟨P, d, hd⟩]

theorem charpoly_eq {A P : Matrix (Fin n) (Fin n) K} {d : Fin n → K} (h : IsDiagonalization A P d) :
    A.charpoly = (diagonal d).charpoly := by
  rw [h.2]
  exact Matrix.charpoly_units_conj (P.nonsingInvUnit (isUnit_iff_ne_zero.mpr h.1)) _

end SympyProofs.Diagonalization.Meadow
