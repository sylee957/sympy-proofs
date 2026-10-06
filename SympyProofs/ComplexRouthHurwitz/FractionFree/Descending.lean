import SympyProofs.ComplexRouthHurwitz.FractionFree.Invariant
import SympyProofs.ComplexRouthHurwitz.FractionFree.Integrality

/-! Relate ascending coefficient vectors to the descending subresultant invariant. -/
namespace RouthHurwitz.ComplexRouth.FractionFree
open Polynomial
noncomputable section
open Classical

def descending {K : Type*} [Zero K] (a : ℕ → K) (d j : ℕ) : K :=
  if j ≤ d then a (d-j) else 0

@[simp] theorem descending_zero {K : Type*} [Zero K] (a : ℕ → K) (d : ℕ) :
    descending a d 0 = a d := by simp [descending]

@[simp] theorem descending_scale {N} (a : Coefficients.Row N) (c : ℂ) (d j : ℕ) :
    descending (Coefficients.entry (Coefficients.scale c a)) d j =
      c*descending (Coefficients.entry a) d j := by
  simp only [descending, Coefficients.entry, Coefficients.scale]
  split_ifs <;> simp

theorem entry_nextLower {N} (d : ℕ) (D : ℝ) (u v : Coefficients.Row N) (j : ℕ) (hj : j < N) :
    Coefficients.entry (nextLower d D u v) j =
      (((Coefficients.entry v d).re : ℂ)^2*Coefficients.entry u j -
        (((Coefficients.entry v d).re : ℂ)*Coefficients.entry u d -
          ((Coefficients.entry u (d+1)).re : ℂ)*Coefficients.entry v (d-1))*Coefficients.entry v j -
        ((Coefficients.entry u (d+1)).re : ℂ)*((Coefficients.entry v d).re : ℂ)*
          (if j=0 then 0 else Coefficients.entry v (j-1))) / (D:ℂ) := by
  rw [Coefficients.entry, dite_eq_left hj]
  simp only [nextLower, Vector.getElem_ofFn, Fin.getElem_fin,
    show Coefficients.entry u j = u[j] by simp [Coefficients.entry, hj],
    show Coefficients.entry v j = v[j] by simp [Coefficients.entry, hj]]

theorem descending_nextLower {N d} (u v : Coefficients.Row N) (hd : 0 < d) (hN : d+1 < N)
    (hu : Coefficients.entry u (d+1) = ((Coefficients.entry u (d+1)).re : ℂ))
    (hv : Coefficients.entry v d = ((Coefficients.entry v d).re : ℂ)) (D : ℝ) (j : ℕ) :
    descending (Coefficients.entry (nextLower d D u v)) (d-1) j =
        numerator (descending (Coefficients.entry u) (d+1)) (descending (Coefficients.entry v) d) j / (D:ℂ) := by
  by_cases hj : j ≤ d-1
  · have hjN : d-1-j < N := by omega
    simp only [descending, numerator, show 0 ≤ d+1 by omega, show 0 ≤ d by omega,
      show 1 ≤ d+1 by omega, show 1 ≤ d by omega, show j+2 ≤ d+1 by omega,
      show j+1 ≤ d by omega, hj, ite_true, Nat.sub_zero,
      show d+1-1=d by omega, show d+1-(j+2)=d-1-j by omega]
    rw [entry_nextLower _ _ _ _ _ hjN, hu, hv]
    simp only [Complex.ofReal_re]
    have he : d-(j+1)=d-1-j := by omega
    rw [he]
    by_cases hz : d-1-j=0
    · have ht : ¬ j+2 ≤ d := by omega
      simp only [hz, ht, ite_false, ite_true, mul_zero, sub_zero]
    · have ht : j+2 ≤ d := by omega
      have he' : d-(j+2)=d-1-j-1 := by omega
      simp only [hz, ht, ite_false, ite_true, he']
  · simp [descending, numerator, hj, show ¬ j+2 ≤ d+1 by omega,
      show ¬ j+1 ≤ d by omega, show ¬ j+2 ≤ d by omega]

/-- Transfer the determinant invariant to the actual ascending coefficient vectors. -/
theorem advance_vectors {R : Type*} [CommRing R] (f : R →+* ℂ)
    {N d : ℕ} (u v : ℂ[X]) (h : ComplexRouth.Pair d u v)
    (hd : 0 < d) (hN : d+1 < N) (hv : (v.coeff d).re ≠ 0) (D : ℝ) (hD : 0 < D)
    (hs : Arithmetic.Segment f
      (descending (Coefficients.entry (Coefficients.pack N u)) (d+1))
      (descending (Coefficients.entry (Coefficients.pack N v)) d) (D:ℂ)) :
    Arithmetic.MappedRow f (Coefficients.entry (nextLower d D (Coefficients.pack N u) (Coefficients.pack N v))) ∧
    Arithmetic.Segment f
      (descending (Coefficients.entry (Coefficients.pack N v)) d)
      (descending (Coefficients.entry (nextLower d D (Coefficients.pack N u) (Coefficients.pack N v))) (d-1))
      (((v.coeff d).re : ℂ)^2) := by
  have huN : u.natDegree < N := h.upper_bound.trans_lt hN
  have hvN : v.natDegree < N := h.lower_bound.trans_lt (by omega)
  have huC : u.coeff (d+1) = ((u.coeff (d+1)).re : ℂ) := by
    apply Complex.ext <;> simp [h.upper_sym.real_coeff]
  have hvC : v.coeff d = ((v.coeff d).re : ℂ) := by
    apply Complex.ext <;> simp [h.lower_sym.real_coeff]
  have hlow : descending (Coefficients.entry (Coefficients.pack N v)) d 0 ≠ 0 := by
    rw [descending_zero, Coefficients.entry_pack v hvN, hvC]
    exact Complex.ofReal_ne_zero.mpr hv
  have hn := hs.advance (σ := 1) (Complex.ofReal_ne_zero.mpr (ne_of_gt hD)) hlow (Or.inl rfl)
  simp only [one_mul] at hn
  have he : descending (Coefficients.entry (nextLower d D (Coefficients.pack N u) (Coefficients.pack N v))) (d-1) =
      (fun j => numerator (descending (Coefficients.entry (Coefficients.pack N u)) (d+1))
          (descending (Coefficients.entry (Coefficients.pack N v)) d) j / (D:ℂ)) := by
    funext j
    simpa only [Coefficients.entry_pack u huN, Coefficients.entry_pack v hvN] using
      descending_nextLower (Coefficients.pack N u) (Coefficients.pack N v) hd hN
        (by simpa only [Coefficients.entry_pack u huN] using huC)
        (by simpa only [Coefficients.entry_pack v hvN] using hvC) D j
  rw [← he] at hn
  constructor
  · intro j
    by_cases hj : j ≤ d-1
    · obtain ⟨q,hq⟩ := hn.1 (d-1-j)
      refine ⟨q, ?_⟩
      simpa only [descending, show d-1-j ≤ d-1 by omega, ite_true,
        show d-1-(d-1-j)=j by omega] using hq
    · refine ⟨0, ?_⟩
      rw [nextLower_pack u v h hd hN hv D hD]
      have hb : (ComplexRouth.remainder (d-1) u v).natDegree ≤ d-1 := by
        apply ComplexRouth.remainder_bound (by simpa only [Nat.sub_add_cancel hd] using h)
        simpa only [Nat.sub_add_cancel hd] using hv
      have hb' := (natDegree_C_mul_le (((v.coeff d).re^2/D:ℝ):ℂ)
        (ComplexRouth.remainder (d-1) u v)).trans hb
      rw [Coefficients.entry_pack _ (hb'.trans_lt (by omega)), coeff_eq_zero_of_natDegree_lt (hb'.trans_lt (by omega)), map_zero]
  · have hh := hn.2
    simp only [descending_zero, Coefficients.entry_pack v hvN] at hh
    rw [hvC] at hh
    simpa only [Complex.ofReal_re] using hh

end
end RouthHurwitz.ComplexRouth.FractionFree
