import SympyProofs.ComplexRouthHurwitz.FractionFree.InitialDeterminants
import SympyProofs.ComplexRouthHurwitz.FractionFree.Algebra

/-! The ring-valued invariant for an uninterrupted squared-pivot segment.
The sign may change at every step. A repair starts a fresh segment with divisor
one once its output rows are known to belong to the coefficient ring. -/
namespace RouthHurwitz.ComplexRouth.FractionFree.Arithmetic
variable {R K : Type*} [CommRing R] [Field K]

/-- Seed rows, determinant scale, and a unit sign are proof-only data. -/
def Segment (f : R →+* K) (upper lower : ℕ → K) (D : K) : Prop :=
  ∃ u v : ℕ → K, ∃ k : ℕ, ∃ a e : K,
    (∀ m j, ∃ z : R, (minor u v m j).det = f z) ∧ Regular u v k ∧ (e = 1 ∨ e = -1) ∧
    D = a*(e*weight u v k) ∧
    (∀ j, upper j = a*(pair u v k).1 j) ∧
    (∀ j, lower j = e*weight u v k*(pair u v k).2 j)

theorem Segment.start {f : R →+* K} {u v : ℕ → K}
    (hu : MappedRow f u) (hv : MappedRow f v) : Segment f u v 1 := by
  refine ⟨u,v,0,1,1,mapped_minor f u v hu hv, trivial, Or.inl rfl, ?_, ?_, ?_⟩ <;> simp [weight, pair]

/-- The special first elimination starts with divisor `a`, not `a²`. -/
theorem Segment.start_initial {R K : Type*} [CommRing R] [Field K]
    (f : R →+* K) (U V : ℕ → R) (a b : R) (ha : f a ≠ 0)
    (hU : U 0 = a) (hV : V 0 = b) :
    Segment f (fun j => f (U j)) (fun j => f (a*V (j+1)-b*U (j+1))) (f a) := by
  refine ⟨(fun j => f (U j)/f a), _, 0, f a, 1,
    mapped_initial_minor f U V a b ha hU hV, trivial, Or.inl rfl, ?_, ?_, ?_⟩
  · simp [weight]
  · intro j; simp [pair]; field_simp
  · intro j; simp [pair, weight]

/-- The quotient row is a signed subresultant row, hence belongs to the ring. -/
theorem Segment.advance {f : R →+* K} {upper lower : ℕ → K} {D σ : K}
    (h : Segment f upper lower D) (hD : D ≠ 0) (hp : lower 0 ≠ 0)
    (hσ : σ = 1 ∨ σ = -1) :
    let row := fun j => σ * numerator upper lower j / D
    MappedRow f row ∧ Segment f (fun j => σ*lower j) row (lower 0^2) := by
  obtain ⟨u,v,k,a,e,hmin,hr,he,hD',hupper,hlower⟩ := h
  have hw := weight_ne_zero u v k hr
  have hp' : (pair u v k).2 0 ≠ 0 := by
    intro hz; apply hp; rw [hlower, hz, mul_zero]
  have hr' : Regular u v (k+1) := (regular_step u v k).mpr ⟨hr,hp'⟩
  have ha : a ≠ 0 := by intro hz; apply hD; simp [hD', hz]
  have he' : e ≠ 0 := by rcases he with rfl | rfl <;> simp
  have hrow (j : ℕ) : σ*numerator upper lower j / D =
      (σ*e)*weight u v (k+1)*(pair u v (k+1)).2 j := by
    rw [weight_step, pair_step]
    dsimp only
    simp only [numerator, hupper, hlower, hD', next]
    field_simp
    ring
  have hem : ∃ t : R, e = f t := by
    rcases he with he | he
    · exact ⟨1, by simpa using he⟩
    · exact ⟨-1, by simpa using he⟩
  have hσm : ∃ t : R, σ = f t := by
    rcases hσ with hs | hs
    · exact ⟨1, by simpa using hs⟩
    · exact ⟨-1, by simpa using hs⟩
  constructor
  · intro j
    obtain ⟨q,hq⟩ := hmin (k+1) j
    rw [det_pair u v (k+1) j hr'] at hq
    obtain ⟨t,ht⟩ := hem
    obtain ⟨s,hs⟩ := hσm
    refine ⟨s*t*q, ?_⟩
    dsimp only at hq ⊢
    rw [hrow, mul_assoc, hq, hs, ht, map_mul, map_mul]
  · refine ⟨u,v,k+1,σ*e*weight u v k,σ*e,hmin,hr',?_,?_,?_,hrow⟩
    · rcases hσ with rfl | rfl <;> rcases he with rfl | rfl <;> simp
    · rw [hlower, weight_step]
      rcases hσ with rfl | rfl <;> ring
    · intro j; dsimp only; rw [pair_step, hlower]; dsimp only; ring

/-- Exact cancellation in any coefficient ring embedded injectively in a field.
Unlike the local two-step identity, this applies at every regular segment step. -/
theorem Segment.divisor_dvd (f : R →+* K) (hf : Function.Injective f)
    (upper lower : ℕ → R) (D σ : R)
    (h : Segment f (fun j => f (upper j)) (fun j => f (lower j)) (f D))
    (hD : D ≠ 0) (hp : lower 0 ≠ 0) (hσ : σ = 1 ∨ σ = -1) (j : ℕ) :
    D ∣ σ*numerator upper lower j := by
  have hD' : f D ≠ 0 := fun h => hD (hf (h.trans (map_zero f).symm))
  have hp' : f (lower 0) ≠ 0 := fun h => hp (hf (h.trans (map_zero f).symm))
  have hσ' : f σ = 1 ∨ f σ = -1 := by rcases hσ with rfl | rfl <;> simp
  obtain ⟨q,hq⟩ := (h.advance hD' hp' hσ').1 j
  refine ⟨q, hf ?_⟩
  dsimp only at hq
  simp only [map_mul]
  rw [← hq]
  simp only [map_mul, numerator, map_sub, map_pow]
  field_simp

end RouthHurwitz.ComplexRouth.FractionFree.Arithmetic
