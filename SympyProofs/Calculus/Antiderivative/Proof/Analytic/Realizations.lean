module

public import SympyProofs.Calculus.Antiderivative.Proof.Analytic.OpenSet
public import SympyProofs.Calculus.Antiderivative.Proof.Tower
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv

/-! The usual complex variable, exponential, logarithm and tangent give actual solutions of
the corresponding tower equations on their regular branches. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

open Filter Topology

variable {n : ℕ} {z : ℂ} {G : ℂ → Fin n → ℂ}

/-- Extend a realization with one new complex function as the last coordinate. -/
def Model.adjoin (G : ℂ → Fin n → ℂ) (f : ℂ → ℂ) : ℂ → Fin (n+1) → ℂ :=
  fun w => Fin.lastCases (f w) (G w)

private theorem Model.include_hasValue {x : M ℂ n} {a : ℂ} {f : ℂ → ℂ}
    (h : HasValue (G z) x a) : HasValue (adjoin G f z) (includeVars (Nat.le_succ n) x) a := by
  apply hasValue_include_iff.mpr
  simpa only [adjoin, Function.comp_def, Fin.lastCases_castSucc] using h

private theorem Model.last_hasValue (G : ℂ → Fin n → ℂ) (f : ℂ → ℂ) (z : ℂ) :
    HasValue (adjoin G f z) (polynomial ℂ (MvPolynomial.X (Fin.last n))) (f z) := by
  simpa [adjoin] using HasValue.polynomial (p := adjoin G f z) (MvPolynomial.X (Fin.last n))

private theorem Model.SolvedBy.adjoin {v : List (M ℂ n)} (len : v.length = n)
    (hg : SolvedBy v G z) {x : M ℂ (n+1)} {c : ℂ} {f : ℂ → ℂ}
    (hx : HasValue (Model.adjoin G f z) x c) (hf : HasDerivAt f c z) :
    SolvedBy (v.map (includeVars (Nat.le_succ n)) ++ [x]) (Model.adjoin G f) z := by
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa [List.getD,len,Model.adjoin,hx.evalAt] using
      And.intro (show RegularAt _ x from ⟨_,hx⟩) hf
  · obtain ⟨hr,hd⟩ := hg i
    have hv := include_hasValue (f := f) hr.hasValue
    have e : (v.map (includeVars (Nat.le_succ n)) ++ [x]).getD i.castSucc.val 0 =
        includeVars (Nat.le_succ n) (v.getD i.val 0) := by simp [List.getD,len,i.isLt]
    rw [e,hv.evalAt]
    exact ⟨⟨_,hv⟩,by simpa [Model.adjoin] using hd⟩

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [Algebra R ℂ] [FaithfulSMul R ℂ] {t : Tower R n}

private theorem Tower.SolvedBy.extend {g : Gen (K R n)} (hg : t.SolvedBy G z)
    {f : ℂ → ℂ} {c : ℂ}
    (hx : Model.HasValue (Model.adjoin G f z) (val ℂ ((t.step g).D K.gen)) c)
    (hf : HasDerivAt f c z) : (t.step g).SolvedBy (Model.adjoin G f) z := by
  change Model.SolvedBy _ _ _
  have hv : (t.step g).gens.map (val ℂ) =
      (t.gens.map (val ℂ)).map (Model.includeVars (Nat.le_succ n)) ++
        [val ℂ ((t.step g).D K.gen)] := by
    cases g <;> simp only [D_gen_prim,D_gen_exp,D_gen_tan] <;>
      simp [gens,D,List.map_map,Function.comp_def]
  rw [hv]
  exact Model.SolvedBy.adjoin (by simp) hg hx hf

/-- A constant velocity `b` gives the ordinary coordinate `b z` at height one. -/
theorem Tower.solvedBy_variable (b : K R 0) (z : ℂ) :
    ((Tower.base : Tower R 0).step (.prim b)).SolvedBy
      (Model.adjoin (fun _ => Fin.elim0) (fun w => Model.constantHom ℂ b * w)) z := by
  apply SolvedBy.extend (fun i => i.elim0)
  · rw [D_gen_prim,val_lift,← Model.C_zero_constantHom]
    exact Model.include_hasValue (Model.HasValue.C _)
  · simpa using (hasDerivAt_id z).const_mul (Model.constantHom ℂ b)

/-- The exponential of a regular argument realizes its exponential tower step. -/
theorem Tower.SolvedBy.exp (hg : t.SolvedBy G z) (u : K R n)
    (hu : Model.RegularAt (G z) (val ℂ u)) :
    (t.step (.exp u)).SolvedBy
      (Model.adjoin G (fun w => Complex.exp (Model.evalAt (G w) (val ℂ u)))) z := by
  obtain ⟨hr,hd⟩ := Model.hasDerivAt_evalAt hg hu
  apply hg.extend
  · rw [D_gen_exp,map_mul,val_lift,val_D,Antiderivative.val_gen]
    exact (Model.include_hasValue hr.hasValue).mul (Model.last_hasValue ..)
  · simpa only [mul_comm] using hd.cexp

/-- Any continuous local logarithm of a regular argument realizes the corresponding
primitive tower step. -/
theorem Tower.SolvedBy.logWith (hg : t.SolvedBy G z) (u : K R n) {f : ℂ → ℂ}
    (hu : Model.RegularAt (G z) (val ℂ u)) (hf : ContinuousAt f z)
    (h : ∀ᶠ w in 𝓝 z, Complex.exp (f w) = Model.evalAt (G w) (val ℂ u)) :
    (t.step (.prim (t.D u / u))).SolvedBy (Model.adjoin G f) z := by
  obtain ⟨hr,hd⟩ := Model.hasDerivAt_evalAt hg hu
  apply hg.extend
  · rw [D_gen_prim,val_lift,map_div₀,val_D]
    exact Model.include_hasValue (hr.hasValue.div hu.hasValue
      (h.self_of_nhds ▸ Complex.exp_ne_zero _))
  · exact hasDerivAt_of_exp_eq hd hf h

/-- Off its branch cut, the principal logarithm realizes a logarithmic tower step. -/
theorem Tower.SolvedBy.log (hg : t.SolvedBy G z) (u : K R n)
    (hu : Model.RegularAt (G z) (val ℂ u))
    (hs : Model.evalAt (G z) (val ℂ u) ∈ Complex.slitPlane) :
    (t.step (.prim (t.D u / u))).SolvedBy
      (Model.adjoin G (fun w => Complex.log (Model.evalAt (G w) (val ℂ u)))) z := by
  have hc := (Model.hasDerivAt_evalAt hg hu).2.continuousAt
  exact hg.logWith u hu (hc.clog hs) ((hc.eventually_ne (Complex.slitPlane_ne_zero hs)).mono
    fun _ hw => Complex.exp_log hw)

/-- Away from cosine zeroes, the usual complex tangent realizes the native tangent velocity. -/
theorem Tower.solvedBy_tan (t : Tower R n) (hg : t.SolvedBy G z) (u : K R n)
    (hu : Model.RegularAt (G z) (val ℂ u))
    (hz : Complex.cos (Model.evalAt (G z) (val ℂ u)) ≠ 0) :
    (t.step (.tan u)).SolvedBy
      (Model.adjoin G (fun w => Complex.tan (Model.evalAt (G w) (val ℂ u)))) z := by
  let f (w : ℂ) := Complex.tan (Model.evalAt (G w) (val ℂ u))
  obtain ⟨hr,hd⟩ := Model.hasDerivAt_evalAt hg hu
  let a := Model.evalAt (G z) (val ℂ u)
  let d := Model.evalAt (G z) (t.modelD ℂ (val ℂ u))
  apply hg.extend (c := d*(1+f z^2))
  · have hx := Model.last_hasValue G f z
    have h1 : Model.HasValue (Model.adjoin G f z) 1 1 := by
      simpa using Model.HasValue.C (p := Model.adjoin G f z) (1 : ℂ)
    simpa only [D_gen_tan,map_mul,map_add,map_pow,map_one,val_lift,Antiderivative.val_gen,
      t.val_D ℂ u,pow_two,modelD,d,Model.polynomial,f] using
       (Model.include_hasValue hr.hasValue).mul (h1.add (hx.mul hx))
  · have he := (Complex.hasDerivAt_tan hz).comp z hd
    have htc : (1 + Complex.tan a^2) * Complex.cos a^2 = 1 :=
      Complex.one_add_tan_sq_mul_cos_sq_eq_one hz
    have eqn : d*(1+Complex.tan a^2) = 1 / Complex.cos a^2 * d := by
      rw [(div_eq_iff (pow_ne_zero _ hz)).mpr htc.symm, mul_comm]
    rw [show d*(1+f z^2) = _ from eqn]
    exact he

omit [DecidableEq R] [NormalizedGCDMonoid R] [Div R] [Algebra R ℂ] [FaithfulSMul R ℂ] in
/-- A primitive adds no exceptional values to a nondegenerate realization. -/
theorem Tower.Nondegenerate.prim (h : t.Nondegenerate (G z)) (b : K R n) (f : ℂ → ℂ) :
    (t.step (.prim b)).Nondegenerate (Model.adjoin G f z) := by
  simpa only [Tower.Nondegenerate,Model.adjoin,Function.comp_def,Fin.lastCases_castSucc] using h

/-- The ordinary exponential never takes the exceptional value zero. -/
theorem Tower.Nondegenerate.exp (h : t.Nondegenerate (G z)) (u : K R n) :
    (t.step (.exp u)).Nondegenerate
      (Model.adjoin G (fun w => Complex.exp (Model.evalAt (G w) (val ℂ u))) z) := by
  simpa only [Tower.Nondegenerate,Model.adjoin,Function.comp_def,Fin.lastCases_castSucc,
    Fin.lastCases_last] using And.intro h (Complex.exp_ne_zero _)

/-- Actual complex tangents omit both exceptional values of the native Riccati equation. -/
theorem Trigonometric.tan_nondegenerate (z : ℂ) :
    Complex.tan z ≠ Complex.I ∧ Complex.tan z ≠ -Complex.I := by
  have omit_root (c : ℂ) (hc : c^2 = -1) : Complex.tan z ≠ c := by
    have hn : c ≠ 0 := by rintro rfl; simp at hc
    intro h
    rw [Complex.tan_eq_sin_div_cos] at h
    by_cases hz : Complex.cos z = 0
    · simp [hz, hn.symm] at h
    · have eq := Complex.sin_sq_add_cos_sq z
      rw [(div_eq_iff hz).mp h,mul_pow,hc,neg_one_mul,neg_add_cancel] at eq
      exact zero_ne_one eq
  exact ⟨omit_root _ Complex.I_sq,omit_root _ (by simp)⟩

/-- The ordinary tangent omits both stationary values of the tangent equation. -/
theorem Tower.Nondegenerate.tan {t : Tower R n} (h : t.Nondegenerate (G z)) (u : K R n) :
    (t.step (.tan u)).Nondegenerate
      (Model.adjoin G (fun w => Complex.tan (Model.evalAt (G w) (val ℂ u))) z) := by
  simpa only [Tower.Nondegenerate,Model.adjoin,Function.comp_def,Fin.lastCases_castSucc,
    Fin.lastCases_last] using And.intro h (Trigonometric.tan_nondegenerate _)

end SympyProofs.Calculus.Antiderivative
