module

public import SympyProofs.Calculus.Antiderivative.Program.Kind.Coefficients
public import SympyProofs.Calculus.Antiderivative.Proof.Row
import Mathlib.Data.List.GetD

/-! Recovering particular solutions of the differential equation from a parametric solution. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

theorem Level.val_combine (v : List (K R 0)) (hs : List (K R n)) :
    val k (Level.combine v hs) = Model.linearCombination k (v.map (Model.constantHom k)) hs := by
  induction v generalizing hs with
  | nil => simp [combine, Model.linearCombination]
  | cons c cs ih =>
    cases hs with
    | nil => simp [combine, Model.linearCombination]
    | cons y ys =>
      simp only [combine, List.zipWith_cons_cons, List.sum_cons, map_add, map_mul,
        List.map_cons, Model.linearCombination]
      rw [← Level.combine, ih, Model.C_constantHom]

private theorem normalized_rows {rows : List (List (K R 0))} {width : ℕ} {v : List (K R 0)}
    (hv : Linear.normalized rows width = some v) :
    v.length = width ∧ v.headD 0 = 1 ∧
      ∀ r ∈ rows, Model.rowHolds k r (v.map (Model.constantHom k)) := by
  let f := Model.constantHom (R := R) k
  obtain ⟨hlen,hfirst,hok⟩ := Linear.normalized_sound f rows width hv
  refine ⟨hlen,hfirst,fun r hr => ?_⟩
  rw [Model.rowHolds_iff_functional, List.length_map, hlen]
  convert hok r hr using 2
  ext j
  change (v.map f).getD j 0 = f (v.getD j 0)
  exact (congrArg (fun z => (v.map f).getD j z) (map_zero f).symm).trans (List.getD_map v 0 f)

private theorem normalized_exists {rows : List (List (K R 0))} {m : ℕ} {cs : List k}
    (hl : cs.length = m + 1) (hhead : cs.headD 0 = 1)
    (h : ∀ r ∈ rows, Model.rowHolds k r cs) :
    ∃ v, Linear.normalized rows (m + 1) = some v := by
  cases ho : Linear.normalized rows (m+1) with
  | some v => exact ⟨v,rfl⟩
  | none =>
    apply False.elim ((Linear.normalized_none_iff (Model.constantHom k) rows m).mp ho ?_)
    refine ⟨Linear.vector (RingHom.id k) (m+1) cs, ?_, ?_⟩
    · cases cs with
      | nil => simp at hhead
      | cons => exact hhead
    · intro r hr
      have hx := (Model.rowHolds_iff_functional k r cs).mp (h r hr)
      exact (congrArg (fun m => Linear.functional (Model.constantHom k) m r
        (Linear.vector (RingHom.id k) m cs) = 0) hl).mp hx

/-- A successful non-parametric solve returns a solution in the model differential field. -/
theorem Level.rde_sound {t : Tower R n} {L : Level R n} (hL : L.SolveSpec k t)
    {f g y : K R n} (hy : L.rde f g = some y) :
    t.modelD k (val k y) + val k f * val k y = val k g := by
  have H := hL f [g]
  rcases hs : L.solve f [g] with ⟨basis, rows⟩
  rw [hs] at H
  simp only [rde, hs] at hy
  cases hv : Linear.normalized rows (basis.length + 1) with
  | none => simp [hv] at hy
  | some v =>
    rw [hv] at hy
    have hy' : combine v.tail basis = y := Option.some.inj hy
    obtain ⟨hl, hh, hr⟩ := normalized_rows k hv
    cases v with
    | nil => simp at hl
    | cons a as =>
      have ha : a = 1 := hh
      subst a
      subst y
      have hd : (as.map (Model.constantHom k)).length = basis.length := by simpa using hl
      have he := (H (val k (combine as basis)) [1] rfl).mpr
        ⟨_, hd, val_combine k as basis, by simpa using hr⟩
      simpa [Model.linearCombination] using he

/-- Failure excludes a solution even after extending the constants. -/
theorem Level.rde_complete {t : Tower R n} {L : Level R n} (hL : L.SolveSpec k t)
    {f g : K R n} (hy : L.rde f g = none) :
    ¬ ∃ y : M k n, t.modelD k y + val k f * y = val k g := by
  rintro ⟨y,he⟩
  have H := hL f [g] y [1] rfl
  rcases hs : L.solve f [g] with ⟨basis, rows⟩
  rw [hs] at H
  obtain ⟨d,hd,_,hr⟩ := H.mp (by simpa [Model.linearCombination] using he)
  have hl : ([1] ++ d).length = basis.length + 1 := by simpa using hd
  obtain ⟨v,hv⟩ := normalized_exists k hl (by rfl) hr
  simp [rde, hs, hv] at hy

/-- The computed limited primitive solves the requested equation, including its constant. -/
theorem Level.limited_sound {t : Tower R n} {L : Level R n} (hL : L.SolveSpec k t)
    {g b y : K R n} {c : K R 0} (hy : L.limited g b = some (c,y)) :
    t.modelD k (val k y) = val k g - val k (K.ofConst c * b) := by
  have H := hL 0 [g,b]
  rcases hs : L.solve 0 [g,b] with ⟨basis, rows⟩
  rw [hs] at H
  simp only [limited, hs] at hy
  cases hv : Linear.normalized rows (basis.length + 2) with
  | none => simp [hv] at hy
  | some v =>
    rw [hv] at hy
    obtain ⟨hc,hy'⟩ := Prod.mk.inj (Option.some.inj hy)
    obtain ⟨hl,hh,hr⟩ := normalized_rows k hv
    cases v with
    | nil => simp at hl
    | cons a as =>
      have ha : a = 1 := hh
      subst a
      cases as with
      | nil => simp at hl
      | cons q qs =>
        subst c y
        have hd : (qs.map (Model.constantHom k)).length = basis.length := by simpa using hl
        have he := (H (val k (combine qs basis)) [1, Model.constantHom k q] rfl).mpr
          ⟨_, hd, val_combine k qs basis, by simpa using hr⟩
        simpa [Model.linearCombination, Model.C_constantHom, sub_eq_add_neg] using he

/-- Failure excludes all solutions, including choices of the constant in the larger model. -/
theorem Level.limited_complete {t : Tower R n} {L : Level R n} (hL : L.SolveSpec k t)
    {g b : K R n} (hy : L.limited g b = none) :
    ¬ ∃ (c : k) (y : M k n), t.modelD k y = val k g - Model.C k n c * val k b := by
  rintro ⟨c,y,he⟩
  have H := hL 0 [g,b] y [1,-c] rfl
  rcases hs : L.solve 0 [g,b] with ⟨basis, rows⟩
  rw [hs] at H
  obtain ⟨d,hd,_,hr⟩ := H.mp (by simpa [Model.linearCombination, sub_eq_add_neg] using he)
  have hl : ([1,-c] ++ d).length = (basis.length + 1) + 1 := by simpa using hd
  obtain ⟨v,hv⟩ := normalized_exists k hl (by rfl) hr
  simp [limited, hs, hv] at hy

end SympyProofs.Calculus.Antiderivative
