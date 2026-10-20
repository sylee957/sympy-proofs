module

public import SympyProofs.Python.Cost.Bounds
public import Mathlib.Analysis.Asymptotics.Theta

/-!
# From concrete execution bounds to asymptotic bounds

Results concern the counter returned by `CostT.run`. A caller supplies the input
family and filter, allowing one-parameter, multivariate, or restricted-domain
analyses without baking a particular notion of input size into the cost model.
-/

@[expose] public section

namespace Python.Cost

open Asymptotics Filter

variable {X α : Type} {l : Filter X}

theorem nat_isBigO_of_le_mul {f g : X → ℕ} (C : ℕ) (h : ∀ x, f x ≤ C * g x) :
    (fun x => (f x : ℝ)) =O[l] (fun x => (g x : ℝ)) := by
  apply IsBigO.of_bound (C : ℝ)
  filter_upwards [] with x
  simpa only [Real.norm_natCast] using (show (f x : ℝ) ≤ (C : ℝ) * g x by
    exact_mod_cast h x)

theorem nat_isTheta_of_bounds {f g : X → ℕ} (C : ℕ)
    (hl : ∀ x, g x ≤ f x) (hu : ∀ x, f x ≤ C * g x) :
    (fun x => (f x : ℝ)) =Θ[l] (fun x => (g x : ℝ)) :=
  ⟨nat_isBigO_of_le_mul C hu, nat_isBigO_of_le_mul 1 (by simpa using hl)⟩

/-- Compose a program's proved budget with an independent asymptotic estimate. -/
theorem Bounded.isBigO {model : Model} {program : X → CostT Id α}
    {post : X → α → Prop} {budget : X → ℕ} {scale : X → ℝ}
    (h : ∀ x, Bounded model (program x) (post x) (budget x))
    (hb : (fun x => (budget x : ℝ)) =O[l] scale) :
    (fun x => ((CostT.run (program x) model).2 : ℝ)) =O[l] scale := by
  exact (nat_isBigO_of_le_mul 1 (by simpa using fun x => (h x).cost_le)).trans hb

end Python.Cost
