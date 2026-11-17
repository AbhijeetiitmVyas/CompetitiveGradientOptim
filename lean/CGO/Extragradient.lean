import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
General Euclidean extragradient energy analysis relevant to CGO Theorem 5.4.
The transformed field is arbitrary here: identifying it with the paper's
competitive gradient and proving its Lipschitz bound remains a separate task.
-/
noncomputable section
open scoped BigOperators
namespace CGO
section Extragradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact two-step energy identity, before coherence or regularity assumptions. -/
theorem extragradient_energy_identity (x p g h : E) (η : ℝ) :
    ‖(x - η • h) - p‖ ^ 2 = ‖x-p‖ ^ 2
      - 2*η*inner (𝕜 := ℝ) h ((x-η • g)-p)
      + η^2*‖h-g‖^2 - η^2*‖g‖^2 := by
  have hx : (x-η • h)-p = (x-p)-η • h := by abel
  have hu : (x-η • g)-p = (x-p)-η • g := by abel
  rw [hx, hu]
  simp only [norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    inner_sub_right, real_inner_smul_right, real_inner_smul_left]
  simp only [inner_sub_left]
  rw [real_inner_comm h x, real_inner_comm h p]
  ring

/-- A local Minty sign and a local Lipschitz bound suffice for one-step descent. -/
theorem extragradient_descent (F : E → E) (x p : E) (η L : ℝ)
    (hη : 0 ≤ η) (_hL : 0 ≤ L)
    (hMinty : 0 ≤ inner (𝕜 := ℝ) (F (x-η • F x)) ((x-η • F x)-p))
    (hLip : ‖F (x-η • F x)-F x‖ ≤ L*‖(x-η • F x)-x‖) :
    ‖(x-η • F (x-η • F x))-p‖^2 ≤ ‖x-p‖^2
      - (η^2*(1-η^2*L^2))*‖F x‖^2 := by
  have hdiff : (x-η • F x)-x = -(η • F x) := by abel
  rw [hdiff, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη] at hLip
  have hsq : ‖F (x-η • F x)-F x‖^2 ≤ (L*(η*‖F x‖))^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hLip 2
  rw [extragradient_energy_identity]
  have hm : 0 ≤ 2*η*inner (𝕜 := ℝ) (F (x-η • F x)) ((x-η • F x)-p) := by positivity
  have hs := mul_le_mul_of_nonneg_left hsq (sq_nonneg η)
  nlinarith
end Extragradient

/-- Finite telescoping; all descent assumptions are explicit hypotheses. -/
theorem sum_residual_bound (D R : ℕ → ℝ) (c : ℝ) (N : ℕ)
    (hD : ∀ n, 0 ≤ D n)
    (hstep : ∀ n, D (n+1) ≤ D n-c*R n) :
    c*(∑ n ∈ Finset.range N, R n) ≤ D 0 := by
  have htel : ∀ N, D N+c*(∑ n ∈ Finset.range N, R n) ≤ D 0 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hs := hstep N
      nlinarith
  have h := htel N
  have hn := hD N
  linarith
section Rate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- General fixed-step O(1/N) average squared-field bound for extragradient.
The trajectory recurrence, Minty condition, and Lipschitz estimate are hypotheses,
not assumed descent inequalities. -/
theorem extragradient_average_rate (F : E → E) (z : ℕ → E) (p : E)
    (η L : ℝ) (hη : 0 < η) (hL : 0 ≤ L) (hstable : η*L < 1)
    (hMinty : ∀ x, 0 ≤ inner (𝕜 := ℝ) (F x) (x-p))
    (hLip : ∀ x y, ‖F x-F y‖ ≤ L*‖x-y‖)
    (hrec : ∀ n, z (n+1) = z n-η • F (z n-η • F (z n)))
    (N : ℕ) (hN : 0 < N) :
    (∑ n ∈ Finset.range N, ‖F (z n)‖^2) / (N : ℝ) ≤
      (‖z 0-p‖^2 / (η^2*(1-η^2*L^2))) / (N : ℝ) := by
  have hc : 0 < η^2*(1-η^2*L^2) := by
    have hp : 0 ≤ η*L := mul_nonneg (le_of_lt hη) hL
    have hs : 0 < 1-η^2*L^2 := by nlinarith
    exact mul_pos (sq_pos_of_pos hη) hs
  have hs := sum_residual_bound (fun n => ‖z n-p‖^2)
    (fun n => ‖F (z n)‖^2) (η^2*(1-η^2*L^2)) N
    (fun n => sq_nonneg _) (by
      intro n
      dsimp
      rw [hrec]
      exact extragradient_descent F (z n) p η L (le_of_lt hη) hL
        (hMinty _) (hLip _ _))
  have hsum : (∑ n ∈ Finset.range N, ‖F (z n)‖^2) ≤
      ‖z 0-p‖^2 / (η^2*(1-η^2*L^2)) := by
    apply (le_div_iff₀ hc).2
    simpa only [mul_comm] using hs
  exact div_le_div_of_nonneg_right hsum (by positivity)
end Rate
end CGO

#print axioms CGO.extragradient_descent
#print axioms CGO.sum_residual_bound
