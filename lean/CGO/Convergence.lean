import CGO.Extragradient
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Full iterate convergence from a common-root Minty condition.
This explicitly requires the sign condition at every zero of the field, not
only at one distinguished point. -/
noncomputable section
open scoped BigOperators
open Filter
namespace CGO

/-- A positive-coefficient descent estimate yields summability of residuals. -/
theorem descent_summable (D R : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hD : ∀ n, 0 ≤ D n) (hR : ∀ n, 0 ≤ R n)
    (hstep : ∀ n, D (n+1) ≤ D n-c*R n) : Summable R := by
  apply summable_of_sum_range_le hR
  intro N
  apply (le_div_iff₀ hc).2
  have h := sum_residual_bound D R c N hD hstep
  simpa only [mul_comm] using h

section Convergence
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem residual_tends_to_zero (F : E → E) (z : ℕ → E)
    (hs : Summable (fun n => ‖F (z n)‖^2)) :
    Tendsto (fun n => F (z n)) atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hs.tendsto_atTop_zero
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h

/-- Fejér descent at every root plus residual summability gives iterate convergence. -/
theorem converges_of_root_descent (F : E → E) (z : ℕ → E) (c : ℝ)
    (hc : 0 < c) (hcont : Continuous F) (hex : ∃ p, F p = 0)
    (hstep : ∀ p, F p = 0 → ∀ n,
      ‖z (n+1)-p‖^2 ≤ ‖z n-p‖^2-c*‖F (z n)‖^2) :
    ∃ q, F q = 0 ∧ Tendsto z atTop (nhds q) := by
  obtain ⟨p, hp⟩ := hex
  have hanti : ∀ q, F q = 0 → Antitone (fun n => ‖z n-q‖^2) := by
    intro q hq
    apply antitone_nat_of_succ_le
    intro n
    have h := hstep q hq n
    have hr : 0 ≤ c*‖F (z n)‖^2 := by positivity
    linarith
  have hb : ∀ n, z n ∈ Metric.closedBall p ‖z 0-p‖ := by
    intro n
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h := hanti p hp (Nat.zero_le n)
    dsimp at h
    have hn := norm_nonneg (z n-p)
    have h0 := norm_nonneg (z 0-p)
    nlinarith
  have hsum := descent_summable (fun n => ‖z n-p‖^2)
    (fun n => ‖F (z n)‖^2) c hc (fun n => sq_nonneg _) (fun n => sq_nonneg _)
    (hstep p hp)
  have hres := residual_tends_to_zero F z hsum
  obtain ⟨q, _, φ, hφ, hlim⟩ := (isCompact_closedBall p ‖z 0-p‖).tendsto_subseq hb
  have hq : F q = 0 := by
    have h1 := hcont.continuousAt.tendsto.comp hlim
    have h2 := hres.comp hφ.tendsto_atTop
    exact tendsto_nhds_unique h1 h2
  refine ⟨q, hq, Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hlim ε hε
  refine ⟨φ K, ?_⟩
  intro n hn
  have hsub := hK K (le_refl K)
  have ha := hanti q hq hn
  dsimp at ha
  simp only [Function.comp_apply, dist_eq_norm] at hsub
  rw [dist_eq_norm]
  have hn0 := norm_nonneg (z n-q)
  have hk0 := norm_nonneg (z (φ K)-q)
  nlinarith
/-- Full convergence for fixed-step extragradient under Minty at every root. -/
theorem extragradient_converges (F : E → E) (z : ℕ → E) (η L : ℝ)
    (hη : 0 < η) (hL : 0 ≤ L) (hstable : η*L < 1)
    (hLip : ∀ x y, ‖F x-F y‖ ≤ L*‖x-y‖)
    (hex : ∃ p, F p = 0)
    (hMinty : ∀ p, F p = 0 → ∀ x, 0 ≤ inner (𝕜 := ℝ) (F x) (x-p))
    (hrec : ∀ n, z (n+1) = z n-η • F (z n-η • F (z n))) :
    ∃ q, F q = 0 ∧ Tendsto z atTop (nhds q) := by
  have hc : 0 < η^2*(1-η^2*L^2) := by
    have hp : 0 ≤ η*L := mul_nonneg (le_of_lt hη) hL
    have hs : 0 < 1-η^2*L^2 := by nlinarith
    exact mul_pos (sq_pos_of_pos hη) hs
  have hl : LipschitzWith ⟨L,hL⟩ F := LipschitzWith.of_dist_le_mul (by
    intro x y
    simpa only [dist_eq_norm, NNReal.coe_mk] using hLip x y)
  apply converges_of_root_descent F z (η^2*(1-η^2*L^2)) hc hl.continuous hex
  intro p hp n
  rw [hrec]
  exact extragradient_descent F (z n) p η L (le_of_lt hη) hL
    (hMinty p hp _) (hLip _ _)
end Convergence
end CGO
#print axioms CGO.converges_of_root_descent

#print axioms CGO.extragradient_converges
