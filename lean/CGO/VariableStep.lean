import CGO.Convergence

/-! Variable-step guarantees retain their actual weights. -/
noncomputable section
open scoped BigOperators
namespace CGO

/-- Telescoping with a coefficient that may vary or approach zero. -/
theorem weighted_sum_bound (D R c : ℕ → ℝ) (N : ℕ)
    (hD : ∀ n, 0 ≤ D n)
    (hstep : ∀ n, D (n+1) ≤ D n-c n*R n) :
    (∑ n ∈ Finset.range N, c n*R n) ≤ D 0 := by
  simpa using sum_residual_bound D (fun n => c n*R n) 1 N hD (by simpa using hstep)

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- No lower stepsize bound is needed for the correctly weighted estimate. -/
theorem variable_extragradient_weighted_bound (F : E → E) (z : ℕ → E)
    (p : E) (η : ℕ → ℝ) (L : ℝ)
    (hη : ∀ n, 0 ≤ η n) (hL : 0 ≤ L)
    (hMinty : ∀ x, 0 ≤ inner (𝕜 := ℝ) (F x) (x-p))
    (hLip : ∀ x y, ‖F x-F y‖ ≤ L*‖x-y‖)
    (hrec : ∀ n, z (n+1) = z n-η n • F (z n-η n • F (z n)))
    (N : ℕ) :
    (∑ n ∈ Finset.range N, (η n)^2*(1-(η n)^2*L^2)*‖F (z n)‖^2)
      ≤ ‖z 0-p‖^2 := by
  apply weighted_sum_bound (fun n => ‖z n-p‖^2) (fun n => ‖F (z n)‖^2)
    (fun n => (η n)^2*(1-(η n)^2*L^2)) N (fun n => sq_nonneg _)
  intro n
  dsimp
  rw [hrec]
  exact extragradient_descent F (z n) p (η n) L (hη n) hL (hMinty _) (hLip _ _)

/-- An unweighted rate follows when the actual descent weights have a uniform
positive lower bound. This additional assumption is explicit. -/
theorem variable_extragradient_average_rate (F : E → E) (z : ℕ → E)
    (p : E) (η : ℕ → ℝ) (L c : ℝ)
    (hη : ∀ n, 0 ≤ η n) (hL : 0 ≤ L) (hc : 0 < c)
    (hweight : ∀ n, c ≤ (η n)^2*(1-(η n)^2*L^2))
    (hMinty : ∀ x, 0 ≤ inner (𝕜 := ℝ) (F x) (x-p))
    (hLip : ∀ x y, ‖F x-F y‖ ≤ L*‖x-y‖)
    (hrec : ∀ n, z (n+1) = z n-η n • F (z n-η n • F (z n)))
    (N : ℕ) :
    (∑ n ∈ Finset.range N, ‖F (z n)‖^2)/(N : ℝ) ≤
      (‖z 0-p‖^2/c)/(N : ℝ) := by
  have hb := variable_extragradient_weighted_bound F z p η L hη hL hMinty hLip hrec N
  have hs : c*(∑ n ∈ Finset.range N, ‖F (z n)‖^2) ≤ ‖z 0-p‖^2 := by
    rw [Finset.mul_sum]
    apply le_trans (Finset.sum_le_sum (fun n _ =>
      mul_le_mul_of_nonneg_right (hweight n) (sq_nonneg _))) hb
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply (le_div_iff₀ hc).2
  simpa only [mul_comm] using hs
end
end CGO
#print axioms CGO.variable_extragradient_weighted_bound
#print axioms CGO.variable_extragradient_average_rate
