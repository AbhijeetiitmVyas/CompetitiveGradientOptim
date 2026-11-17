import CGO.Skew
import CGO.Extragradient

/-! A transformed-field regularity bound for a state-dependent skew interaction.
These hypotheses are explicit analytic requirements, not a claim that all the
paper's printed constants or assumptions have already been matched. -/
noncomputable section
open scoped BigOperators
namespace CGO
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def transformedField (S : E → E →ₗ[ℝ] E) (hS : ∀ x, ZeroQuadratic (S x))
    (a : ℝ) (g : E → E) (x : E) : E := competitiveInverse (S x) (hS x) a (g x)

theorem transformedField_solves (S : E → E →ₗ[ℝ] E) (hS : ∀ x, ZeroQuadratic (S x))
    (a : ℝ) (g : E → E) (x : E) :
    transformedField S hS a g x + a • (S x (transformedField S hS a g x)) = g x := by
  exact competitiveInverse_solves (S x) (hS x) a (g x)

theorem transformedField_norm_le (S : E → E →ₗ[ℝ] E) (hS : ∀ x, ZeroQuadratic (S x))
    (a : ℝ) (g : E → E) (x : E) : ‖transformedField S hS a g x‖ ≤ ‖g x‖ :=
  competitiveInverse_norm_le (S x) (hS x) a (g x)

/-- A safe Lipschitz bound via the resolvent identity. -/
theorem transformedField_lipschitz (S : E → E →ₗ[ℝ] E)
    (hS : ∀ x, ZeroQuadratic (S x)) (a : ℝ) (g : E → E)
    (Lg LH M : ℝ) (hLH : 0 ≤ LH)
    (hg : ∀ x y, ‖g x-g y‖ ≤ Lg*‖x-y‖)
    (hbound : ∀ x, ‖g x‖ ≤ M)
    (hvar : ∀ x y v, ‖S y v-S x v‖ ≤ LH*‖x-y‖*‖v‖)
    (x y : E) :
    ‖transformedField S hS a g x-transformedField S hS a g y‖ ≤
      (Lg+|a| *LH*M)*‖x-y‖ := by
  let F := transformedField S hS a g
  have hx := transformedField_solves S hS a g x
  have hy := transformedField_solves S hS a g y
  have hid : interactionMap (S x) a (F x-F y) =
      (g x-g y)+a • (S y (F y)-S x (F y)) := by
    change (F x-F y)+a • S x (F x-F y) = _
    rw [map_sub, smul_sub]
    rw [← hx, ← hy]
    dsimp [F]
    simp only [smul_sub]
    abel
  have h1 := interaction_expansive (S x) (hS x) a (F x-F y)
  rw [hid] at h1
  have h2 := norm_add_le (g x-g y) (a • (S y (F y)-S x (F y)))
  rw [norm_smul, Real.norm_eq_abs] at h2
  have h3 := hvar x y (F y)
  have h4 : ‖F y‖ ≤ M := (transformedField_norm_le S hS a g y).trans (hbound y)
  have h5 := mul_le_mul_of_nonneg_left h4 (mul_nonneg hLH (norm_nonneg (x-y)))
  have h6 := mul_le_mul_of_nonneg_left (h3.trans h5) (abs_nonneg a)
  have h7 := hg x y
  change ‖F x-F y‖ ≤ _
  nlinarith
/-- General optimistic competitive-gradient rate with explicit safe constants.
This is a fixed-step theorem for a bounded Lipschitz base field and a Lipschitz
skew interaction; it is not presented as a verbatim version of Theorem 5.4. -/
theorem optimistic_competitive_average_rate (S : E → E →ₗ[ℝ] E)
    (hS : ∀ x, ZeroQuadratic (S x)) (a : ℝ) (g : E → E)
    (Lg LH M η : ℝ) (hLg : 0 ≤ Lg) (hLH : 0 ≤ LH) (hM : 0 ≤ M)
    (hη : 0 < η) (hstable : η*(Lg+|a| *LH*M) < 1)
    (hg : ∀ x y, ‖g x-g y‖ ≤ Lg*‖x-y‖)
    (hbound : ∀ x, ‖g x‖ ≤ M)
    (hvar : ∀ x y v, ‖S y v-S x v‖ ≤ LH*‖x-y‖*‖v‖)
    (p : E) (hMinty : ∀ x, 0 ≤ inner (𝕜 := ℝ) (transformedField S hS a g x) (x-p))
    (z : ℕ → E)
    (hrec : ∀ n, z (n+1) = z n-η • transformedField S hS a g
      (z n-η • transformedField S hS a g (z n)))
    (N : ℕ) (hN : 0 < N) :
    (∑ n ∈ Finset.range N, ‖transformedField S hS a g (z n)‖^2) / (N : ℝ) ≤
      (‖z 0-p‖^2 / (η^2*(1-η^2*(Lg+|a| *LH*M)^2))) / (N : ℝ) := by
  apply extragradient_average_rate (transformedField S hS a g) z p η
    (Lg+|a| *LH*M) hη (by positivity) hstable hMinty
  · exact transformedField_lipschitz S hS a g Lg LH M hLH hg hbound hvar
  · exact hrec
  · exact hN
end CGO
#print axioms CGO.optimistic_competitive_average_rate
#print axioms CGO.transformedField_lipschitz
