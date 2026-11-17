import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Invertibility of the identity plus a skew interaction operator, the
linear-algebra backbone of CGO equation (3). -/
noncomputable section
namespace CGO
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The interaction has zero quadratic form, as does the skew cross-Hessian block. -/
def ZeroQuadratic (S : E →ₗ[ℝ] E) : Prop := ∀ v, inner (𝕜 := ℝ) v (S v) = 0

/-- The usual real skew-adjoint identity implies the zero quadratic form. -/
theorem zeroQuadratic_of_skew (S : E →ₗ[ℝ] E)
    (hskew : ∀ u v, inner (𝕜 := ℝ) u (S v) = -inner (𝕜 := ℝ) (S u) v) :
    ZeroQuadratic S := by
  intro v
  have h := hskew v v
  rw [real_inner_comm v (S v)] at h
  linarith

def interactionMap (S : E →ₗ[ℝ] E) (a : ℝ) : E →ₗ[ℝ] E := LinearMap.id + a • S

theorem interaction_inner (S : E →ₗ[ℝ] E) (hS : ZeroQuadratic S)
    (a : ℝ) (v : E) : inner (𝕜 := ℝ) v (interactionMap S a v) = ‖v‖^2 := by
  simp only [interactionMap, LinearMap.add_apply, LinearMap.id_coe, id_eq,
    LinearMap.smul_apply, inner_add_right, real_inner_smul_right, hS v,
    mul_zero, add_zero, real_inner_self_eq_norm_sq]

theorem interaction_expansive (S : E →ₗ[ℝ] E) (hS : ZeroQuadratic S)
    (a : ℝ) (v : E) : ‖v‖ ≤ ‖interactionMap S a v‖ := by
  have hi := real_inner_le_norm v (interactionMap S a v)
  rw [interaction_inner S hS] at hi
  have hv := norm_nonneg v
  have hw := norm_nonneg (interactionMap S a v)
  nlinarith

theorem interaction_injective (S : E →ₗ[ℝ] E) (hS : ZeroQuadratic S)
    (a : ℝ) : Function.Injective (interactionMap S a) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have hn := interaction_expansive S hS a v
  rw [hv, norm_zero] at hn
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg v))

/-- Finite dimension turns injectivity into the inverse required by CGO. -/
theorem interaction_bijective [FiniteDimensional ℝ E] (S : E →ₗ[ℝ] E)
    (hS : ZeroQuadratic S) (a : ℝ) : Function.Bijective (interactionMap S a) :=
  ⟨interaction_injective S hS a,
    LinearMap.injective_iff_surjective.mp (interaction_injective S hS a)⟩

def competitiveInverse [FiniteDimensional ℝ E] (S : E →ₗ[ℝ] E)
    (hS : ZeroQuadratic S) (a : ℝ) : E ≃ₗ[ℝ] E :=
  (LinearEquiv.ofBijective (interactionMap S a) (interaction_bijective S hS a)).symm

theorem competitiveInverse_solves [FiniteDimensional ℝ E] (S : E →ₗ[ℝ] E)
    (hS : ZeroQuadratic S) (a : ℝ) (g : E) :
    interactionMap S a (competitiveInverse S hS a g) = g := by
  exact (LinearEquiv.ofBijective (interactionMap S a)
    (interaction_bijective S hS a)).apply_symm_apply g

theorem competitiveInverse_norm_le [FiniteDimensional ℝ E] (S : E →ₗ[ℝ] E)
    (hS : ZeroQuadratic S) (a : ℝ) (g : E) :
    ‖competitiveInverse S hS a g‖ ≤ ‖g‖ := by
  have h := interaction_expansive S hS a (competitiveInverse S hS a g)
  rwa [competitiveInverse_solves] at h
theorem competitiveInverse_nonexpansive [FiniteDimensional ℝ E]
    (S : E →ₗ[ℝ] E) (hS : ZeroQuadratic S) (a : ℝ) (g h : E) :
    ‖competitiveInverse S hS a g-competitiveInverse S hS a h‖ ≤ ‖g-h‖ := by
  rw [← map_sub]
  exact competitiveInverse_norm_le S hS a (g-h)
end CGO
#print axioms CGO.competitiveInverse_norm_le
