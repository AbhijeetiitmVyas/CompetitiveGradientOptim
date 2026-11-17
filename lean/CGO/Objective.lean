import CGO.TransformedField
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Objective-derived skew interaction. A self-adjoint player-sign operator J
represents diag(+I,-I). The commutator (J H-H J)/2 extracts exactly the
cross-Hessian block used by CGO; pure Hessian terms cancel. -/
noncomputable section
namespace CGO
open InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def SymmetricMap (A : E →ₗ[ℝ] E) : Prop :=
  ∀ u v, inner (𝕜 := ℝ) (A u) v = inner (𝕜 := ℝ) u (A v)

/-- Riesz representation of the actual second Fréchet derivative. -/
def objectiveHessian (f : E → ℝ) (x : E) : E →ₗ[ℝ] E :=
  ((toDual ℝ E).symm.toLinearEquiv.toLinearMap).comp
    (fderiv ℝ (fderiv ℝ f) x).toLinearMap

theorem objectiveHessian_inner (f : E → ℝ) (x u v : E) :
    inner (𝕜 := ℝ) (objectiveHessian f x u) v =
      fderiv ℝ (fderiv ℝ f) x u v := by
  exact toDual_symm_apply

/-- The Riesz Hessian is the derivative of the actual gradient map. -/
theorem gradient_hasFDerivAt (f : E → ℝ) (x : E) (hf : ContDiffAt ℝ 2 f x) :
    HasFDerivAt (gradient f)
      ((toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (fderiv ℝ f) x)) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x := by
    apply ContDiffAt.differentiableAt _ le_rfl
    exact hf.fderiv_right (by norm_num)
  exact ((toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).comp
    x hd.hasFDerivAt

/-- C² regularity supplies Hessian symmetry via Schwarz's theorem. -/
theorem objectiveHessian_symmetric (f : E → ℝ) (x : E)
    (hf : ContDiffAt ℝ 2 f x) : SymmetricMap (objectiveHessian f x) := by
  intro u v
  rw [objectiveHessian_inner, real_inner_comm (objectiveHessian f x v) u,
    objectiveHessian_inner]
  exact hf.isSymmSndFDerivAt (by norm_num) u v

def crossInteraction (J H : E →ₗ[ℝ] E) : E →ₗ[ℝ] E :=
  (1/2 : ℝ) • (J.comp H-H.comp J)

omit [CompleteSpace E] in
theorem crossInteraction_zeroQuadratic (J H : E →ₗ[ℝ] E)
    (hJ : SymmetricMap J) (hH : SymmetricMap H) : ZeroQuadratic (crossInteraction J H) := by
  intro v
  simp only [crossInteraction, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, real_inner_smul_right, inner_sub_right]
  rw [← hJ v (H v), ← hH (J v) v, real_inner_comm v (H (J v))]
  ring

/- The positive/negative player blocks recover the positive cross Hessian. -/
omit [CompleteSpace E] in
theorem crossInteraction_mixed (J H : E →ₗ[ℝ] E) (hJ : SymmetricMap J)
    (u v : E) (hu : J u = u) (hv : J v = -v) :
    inner (𝕜 := ℝ) u (crossInteraction J H v) = inner (𝕜 := ℝ) u (H v) := by
  simp only [crossInteraction, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, real_inner_smul_right, inner_sub_right]
  rw [← hJ u (H v), hu, hv, map_neg, inner_neg_right]
  ring

/- The two pure-player blocks cancel in the interaction. -/
omit [CompleteSpace E] in
theorem crossInteraction_same_sign (J H : E →ₗ[ℝ] E) (hJ : SymmetricMap J)
    (u v : E) (s : ℝ) (hu : J u = s • u) (hv : J v = s • v) :
    inner (𝕜 := ℝ) u (crossInteraction J H v) = 0 := by
  simp only [crossInteraction, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, real_inner_smul_right, inner_sub_right]
  rw [← hJ u (H v), hu, hv, map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

def objectiveInteraction (J : E →ₗ[ℝ] E) (f : E → ℝ) (x : E) : E →ₗ[ℝ] E :=
  crossInteraction J (objectiveHessian f x)

def objectiveGameGradient (J : E →ₗ[ℝ] E) (f : E → ℝ) (x : E) : E :=
  J (gradient f x)

theorem objectiveInteraction_zeroQuadratic (J : E →ₗ[ℝ] E)
    (hJ : SymmetricMap J) (f : E → ℝ) (hf : ContDiff ℝ 2 f) (x : E) :
    ZeroQuadratic (objectiveInteraction J f x) :=
  crossInteraction_zeroQuadratic J (objectiveHessian f x) hJ
    (objectiveHessian_symmetric f x hf.contDiffAt)
section Competitive
variable [FiniteDimensional ℝ E]

def objectiveCompetitiveGradient (J : E →ₗ[ℝ] E) (hJ : SymmetricMap J)
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) (a : ℝ) (x : E) : E :=
  transformedField (objectiveInteraction J f)
    (objectiveInteraction_zeroQuadratic J hJ f hf) a (objectiveGameGradient J f) x

/-- The objective-derived competitive gradient solves equation (3). -/
theorem objectiveCompetitiveGradient_solves (J : E →ₗ[ℝ] E) (hJ : SymmetricMap J)
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) (a : ℝ) (x : E) :
    objectiveCompetitiveGradient J hJ f hf a x +
      a • objectiveInteraction J f x (objectiveCompetitiveGradient J hJ f hf a x) =
      J (gradient f x) :=
  transformedField_solves (objectiveInteraction J f)
    (objectiveInteraction_zeroQuadratic J hJ f hf) a (objectiveGameGradient J f) x

/-- With the player-sign involution, competitive zeros are exactly stationary points. -/
theorem objectiveCompetitiveGradient_zero_iff (J : E →ₗ[ℝ] E) (hJ : SymmetricMap J)
    (hJJ : ∀ v, J (J v) = v) (f : E → ℝ) (hf : ContDiff ℝ 2 f) (a : ℝ) (x : E) :
    objectiveCompetitiveGradient J hJ f hf a x = 0 ↔ gradient f x = 0 := by
  constructor
  · intro hzero
    have hs := objectiveCompetitiveGradient_solves J hJ f hf a x
    rw [hzero, map_zero, smul_zero, add_zero] at hs
    calc
      gradient f x = J (J (gradient f x)) := (hJJ _).symm
      _ = 0 := by rw [← hs, map_zero]
  · intro hzero
    unfold objectiveCompetitiveGradient transformedField objectiveGameGradient
    rw [hzero, map_zero]
    exact map_zero _
end Competitive
end CGO
#print axioms CGO.objectiveCompetitiveGradient_zero_iff
#print axioms CGO.objectiveInteraction_zeroQuadratic

#print axioms CGO.gradient_hasFDerivAt
