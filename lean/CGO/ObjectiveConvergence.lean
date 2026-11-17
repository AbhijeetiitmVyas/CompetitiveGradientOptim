import CGO.Objective
import CGO.Convergence

/-! Fixed-step convergence to a stationary point for the objective-derived
optimistic competitive-gradient iteration. Analytic bounds and Minty at every
stationary point are explicit; this is not the full published variable-step theorem. -/
noncomputable section
open Filter
namespace CGO
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

theorem objective_optimistic_converges (J : E →ₗ[ℝ] E) (hJ : SymmetricMap J)
    (hJJ : ∀ v, J (J v) = v) (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (a Lg LH M η : ℝ) (hLg : 0 ≤ Lg) (hLH : 0 ≤ LH) (hM : 0 ≤ M)
    (hη : 0 < η) (hstable : η*(Lg+|a| *LH*M) < 1)
    (hg : ∀ x y, ‖objectiveGameGradient J f x-objectiveGameGradient J f y‖ ≤ Lg*‖x-y‖)
    (hbound : ∀ x, ‖objectiveGameGradient J f x‖ ≤ M)
    (hvar : ∀ x y v, ‖objectiveInteraction J f y v-objectiveInteraction J f x v‖ ≤
      LH*‖x-y‖*‖v‖)
    (hex : ∃ p, gradient f p = 0)
    (hMinty : ∀ p, gradient f p = 0 → ∀ x,
      0 ≤ inner (𝕜 := ℝ) (objectiveCompetitiveGradient J hJ f hf a x) (x-p))
    (z : ℕ → E)
    (hrec : ∀ n, z (n+1) = z n-η • objectiveCompetitiveGradient J hJ f hf a
      (z n-η • objectiveCompetitiveGradient J hJ f hf a (z n))) :
    ∃ q, gradient f q = 0 ∧ Tendsto z atTop (nhds q) := by
  let F := objectiveCompetitiveGradient J hJ f hf a
  have hl : ∀ x y, ‖F x-F y‖ ≤ (Lg+|a| *LH*M)*‖x-y‖ :=
    transformedField_lipschitz (objectiveInteraction J f)
      (objectiveInteraction_zeroQuadratic J hJ f hf) a (objectiveGameGradient J f)
      Lg LH M hLH hg hbound hvar
  have he : ∃ p, F p = 0 := by
    obtain ⟨p, hp⟩ := hex
    exact ⟨p, (objectiveCompetitiveGradient_zero_iff J hJ hJJ f hf a p).mpr hp⟩
  have hm : ∀ p, F p = 0 → ∀ x, 0 ≤ inner (𝕜 := ℝ) (F x) (x-p) := by
    intro p hp
    exact hMinty p ((objectiveCompetitiveGradient_zero_iff J hJ hJJ f hf a p).mp hp)
  obtain ⟨q, hq, hlim⟩ := extragradient_converges F z η (Lg+|a| *LH*M)
    hη (by positivity) hstable hl he hm hrec
  exact ⟨q, (objectiveCompetitiveGradient_zero_iff J hJ hJJ f hf a q).mp hq, hlim⟩
end CGO
#print axioms CGO.objective_optimistic_converges
