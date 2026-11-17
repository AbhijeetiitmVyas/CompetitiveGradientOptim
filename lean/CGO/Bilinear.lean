import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A verified special case of Competitive Gradient Optimization

Source: Vyas, Bullins, Azizzadenesheli (ICML 2023), equation (3),
specialized to f(x,y) = x*y. This file is NOT a formalization of all
of Theorems 5.1--5.4. The inverse defining g_alpha is verified by its
two scalar equations below, rather than assumed.
-/
noncomputable section

namespace CGO

/-- Squared Euclidean distance to the unique saddle point (0,0). -/
def energy (z : ℝ × ℝ) : ℝ := z.1 ^ 2 + z.2 ^ 2

/-- The scalar game's saddle condition, with x minimizing and y maximizing. -/
def IsSaddle (x y : ℝ) : Prop :=
  (∀ v : ℝ, x*v ≤ x*y) ∧ (∀ u : ℝ, x*y ≤ u*y)

theorem saddle_iff_origin (x y : ℝ) : IsSaddle x y ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have hx := h.1 (y+x)
    have hy := h.2 (x-y)
    constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]
  · rintro ⟨rfl, rfl⟩
    simp [IsSaddle]

/-- Eq. (3) specialized to f(x,y)=xy. -/
def direction (a : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  ((z.2 + a*z.1)/(1+a^2), (a*z.2-z.1)/(1+a^2))

def step (a η : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1 - η*(direction a z).1, z.2 - η*(direction a z).2)

def factor (a η : ℝ) : ℝ := 1 - η*(2*a-η)/(1+a^2)

theorem denom_pos (a : ℝ) : 0 < 1+a^2 := by positivity

theorem direction_solves_system (a : ℝ) (z : ℝ × ℝ) :
    (direction a z).1 + a*(direction a z).2 = z.2 ∧
    -a*(direction a z).1 + (direction a z).2 = -z.1 := by
  unfold direction
  dsimp
  constructor <;> field_simp [ne_of_gt (denom_pos a)] <;> ring

theorem energy_step (a η : ℝ) (z : ℝ × ℝ) :
    energy (step a η z) = factor a η * energy z := by
  unfold energy step direction factor
  dsimp
  field_simp [ne_of_gt (denom_pos a)]
  ring

theorem factor_nonneg (a η : ℝ) : 0 ≤ factor a η := by
  have h : factor a η = ((η-a)^2+1)/(1+a^2) := by
    unfold factor
    field_simp [ne_of_gt (denom_pos a)]
    ring
  rw [h]
  positivity

theorem factor_lt_one {a η : ℝ} (hη : 0 < η) (hupper : η < 2*a) :
    factor a η < 1 := by
  have h : 0 < η*(2*a-η)/(1+a^2) :=
    div_pos (mul_pos hη (sub_pos.mpr hupper)) (denom_pos a)
  unfold factor
  linarith

/-- The exact geometric rate, with no oracle or descent-lemma assumption. -/
theorem energy_iterate (a η : ℝ) (z : ℝ × ℝ) (n : ℕ) :
    energy ((step a η)^[n] z) = factor a η ^ n * energy z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', energy_step, ih, pow_succ]
    ring

/-- For positive eta below 2 alpha, squared distance tends to zero. -/
theorem energy_tends_to_zero {a η : ℝ} (hη : 0 < η) (hupper : η < 2*a)
    (z : ℝ × ℝ) :
    Filter.Tendsto (fun n : ℕ => energy ((step a η)^[n] z))
      Filter.atTop (nhds 0) := by
  simp_rw [energy_iterate]
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (factor_nonneg a η)
    (factor_lt_one hη hupper)
  simpa using h.mul_const (energy z)

/-- Contrast: simultaneous GDA (alpha=0) increases energy for eta != 0. -/
theorem gda_factor (η : ℝ) : factor 0 η = 1 + η^2 := by
  unfold factor
  ring

end CGO

#print axioms CGO.energy_tends_to_zero
