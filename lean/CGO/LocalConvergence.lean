import CGO.Convergence

/-! Local Fejér trapping: global Fejér monotonicity at every root is unnecessary
once a root is a cluster point and a local nonincrease estimate is available. -/
noncomputable section
open Filter
namespace CGO

/-- A converging subsequence enters a local invariant ball; local distance
nonincrease then forces convergence of the entire sequence. -/
theorem tendsto_of_local_fejer {E : Type*} [MetricSpace E]
    (z : ℕ → E) (q : E) (φ : ℕ → ℕ) (_hφ : StrictMono φ)
    (hsub : Tendsto (z ∘ φ) atTop (nhds q)) (r : ℝ) (hr : 0 < r)
    (hlocal : ∀ n, dist (z n) q < r → dist (z (n+1)) q ≤ dist (z n) q) :
    Tendsto z atTop (nhds q) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hsub (min ε r) (lt_min hε hr)
  have hstart := hK K (le_refl K)
  simp only [Function.comp_apply] at hstart
  refine ⟨φ K, ?_⟩
  intro n hn
  have hbound : ∀ m, dist (z (φ K+m)) q ≤ dist (z (φ K)) q := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hin : dist (z (φ K+m)) q < r :=
        lt_of_le_of_lt ih (lt_of_lt_of_le hstart (min_le_right _ _))
      exact le_trans (hlocal (φ K+m) hin) ih
  have h := hbound (n-φ K)
  rw [Nat.add_sub_of_le hn] at h
  exact lt_of_le_of_lt h (lt_of_lt_of_le hstart (min_le_left _ _))

/-- One global descent point gives boundedness and residual decay. Local Fejér
nonincrease at each root is enough for full convergence. -/
theorem converges_of_global_descent_local_fejer
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (F : E → E) (z : ℕ → E) (p : E) (c : ℝ)
    (hc : 0 < c) (hcont : Continuous F)
    (hstep : ∀ n, ‖z (n+1)-p‖^2 ≤ ‖z n-p‖^2-c*‖F (z n)‖^2)
    (hlocal : ∀ q, F q = 0 → ∃ r : ℝ, 0 < r ∧
      ∀ n, dist (z n) q < r → dist (z (n+1)) q ≤ dist (z n) q) :
    ∃ q, F q = 0 ∧ Tendsto z atTop (nhds q) := by
  have ha : Antitone (fun n => ‖z n-p‖^2) := by
    apply antitone_nat_of_succ_le
    intro n
    have h := hstep n
    have hp : 0 ≤ c*‖F (z n)‖^2 := by positivity
    linarith
  have hb : ∀ n, z n ∈ Metric.closedBall p ‖z 0-p‖ := by
    intro n
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h := ha (Nat.zero_le n)
    dsimp at h
    have hn := norm_nonneg (z n-p)
    have h0 := norm_nonneg (z 0-p)
    nlinarith
  have hs := descent_summable (fun n => ‖z n-p‖^2)
    (fun n => ‖F (z n)‖^2) c hc (fun n => sq_nonneg _)
    (fun n => sq_nonneg _) hstep
  have hz := residual_tends_to_zero F z hs
  obtain ⟨q, _, φ, hφ, hlim⟩ := (isCompact_closedBall p ‖z 0-p‖).tendsto_subseq hb
  have hq : F q = 0 := tendsto_nhds_unique
    (hcont.continuousAt.tendsto.comp hlim) (hz.comp hφ.tendsto_atTop)
  obtain ⟨r, hr, hl⟩ := hlocal q hq
  exact ⟨q, hq, tendsto_of_local_fejer z q φ hφ hlim r hr hl⟩
/-- Local Minty suffices because Lipschitz continuity keeps the lookahead inside
its neighborhood whenever the original iterate is sufficiently close. -/
theorem extragradient_local_fejer
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : E → E) (q x : E) (η L r : ℝ)
    (hη : 0 ≤ η) (hL : 0 ≤ L) (hstable : η*L ≤ 1)
    (hq : F q = 0) (_hr : 0 < r)
    (hLip : ∀ x y, ‖F x-F y‖ ≤ L*‖x-y‖)
    (hMinty : ∀ y, ‖y-q‖ < r → 0 ≤ inner (𝕜 := ℝ) (F y) (y-q))
    (hx : ‖x-q‖ < r/(1+η*L)) :
    ‖(x-η • F (x-η • F x))-q‖ ≤ ‖x-q‖ := by
  have hd : 0 < 1+η*L := by positivity
  have hf : ‖F x‖ ≤ L*‖x-q‖ := by simpa [hq] using hLip x q
  have he : (x-η • F x)-q = (x-q)-η • F x := by abel
  have ht := norm_sub_le (x-q) (η • F x)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη] at ht
  have hy : ‖(x-η • F x)-q‖ < r := by
    rw [he]
    have hxf := (lt_div_iff₀ hd).mp hx
    have hm := mul_le_mul_of_nonneg_left hf hη
    nlinarith
  have hs := extragradient_descent F x q η L hη hL (hMinty _ hy) (hLip _ _)
  have hc : 0 ≤ η^2*(1-η^2*L^2) := by
    have hp := mul_nonneg hη hL
    have hh : 0 ≤ 1-η^2*L^2 := by nlinarith
    exact mul_nonneg (sq_nonneg _) hh
  have hp := mul_nonneg hc (sq_nonneg ‖F x‖)
  have h0 := norm_nonneg (x-q)
  nlinarith

/-- Fixed-step convergence with one global Minty point and only local Minty
at all roots, rather than global Minty at every root. -/
theorem extragradient_converges_local_minty
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (F : E → E) (z : ℕ → E) (p : E) (η L : ℝ)
    (hη : 0 < η) (hL : 0 ≤ L) (hstable : η*L < 1)
    (hLip : ∀ x y, ‖F x-F y‖ ≤ L*‖x-y‖)
    (hglobal : ∀ x, 0 ≤ inner (𝕜 := ℝ) (F x) (x-p))
    (hlocal : ∀ q, F q = 0 → ∃ r : ℝ, 0 < r ∧
      ∀ x, ‖x-q‖ < r → 0 ≤ inner (𝕜 := ℝ) (F x) (x-q))
    (hrec : ∀ n, z (n+1) = z n-η • F (z n-η • F (z n))) :
    ∃ q, F q = 0 ∧ Tendsto z atTop (nhds q) := by
  have hc : 0 < η^2*(1-η^2*L^2) := by
    have hp := mul_nonneg (le_of_lt hη) hL
    have hs : 0 < 1-η^2*L^2 := by nlinarith
    exact mul_pos (sq_pos_of_pos hη) hs
  have hl : LipschitzWith ⟨L,hL⟩ F := LipschitzWith.of_dist_le_mul (by
    intro x y
    simpa only [dist_eq_norm, NNReal.coe_mk] using hLip x y)
  apply converges_of_global_descent_local_fejer F z p (η^2*(1-η^2*L^2)) hc hl.continuous
  · intro n
    rw [hrec]
    exact extragradient_descent F (z n) p η L (le_of_lt hη) hL (hglobal _) (hLip _ _)
  · intro q hq
    obtain ⟨r, hr, hm⟩ := hlocal q hq
    have hd : 0 < 1+η*L := by positivity
    refine ⟨r/(1+η*L), div_pos hr hd, ?_⟩
    intro n hn
    simp only [dist_eq_norm] at hn ⊢
    rw [hrec]
    exact extragradient_local_fejer F q (z n) η L r (le_of_lt hη) hL
      (le_of_lt hstable) hq hr hLip hm hn

end CGO
#print axioms CGO.converges_of_global_descent_local_fejer

#print axioms CGO.extragradient_converges_local_minty
