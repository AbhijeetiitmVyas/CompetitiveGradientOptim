# Statement correspondence and remaining work

## Proved

- Scalar bilinear equation (3), unique saddle, exact contraction and geometric rate.
- General Euclidean extragradient energy identity and descent under explicit
  local Minty and Lipschitz inequalities.
- Fixed-step average squared-residual bound with a positive uniform margin.
- Finite-dimensional invertibility of the identity plus a zero-quadratic-form
  linear interaction and inverse nonexpansiveness.
- State-dependent transformed-field Lipschitz estimate from explicit base-field
  and interaction bounds.
- Riesz representation of the objective's actual second Fréchet derivative;
  this is the derivative of its gradient when the objective is C².
- Hessian symmetry from Schwarz's theorem, not an unproved symmetry axiom.
- Player-sign commutator extraction: positive-to-negative mixed block and
  cancellation of same-sign blocks. Zero quadratic form follows.
- Competitive zeros iff objective stationary points for a sign involution.
- General fixed-step full iterate convergence under Minty at every root,
  existence of a root and a global Lipschitz bound. Residual summability and
  compactness/Fejér arguments are proved.
- Objective-derived optimistic CGO convergence to a stationary point under the
  README's complete explicit hypotheses.

## Not yet proved

- Literal product-coordinate instantiation `J=diag(+I,-I)` with partial-gradient
  and partial-Hessian notation matched point-for-point to the paper.
- Translation from every printed regularity constant to the global analytic
  assumptions used in the current theorem.
- Published variable-step conditions/constants or the full Theorems 5.1–5.4.
- General constrained/projected/proximal updates or invariance in restricted
  domains where only local bounds hold.
- The implication from stationary limit to saddle point via the paper's full
  definition of alpha-coherence.
- Numerical solver, GAN experiments or empirical claims.

These boundaries are not filled by custom axioms, placeholders or assumed
conclusions. The current fixed-step theorem is intentionally labeled separately
from the published variable-step theorem.

Latest additions (supersede the all-roots-global-Minty limitation above):
- Verified variable-step weighted residual bound.
- Verified unweighted rate with an explicit uniform lower descent-weight bound.
- Verified fixed-step convergence under local Minty at roots and one global Minty point.
- Still pending: objective saddle characterization and literal published variable-step hypotheses.
