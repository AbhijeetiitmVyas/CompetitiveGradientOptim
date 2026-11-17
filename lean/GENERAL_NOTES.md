# Interpretation notes

The objective theorem now uses actual Fréchet derivatives, not an arbitrary
operator merely named a Hessian. The Riesz map converts the second derivative
into a linear operator, and Schwarz's theorem supplies its symmetry.

A self-adjoint player-sign involution J generalizes diag(+I,-I). Its commutator
with the Hessian cancels pure-player blocks and has the correct mixed-block
sign. A concrete product-coordinate specialization is still separate work.

The theorem assumes globally bounded/Lipschitz game gradient and globally
Lipschitz interaction. These bounds are substantive; they do not follow from
C² regularity alone. For estimates valid only on a region, a trajectory
invariance proof and restricted-domain variant are required.

The fixed-step residual bound only needs Minty relative to its reference point.
The full convergence theorem explicitly requires Minty relative to **every
stationary point**, so the distance to the cluster point is also nonincreasing.
The proof derives residual summability, a zero-residual cluster point and full
sequence convergence. It does not infer iterate convergence from averaged
residual convergence alone.

The limit is proved stationary. Calling it a saddle point requires connecting
the paper's alpha-coherence definition to the stationary set; this is not yet
included. This package is not a certification of all statements in the paper.
