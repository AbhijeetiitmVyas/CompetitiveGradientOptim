# What the second milestone establishes

The new rate proof is valid for any finite-dimensional real inner product space,
not only scalar or bilinear games. It proves the inverse and regularity of the
competitive transformed field from explicit hypotheses, and then proves an
optimistic two-step residual bound.

For a twice-differentiable minimax objective, the intended specialization is
`g=(grad_x f,-grad_y f)` and the interaction block
`S=[0,Hxy;-Hyx,0]` with `Hyx=Hxy^T`. The zero-quadratic-form condition is the
algebraic consequence of that transpose relation. This exact connection to
Lean's differential calculus has **not yet been implemented**.

The theorem assumes a globally bounded base field and global Lipschitz bounds.
For unbounded-gradient objectives or estimates valid only on a compact region,
a restricted-domain/trajectory theorem is needed, together with a proof that
the iterates stay in that region. Do not infer this from the current theorem.

The theorem is about the average squared residual of the transformed field,
not convergence of the point sequence. A positive step is fixed, so the
variable-step subtlety in the paper's Appendix H.2 is avoided openly rather
than silently hidden. The constant used is a separately proved sufficient
bound, not the precise expression printed in Theorem 5.4.
