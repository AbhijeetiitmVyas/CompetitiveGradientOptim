# CGO in Lean 4: verified bilinear starting point

This is an initial, deliberately limited formalization of **Competitive Gradient
Optimization**, Abhijeet Vyas, Brian Bullins and Kamyar Azizzadenesheli, ICML 2023.

Source: https://proceedings.mlr.press/v202/vyas23a.html
Paper: https://proceedings.mlr.press/v202/vyas23a/vyas23a.pdf

## Scope

`CGO/Bilinear.lean` specializes equation (3) to the unconstrained scalar game
`f(x,y) = x*y`. It verifies the two linear equations defining the competitive
gradient, derives the exact one-step squared-distance identity, proves its
geometric iterate formula, and proves that squared distance tends to zero when
`0 < eta < 2*alpha`.

With `d=1+alpha^2`, the update is

```
x' = x - eta * (y + alpha*x)/d
y' = y - eta * (alpha*y - x)/d
```

For `E(x,y)=x^2+y^2`, the exact contraction factor is

```
q = 1 - eta*(2*alpha-eta)/(1+alpha^2)
E(z_n) = q^n E(z_0)
```

The file proves `0 <= q < 1` under the step-size conditions. It also checks
that alpha=0 gives the simultaneous GDA factor `1+eta^2`.

This is **not** a formalization of the complete paper or of the general
Theorems 5.1–5.4. In particular, no full Hessian spectral argument,
alpha-coherence characterization, projected/proximal update, or general
nonlinear convergence theorem is claimed. The connection between the source
paper's derivatives and this scalar algebraic specialization is documented,
not itself encoded as a differentiability theorem.

## Build

Requires Lean 4.19.0 and mathlib v4.19.0. With elan installed:

```
lake update
lake exe cache get
lake build
```

The final command prints the axioms of the convergence result. Standard Lean
foundations such as `propext`, `Classical.choice`, and `Quot.sound` are expected;
`sorryAx` is not.

See `VERIFICATION.md` for the actual verification status of this deliverable.

## Further work

1. Formalize the general Euclidean extragradient one-step energy inequality.
2. Prove its telescoping rate under explicit fixed-step or uniform-margin
   conditions.
3. Connect the vector field to the CGO skew block operator and prove the
   required Lipschitz estimates.
4. Reconcile every hypothesis with the published theorem before calling the
   complete theorem verified.

No claim of theorem verification should be based on a Lean file that merely
assumes the theorem's main descent inequality or introduces an axiom for it.
