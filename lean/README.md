# CGO in Lean 4: an incremental formalization

Based on **Competitive Gradient Optimization**, Abhijeet Vyas, Brian Bullins and
Kamyar Azizzadenesheli, ICML 2023.

Official source: https://proceedings.mlr.press/v202/vyas23a.html

## Kernel-checked components

| Module | Result |
|---|---|
| `Bilinear` | Exact scalar `f(x,y)=xy` CGO energy contraction and geometric convergence |
| `Extragradient` | General energy identity, descent, telescoping, fixed-step average residual rate |
| `Skew` | Inverse existence and nonexpansiveness for identity plus skew interaction |
| `TransformedField` | State-dependent inverse regularity and fixed-step optimistic CGO residual rate |
| `Objective` | Actual Fréchet derivative/Riesz Hessian, gradient derivative, Schwarz symmetry, cross-interaction extraction and stationary-zero equivalence |
| `Convergence` | Residual summability, compact subsequence and full Fejér iterate convergence |
| `ObjectiveConvergence` | Fixed-step convergence of objective-derived optimistic CGO to a stationary point under explicit hypotheses |

## Main verified objective theorem

In a finite-dimensional real inner product space, take a C² objective `f` and a
self-adjoint involution `J`. For the two-player interpretation `J` is the
player-sign operator `diag(+I,-I)`. Define

```
g(x) = J * gradient(f)(x)
H(x) = Riesz representation of the second Frechet derivative of f at x
S(x) = (J*H(x) - H(x)*J)/2
F(x) = (I + alpha*S(x))^(-1) g(x).
```

The inverse is proved to exist. The cross interaction has zero quadratic form;
on opposite-sign player subspaces it recovers the cross Hessian, and same-sign
blocks cancel. `F(x)=0` iff the actual objective gradient vanishes.

`objective_optimistic_converges` proves convergence of the full iterate sequence

```
z_(n+1) = z_n - eta*F(z_n - eta*F(z_n))
```

to a stationary point, provided:

- `g` is globally `Lg`-Lipschitz and bounded in norm by `M`;
- `||(S(y)-S(x))v|| <= LH*||x-y||*||v||`;
- `Lg,LH,M >= 0`, `eta>0`, and `eta*(Lg+|alpha|*LH*M)<1`;
- a stationary point exists;
- **at every stationary point p**, `<F(x),x-p> >= 0` for every x.

The last assumption is essential to the implemented full-iterate convergence
argument, not silently reduced to Minty at a single point. Compactness of the
bounded trajectory and residual convergence are derived in the proof.

A separate theorem gives the average squared residual bound, with
`L=Lg+|alpha|*LH*M`:

```
(1/N) sum_{n<N} ||F(z_n)||^2
 <= ||z_0-p||^2 / (eta^2*(1-eta^2*L^2)) / N.
```

## Scope and remaining work

This is **not a complete formalization of the paper or a verbatim proof of
Theorem 5.4**. The above theorem uses a fixed step, an explicitly stronger
all-stationary-points Minty hypothesis, and independently proved safe constants.
It concludes stationarity, not saddle status without an additional
stationarity-to-saddle/coherence identification.

The objective bridge is expressed using a player-sign involution rather than a
concrete product-coordinate representation. Deriving its global bounds directly
from each printed scalar regularity constant, variable-step versions, projected
domains, and the full Theorems 5.1–5.3 remain. See STATUS.md and GENERAL_NOTES.md.

## Reproduce

Lean 4.19.0, mathlib v4.19.0, pinned manifest included:

```
lake update
lake exe cache get
lake build
```

All nine modules compile. Axiom audits show only `propext`, `Classical.choice`,
and `Quot.sound`; no custom axioms or `sorry` bridge missing proofs.
See VERIFICATION.md and build.log for the recorded build.

## Further verified extension: variable weights and local Minty

`CGO/VariableStep.lean` proves the variable-step estimate with the actual weights
ηₙ²(1−ηₙ²L²). An unweighted average bound is separately proved under an explicit
uniform positive lower bound on these weights. Merely positive stepsizes are not
represented as sufficient for this unweighted bound.

`CGO/LocalConvergence.lean` proves full fixed-step extragradient convergence using
one global Minty point and only local Minty at every root. The proof controls the
lookahead inside the Minty neighborhood, establishes local Fejér trapping, and
uses a bounded subsequence plus residual decay to prove full convergence. Thus
the earlier all-roots-global-Minty theorem remains valid but is no longer the
weakest convergence result in this package.

This extension still does not identify all field roots with the paper's saddle
set or establish the published variable-step convergence claim. It is not a
verbatim formalization of Theorem 5.4.
