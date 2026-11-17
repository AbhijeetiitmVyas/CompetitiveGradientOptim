# Statement correspondence ledger

| Lean result | Paper relationship | Status boundary |
|---|---|---|
| `saddle_iff_origin` | Scalar example f(x,y)=xy | Exact saddle inequalities |
| `direction_solves_system` | Equation (3) | Scalar block-system identity |
| `energy_step` | Discrete CGO convergence mechanism | Exact scalar identity; no descent hypothesis assumed |
| `factor_nonneg`, `factor_lt_one` | Stable parameter region | Assumes 0 < eta < 2 alpha; entails alpha > 0 |
| `energy_iterate` | Geometric rate | Exact formula for every natural n |
| `energy_tends_to_zero` | Scalar bilinear convergence | Squared distance tends to zero; not general nonlinear theorem |
| `gda_factor` | CGO alpha=0 reduces to GDA | Exact factor 1+eta^2 |

## Not formalized yet

- Identification of the derivatives of f(x,y)=xy through Lean's derivative APIs.
- General block-operator inverse and Hessian regularity estimates.
- Theorems 5.1, 5.2, 5.3, or 5.4 in their full published form.
- General projected/proximal domains or arbitrary matrix bilinear games.
- Empirical experiments, GAN applications, or an executable numerical solver.

The code does not introduce custom axioms or placeholders to bridge these gaps.
