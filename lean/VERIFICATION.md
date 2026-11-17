# Verification record

Verified 2026-11-17 in a Linux cloud workspace.

- Lean: 4.19.0, commit `6caaee842e94`.
- mathlib: v4.19.0, commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- Command: `lake build`.
- Result: **passed**, exit code 0, no warnings in the final build.
- All seven modules and root CGO import target compile.
- `#print axioms CGO.objective_optimistic_converges` reports
  `[propext, Classical.choice, Quot.sound]`.
- The other included axiom audits report these same standard foundations.
- No `sorry`, `admit`, or custom `axiom` declarations in the Lean source.

The current full-iterate theorem is for fixed-step objective-derived optimistic
CGO under the README's explicit global regularity, root existence and all-root
Minty assumptions. It concludes stationarity. It is not certification of the
entire paper or its full variable-step statements.

Mathlib's dependency cache was used; some dependencies were also locally built.
No mathematical dependency source was modified. This is symbolic proof checking,
not merely numerical experimentation.

Official PMLR PDF SHA-256:
`081a4984e8126adecea5e593e48e832808b1bfaefc63d108e36226f281c621ee`.
Source: https://proceedings.mlr.press/v202/vyas23a/vyas23a.pdf.
The paper itself is linked, not redistributed.

Latest extension: all nine modules build successfully under the same pinned
Lean/mathlib versions. See replaced build.log. New main theorems print only
propext, Classical.choice, Quot.sound; no additional axioms or sorry were added.
