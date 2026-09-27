# RC1 macOS Stage 3 callable dependency ambiguity

**Status:** Fix under admission. **Platform:** `aarch64-apple-darwin`.

On RC1 commit `482266d0871`, the full Stage 2 compiler passed sanity and was
admitted. The canonical Stage 3 resume created its memory snapshot with the
required `run_id` and 25 fields, passing the earlier snapshot-open failure.
HIR then reported thousands of `ambiguous explicit callable dependency`
errors. The first was `AsmTargetSpec` in `compiler.hir.hir_definitions` while
lowering `src/compiler/driver/driver.spl`; other early errors named `Span`,
`CompilerDriver`, and `Closure`. The build was stopped after source 57/717 as
the failing process passed 7 GB RSS on a 24 GB host.

The RC1 dependency sweep considered explicit named imports and wildcard
routes at the same rank. It also compared re-export facade indices before
canonicalizing them to the terminal declaration. The existing imports in
`hir_definitions.spl` include a named `AsmTargetSpec` alongside a wildcard
route, exposing this mismatch. `main` already contains the focused resolution
in `ffcd929a5e8`; the RC1 branch backports canonical candidate resolution and
named-over-glob precedence, with a direct sweep regression fixture.

Next gate: rebuild and admit Stage 2 on the fixed commit, then resume Stage 3
from its path-bound receipt. The fix is not admitted by this report alone.
