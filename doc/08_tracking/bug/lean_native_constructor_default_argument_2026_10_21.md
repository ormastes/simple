# Imported constructor-expression default blocks Lean bootstrap owner

- Canonical ID: `lean_native_constructor_default_argument_2026_10_21`
- Status: OPEN; source workaround active. Bug DB reconciliation pending because
  the available exact compiler is bootstrap-only, not a qualified full CLI.
- Original source/recovery commit: `0bfa8039acd`.
- Owner: imported default-expression lowering in the bootstrap producer;
  `src/plugins/backend_lean/lean_backend.spl:769` is the affected consumer.
- Evidence predates workaround: parent Phase 2 terminal native-build log
  `.simple/storage/build/bootstrap/logs/x86_64-pc-windows-msvc/stage2-native-build.log`
  recorded `compiled=1431 reused=0 failed=5`, including `lean_backend.spl`:
  `call to lean_plan_type_declarations omits argument 3 whose default is not a
  call-site constant; a cross-module/native call cannot evaluate it`.
- Producer: parent's immutable
  `stage3/x86_64-pc-windows-msvc/stage2-runtime-authority/simple.exe`; exact hash
  and focused command/results are recorded below after diagnostic execution.

`lean_plan_type_declarations` declares argument 3 as
`LeanRecursiveArrayLimitsV1()`. Its defaults are depth 128, nodes 65536, work
1048576, key bytes 1048576, plans 4096. The workaround passes that exact
constructor explicitly; it neither changes policy budgets nor removes the
public default. The missing grammar capability stays open rather than being
normalized into a requirement for all callers to spell defaults explicitly.

The immediately preceding source annotation links this record. The workaround
commit is the Git commit containing this record and that annotation. Retirement
requires a compiler-owner fix plus successful native execution of the original
omitted form against the corrected producer; do not remove the default API.
Related historical diagnosis: `seed_cross_module_selfless_method_drops_receiver_2026-09-26.md`,
section "Still open".

Focused native fixtures in `test/fixtures/compiler/lean_constructor_default_native/`:
`omitted.spl` preserves the failing cross-module constructor-default call;
`explicit.spl` checks the exact five default values, a distinct explicit policy,
and an ordinary imported literal default. They are bootstrap diagnostics, not
SSpec/product-suite or full Lean export qualification. Parent owns the real
Lean module rebuild with retained compatible objects.

Provider usage: input/output/cache-read/cache-create tokens unavailable;
comparable cohort average unavailable; ratio unavailable. No zero-filled or
guessed usage values. Runtime bug-database reconciliation remains pending.

## Focused evidence

2026-10-21 bootstrap-focused execution, exact producer SHA256:
`32014b3401e3cb76aec44acb475a22f2385fefcd1d19ab71049e52d633356825`.
No product-suite seed fallback or production PASS is claimed.

The fixture sources were copied unchanged into a tiny private Git checkout at
`build/lean-default-diagnostic/tiny/src/` and committed there to bind source
authority. Both attempts used the canonical
`scripts/setup/windows-msvc-bootstrap-env.shs`, LLVM 23.1.1/clang-cl, target
`x86_64-pc-windows-msvc`, the frozen producer's adjacent runtime path, private
HOME/TEMP/runtime-object/native caches, and these native-build options:

```text
native-build --backend llvm --runtime-bundle core-c-bootstrap --source src
--entry-closure --threads 1 --cache-dir <tiny>/<entry>-cache --mode one-binary
--target x86_64-pc-windows-msvc --runtime-path <frozen-stage2-runtime-authority>
--entry src/<entry>.spl -o <tiny>/<entry>.exe
```

- Negative `omitted`: exit 1, one failed file; exact diagnostic:
  `call to policy_signature omits argument 1 whose default is not a call-site
  constant; a cross-module/native call cannot evaluate it`.
  Retained `build/lean-default-diagnostic/tiny/omitted.log`.
- Positive `explicit`: exit 0, `2 compiled, 0 cached, 0 failed`, linked 277 KB.
  Output executable exited 0 and printed exactly
  `PASS lean constructor default: 3 checks` (all five default fields, all five
  explicit overrides, imported literal default). Retained `explicit.log` and
  `run.log` in the same private directory.
- Actual Lean source review: the consumer now passes the exact declaration's
  `LeanRecursiveArrayLimitsV1()` and leaves its API/default budgets untouched.
  Full Lean owner native rebuild remains the parent's retained-object gate.

An earlier full-worktree cold SCV attempt was not native evidence: it held its
own `build/scv/compile-events/refresh.lock.lock`, had no child processes or
published journal, consumed over 200 CPU seconds and roughly 1 GB RSS without
reaching the fixture, and was bounded at 300 seconds. Its first invocation had
already refused `compile-event-journal-missing`; cold-init was private only.
The attempted `--emit-object` option is unsupported by this seed and is absent
from both successful scoped native commands above. This full-checkout startup
performance issue remains unqualified; tiny-checkout negative/positive builds
completed in seconds. No canonical parent cache was modified.
