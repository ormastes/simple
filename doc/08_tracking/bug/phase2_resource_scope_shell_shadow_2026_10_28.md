# Cached phase2 resolves the resource-scope shell local as a function

Canonical ID: `phase2_resource_scope_shell_shadow_2026_10_28`
Status: FIX IMPLEMENTED, VERIFICATION PENDING (T0 hosted); source workaround
still active pending original-name native retirement; authoritative DB row
updated 2026-11-09.
Owner: compiler local-name/function-value resolution; next admitted compiler rebuild.

After PR #5170 repaired capture pointer/length transport, the native runner still
failed every bounded child launch. LLDB on the existing phase2-built runner showed
`rt_process_run_bounded_tuple` receiving ARM64 instruction bytes as its command.
The stack passed through `_run_with_unix_limits` and `_legacy_process_fallback`.
The local `shell` binding collides with a global function name in this producer.

Evidence: `/tmp/test-runner-refresh-20261028/child-launch.lldb.log` and
`qualification-patched/`. Original source recovery: `74c4f7c879b`.
Producer: existing `stage2-simple-aliasfix` under
`/Users/ormastes/wt/release-phase2-review/build/verify/pure-spl-aliasfix-p2-20261025-02/`.
The compiler is intentionally not rebuilt in this task.

Workaround: rename the `_run_with_unix_limits` local to `limit_shell_path`
and the `_limit_shell` loop local to `candidate_shell_path`. The first native
probe proved the neighboring loop collision as well: no-pid-cap children passed,
but the pid-capped child incorrectly reported that no supported shell existed.
The host has `/bin/bash`; the renamed loop must return that executable.
Its tagged source and this report are committed before native qualification;
the workaround commit is discoverable with `git log -S phase2_resource_scope_shell_shadow_2026_10_28`.
Retirement requires a new admitted producer and an original-name reproducer that
executes real scoped children. A source rename does not fix the compiler.

Prevention: the native capture fixture now covers the runner's scope entry,
pid-capped and ordinary POSIX shells, empty/spaced/quoted/UTF-8 arguments,
stdout/stderr, child exit 7, missing executable, and timeout classification.
The standalone gate verifies all 11 named cases independently of runner status.
Native runner acceptance uses positive, negative and empty BDD, SSpec, plain SPL,
Markdown and source-comment fixtures; all receipts are retained separately.

## Native qualification

Workaround commits: `9fd8fc597a6` (call site) and `75a52c487ae` (selector).
Qualified source: `75a52c487aefa57e0a5a6fc9bd7cda103a40fec4`.
Producer SHA256: `0d6f2e4720845195c9f91de292056fac4c57cabef81390507c78d95e51133a28`.
The phase2 compiler was not rebuilt. The initial sparse-checkout link failure
(missing counterpart header) and call-site-only 10/11 result remain retained.
After both renames, all 11 native regression cases pass. Probe SHA256:
`ddd6e27f108367b6b2ee10b0de6b18771aa4a88fb7d62b963b97d28669ae2277`.
Luna reviewed the exact source commit without findings.

The native runner built in 195 seconds, peak observed process-tree RSS
7,439,824 KiB, quiescent completion, SHA256:
`ea9972bd35a2023594baa24c2a4e6d37c90dd3702bb8e44c46951e4c3b62b501`.
Receipts and immutable fixture copies/hashes:
`/tmp/runner-limit-shell-evidence-20261028/` (`scope-build.status`,
`scope-check.stdout`, `runner-build.status`, `runner-build.rss.env`,
`qualification-patched/identity.json`, `qualification-patched/rows.json`).
Its 24 positive/negative/empty invocations used the retained Phase1 child;
this mixed-producer run is diagnostic, not phase2 child admission.

Markdown returns expected exits 0/1/1 and pass/fail/no-block results. The four
source-documentation forms (`#`, `##`, `///`, docstring) each produce expected
doctest subresults: green 1 passed, red 1 failed, empty rejected. Standalone
snippets use conditional `panic` assertions; the earlier raw `assert` inputs
were invalid under the retained child and remain preserved in the prior folder.

The normal file route still reports `Resource limit exceeded ()` for BDD,
SSpec, plain SPL and source-comment files, after successfully launching the
child. All 21 non-Markdown commands therefore return 1. Some show the existing
MC/DC compile fallback diagnostic (`struct i64 has no field recorder`). No
positive BDD/SSpec/plain-SPL acceptance or whole comment-command success is
claimed. See `phase2_runner_empty_limit_classification_2026_10_28.md` for the
next blocker. Do not promote this candidate or mark the compiler defect fixed.

## Source-to-HIR prevention (2026-11-08)

`test/01_unit/compiler/20.hir/bootstrap_regressions/local_shadows_function_name_spec.spl`
pins that HIR lowering binds a local (`val shell`, `for shell`, imported-function
shadow) to its own symbol, never the same-named function. 3/3 GREEN on the seed
interpreter, so the defect is NOT in source-to-HIR name binding; it lies in the
cached phase2 producer's later stage (MIR/codegen function-value resolution).
Status unchanged: still open pending an admitted producer rebuild.

MIR extension (2026-11-08): the same fixtures lowered through `MirLowering` emit zero
function-value casts naming `shell` inside the shadowing functions (5/5 spec GREEN on
the seed). Current source (`find_local` before `try_lower_function_value`) is correct
through MIR; the defect is specific to the cached phase2 producer build. Native-build
was not run (single-shard s3 path has an open heap-corruption crash).

## 2026-11-09 — resolved-disappeared (native)
Native re-run 2026-11-09 with the current self-hosted stage2 `C:/dev/p3new/stage2new/stage2_new4.exe` (`native-build --entry-closure`, llvm, x86_64-pc-windows-gnu, core-c-bootstrap, SIMPLE_HIR_CACHE=0, clean sparse worktree of origin/release/1.0.0 @1cc167e37fd): original-name reproducer (`test/fixtures/compiler/phase2_native_repro/shell_shadow.spl`: global `fn shell`, a `for shell in candidates` loop local and a `val shell = ...` local in a limit-shaped helper) runs correctly: `RESULT rc=0 stdout=[a=/bin/bash#3|PASS shell shadow]`. The source workaround renames (`limit_shell_path`, `candidate_shell_path`) may now be retired in a separate change.

## Fix verification — 2026-11-09 (T0 hosted)

No compiler source change was required: both owners are already correct at
HEAD (`4648b81b549`):

- Pure-Simple compiler: HIR lowering binds every in-scope `shell` reference
  to the local's own symbol (spec 3/3 green), and MIR lowering consults
  `find_local` before `try_lower_function_value` in every Var/NamedVar
  dispatch and function-value path (`expr_dispatch.spl`, pre-dispatch arms and
  `case Var`/`case NamedVar`), so a bound local can never fall through to the
  same-named function (spec 5/5 green; native re-run above green).
- Seed interpreter: `evaluate_call` (src/compiler_rust/compiler/src/
  interpreter_call/mod.rs) previously reached Priority-4 import binding /
  Priority-5 flat `functions` map before any block-scope binding, so a
  function-typed block local called as a callee dispatched to the same-named
  module-level function — the exact "local resolves as function" failure.
  Fixed by `7a60d8bb19f` (2026-11-06, "fn-valued locals shadow imported
  functions", Priority 3.9 lexical callable locals). The released seed binary
  (`release100-7a0e6fe516f-20261031`) predates that commit.

Evidence (T0 hosted probes, cwd = worktree):

- `bin/simple run test/fixtures/compiler/phase2_native_repro/shell_shadow.spl
  --mode=interpreter` and without `--mode=interpreter`: `a=/bin/bash#3`,
  `PASS shell shadow`, rc=0 (seed provenance: Rust bootstrap seed
  `release100-7a0e6fe516f-20261031`).
- New regression spec
  `test/01_unit/interpreter/resource_scope_shell_shadow_runtime_spec.spl`
  (6 examples: val-local as command text at module-fn scope and inside a spec
  block closure, for-loop local, bare-local branch, global still callable by
  name inside a spec block, function-typed local as callee):
  - current sources (seed rebuilt from this tree): 6/6 GREEN,
    `SPEC FILE VERDICT ... outcome=OK ... passed=6 failed=0`;
  - released pre-fix seed: 5/6, the callee case fails with the local
    resolving to the module-level function (`expected ran:ls to equal
    local:ls`) — the tracked defect class, caught by the new spec.
- `simple test <spec> --mode=interpreter` is not usable on this host
  (pre-existing: light daemon requires Linux /proc on macOS, then a
  `byte_len` semantic error in the runner on every spec, including previously
  green ones); the spec was executed via `simple run`, which drives the same
  spec harness and prints the standard SPEC FILE VERDICT line.

Honest limits:

- Verification tier is T0 hosted only; the native lane was not re-run in this
  change (prior native re-run above stands).
- The `resource_scope.spl` workaround renames remain in place; retirement is
  a separate change with its own native regression.
- Adjacent, out-of-scope gap observed while probing: inside a spec module, a
  bare-identifier VALUE read of a top-level function loses to a
  transitively-imported std function of the same name (module-global
  preference on the identifier-read path), while the callee ladder binds the
  module's own definition. Not the local-vs-function defect this bug tracks;
  no spec pins it here.
