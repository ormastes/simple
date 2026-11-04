# Pure-Simple nested extern registration

Status: temporary workaround verified; authoritative bug DB reconciliation pending.

Bug ID: `pure_simple_nested_extern_registration_2026_10_12`.

The retained Phase2 producer `f2ce31b4e4dea1ea6ca3e8726cd411144914c24ffcf58722021f38c4b6393dec` rejects `ParallelConfig.default_config` in `src/compiler/00.common/parallel.spl`: its nested `extern fn rt_cpu_count()` is parsed, but the following call fails HIR lowering with unresolved name `rt_cpu_count`. The original failed module is retained as the reproducer; its failure was not rerun.

Moving the identical extern declaration to module scope preserves the call, return type, configuration values and runtime symbol. The private candidate produced a real 4,565-byte AMD64 COFF object, SHA256 `a10e1845962f32c10360747236f0362c8215963a563fc59050a6d01be4c23a84`. `llvm-nm` confirms an actual undefined external `rt_cpu_count` relocation; the test did not replace the CPU count with a constant.

Evidence: `build/native_probe/parallel-nested-extern-20261012-astra/`; patch SHA256 `603e82db1a39ea20f2403ef556b5fe207d566d9ae54de0c005fdae96b40418b3`; successful receipt SHA256 `b0f9f6296552fef76672fe4ac61405d9c1cf6001cb3a9591a07c197f892e5d26`.

Recovery reference: `50c8c89f6e476d1e0f3e7b2e1512e7db57a6bd06`, original nested declaration in the same source owner. Workaround commit: `0a9ecc244a6de194f9bd3bd8e34f9805d1337372` on local `release_phase3`. Remote landing remains subject to the user's Phase3 gate.

Permanent repair must register nested extern declarations at their intended lexical scope in pure-Simple HIR lowering. Check the Rust seed for the same behavior. Add prevention cases for nested extern calls in static methods and ordinary functions, identical declarations in separate scopes, and conflicting signatures. Before removal, apply the permanent repair, verify the original nested reproducer and these scope cases, then restore only this tagged declaration move. Fetching a purported repair alone does not authorize recovery.

This object check does not qualify runtime CPU discovery, linking, compiler-wide behavior, memory/performance, or full Phase3. No native codegen behavior changed in the workaround; its scope remains declaration registration only.

## release_phase3 port linkage (2026-10-19)

The original recovery reference `50c8c89f6e4` and workaround commit `0a9ecc244a6`
exist only in a local worktree. On the release_phase3 port (PR #3803) the
workaround commit is `657ca5c5fb55ec59f146a8946d710c79d1276def`, and the source tag
now uses `recover=0f7368cd97dca86e99379c5173a4c530d1d6f2c2`, its parent on that
branch, which still has the original nested declaration. A row was added to
`bug_db.sdn` by hand; qualified bug-database reconciliation remains pending.


## Scoped signature-conflict repair (2026-11-02)

Status: **OPEN** for the original lexical-scope requirement. This change repairs
conflicting signatures among already-visible nongeneric extern declarations;
it does not remove the `rt_cpu_count` declaration-hoisting workaround.

`parse_extern_fn_stmt_inline` previously ignored every later same-named
declaration. It now compares ordered parameter types and the return type and
reports `conflicting extern declaration: <name>` at the later declaration.
Identical signatures share one declaration regardless of parameter names.
An existing ordinary module function remains authoritative.

The existing `inline_extern_fn_registration_spec.spl` now contains 11 scenarios:
registration, unsafe attributes, repeated identical signatures, prior top-level
externs, ordinary-function twins, conflicting arity, first/later parameter type
conflicts, zero-argument return conflicts, identical composite signatures, and
conflicts with a prior top-level extern. The arity case pins the diagnostic
location to line 6, column 5. These assertions execute the real parser/bridge.

Astra reviewed the exact two-file patch and accepted it for landing with no
outstanding static findings. **This is not a runtime verification PASS.** The
authorized Windows Phase1 seed (`56664f6dbff85fd05a684c842d68fd16d96964e8f34953c4f2797df6c514c7f4`)
failed before test assertions while loading
`src/lib/nogc_sync_mut/io/windows_redirected_process.spl` with
`Unexpected token: expected Fn, found Colon`; alternate root probes could not
resolve the test tool or dependencies. Those initial attempts executed no test assertions.
Local attempt logs are retained in
`C:/dev/wt/p12-compiler-repairs/build/p12-extern-evidence/`.

Remaining acceptance: execute the 11 regression scenarios with a compatible
runner, then address lexical visibility, generic/effect metadata, and later
top-level declarations separately. Full HIR/native original-reproducer
qualification is still required before closing this broad bug or removing its
workaround. This patch claims neither Phase1 suite nor Phase2 qualification.


### Subsequent direct-owner diagnostic

A newer `seed_nilfix.exe` (SHA256
`fc56d4b5fc384ea93ed20befd4503ff6e27db7734214ca45e072b4df1b081828`)
executed the changed parser with **11 scenarios and 34 real assertions**, exit 0.
Each assertion panics on failure. Astra inspected the harness, actual log and
matching source hashes and accepted this scoped evidence. The producer lacks
an input admission receipt, so this is an **unadmitted Phase1-hosted diagnostic**,
not standard SSpec or Phase2 qualification. The standard test command remained
blocked before scenarios by unavailable/incomplete runner dependencies.

The reproducible harness is
`test/fixtures/compiler/inline_extern_signature_direct/main.spl`.
The complete log and identity receipt are in
`doc/08_tracking/bug/evidence/nested_extern_signatures_2026_11_02/`.
Run the harness with the named seed using `run <harness> --mode=interpreter`
against the recorded parser source. The broader issue and workaround remain
open under the acceptance criteria above.

## Nested extern declaration identity and location (2026-11-03)

The inline declaration parser now uses the same `declaration_identifier_text`
owner as top-level extern declarations. A contextual keyword such as `match`
can therefore name an extern declaration in either position. Previously the
inline path required an IDENT token even though the top-level path accepted
contextual keyword names.

Newly registered nested externs also retain their actual declaration start,
end, line and column instead of span ID zero. The existing bridge already uses
that span for `ParserFunction` and its parameter declarations. Repeated
compatible declarations leave the first declaration and its span unchanged.
The signature-conflict diagnostic still points to the later declaration.

Four parser regression scenarios cover ordinary functions, static methods,
repeated declarations and contextual keyword parity. They supplement the 11
existing registration/signature scenarios without claiming lexical isolation.

**TEST_BLOCKED:** no qualified self-hosted CLI is available in this Windows
repair lane. The new scenarios have not executed; source review and whitespace
checks are not behavioral qualification. Execute the complete 15-scenario
`test/01_unit/compiler/frontend/inline_extern_fn_registration_spec.spl` using an
admitted producer, then perform the required compiler/library/MCP checks before
admission. The broader lexical-scope, generic/effect metadata and later
module-declaration requirements remain OPEN. The `rt_cpu_count` hoisting
workaround remains in place.

## c28-w2 triage 2026-11-04: fix landed, verification pending

PR #6369 (084fca5abf4) and #5958 (c78f0b004f5) landed the parser-side
nested-extern registration and conflicting-signature diagnostic with spec
`test/01_unit/compiler/frontend/inline_extern_fn_registration_spec.spl`
(15 scenarios). The `rt_cpu_count` module-scope hoist in
`src/compiler/00.common/parallel.spl:15` is KEPT. Status:
fix-implemented-verification-pending. Stage3 repro: run the 15-scenario spec
with a stage3 CLI, then restore the nested declaration in
`ParallelConfig.default_config` and native-build `parallel.spl`; success is a
COFF/ELF object with an undefined `rt_cpu_count` and no HIR "unresolved name".
