# No `native-build` invocation completes a binary on this Windows host (2026-09-03)

- **Status:** OPEN — filed from the module-global MIR lowering lane, not fixed
  there.
- **Severity:** blocking for any Windows `native-build` deliverable. It is why
  the MCP lane cannot yet show a running `simple_mcp_server.exe` even after the
  MIR defect in front of it was cleared.
- **Scope:** not program-specific. A three-line hello world reproduces it under
  every invocation tried.
- **Related:** `native_build_requires_simple_bootstrap_env_windows_2026-09-03.md`
  (the invocation-form half of the same wall).

## What was measured

`bin/simple.exe` (the Rust seed) in `C:\Users\ormas\dev\simple`, fixture
`hello.spl` = `fn main() -> i64: print "hi"; 0`:

| invocation | how far it gets | verdict |
|---|---|---|
| bare `native-build` | past MIR, past LLVM codegen, past `llc` | `native-capsule-receipt-invalid:<module>` |
| `SIMPLE_BOOTSTRAP=1` | `[llvm-tools] llc-object`, `read-bytes` | `[cc-detect] no C compiler verified on Windows` |
| `SIMPLE_BOOTSTRAP=1` + sourced `scripts/setup/windows-msvc-bootstrap-env.shs` | `[llvm-tools] llc-object`, `read-bytes` | `worker exited with code 1`, no artifact |

No invocation produces an executable. The same three verdicts appear for
fixtures that DO have module globals (`var G_S: text`, `var G_ARR: [i64]`,
`var G_DICT: Dict<text,i64>`), so this is downstream of anything program-shaped.

The hello-world control is load-bearing: it has no module-level binding at all,
so none of the MIR module-global code paths touched by
`e29d4a2aceb fix(mir): mirror module statics into global_statics_by_id` execute
for it. This wall is independent of, and pre-existing relative to, that fix.

## The bare-invocation half: `native-capsule-receipt-invalid`

`src/compiler/80.driver/driver_aot_native_output.spl`

- `driver_native_collect_capsule_result_v1` returns
  `"native-capsule-receipt-invalid:{module_name}"` (line ~392) when
  `driver_native_capsule_result_valid_v1(capsule)` is false.
- That predicate fails closed on any of SIX conditions: identity invalid, object
  file missing, cache-source identity mismatch, `<object_path>.capsule-receipt`
  missing, object fingerprint unavailable, or receipt content not byte-equal to
  `"native-capsule-result-v1\n{capsule_identity}\n{object_path}\n{size}\n{content_hash}\n"`.

Which one fires has NOT been isolated, and that is itself a defect: **six causes
share one verdict string**, which names the module and never the failed
invariant. Deleting `.simple/native_cache` and `.simple/native-objects-*`, and
running with a fresh `SIMPLE_CACHE_SCOPE`, did not change it — so it is not a
stale cache entry.

Windows path handling is the first place to look. This host already carries
`windows_bootstrap_max_path_262_2026-08-30.md`, and the scope-directory
derivation in the same source file documents at length that NTFS forbids `:` in
a path component while the raw cache key always contains one.

## What would unblock

1. Make the capsule verdict name the invariant that failed. Six causes behind
   one string is why this record cannot say which one it is.
2. Separately, resolve the post-`llc` failure on the `SIMPLE_BOOTSTRAP=1` lane
   (that half is the Windows linker/CC lane's, see the related record).

## Consequence for the MCP lane

`native-build src/app/mcp/main.spl` can no longer be blocked by
"assignment target has no local binding" (fixed 2026-09-03, `e29d4a2aceb`), but
a running `simple_mcp_server.exe` on Windows still requires this wall to come
down. The interpreted MCP server (`bin/simple run src/app/mcp/main.spl`) is
unaffected and continues to answer real MCP protocol.

## NOT Windows-specific — reproduced on aarch64 Linux (2026-09-06)

The title and scope above name Windows. The same verdict reproduces on this
aarch64 Linux host with the Rust seed
(`bin/release/aarch64-unknown-linux-gnu/simple`), at `4699194f81e`, on the
gate's own in-tree fixture:

```
simple native-build --backend cranelift --runtime-bundle core-c-bootstrap \
  --entry-closure --mode one-binary --threads 1 --cache-dir <tmp> \
  --entry scripts/check/cert/redeploy_gate/fixtures/hello_world.spl --output <tmp>/hw.bin
-> rc=1
   [cranelift-direct] emit /tmp/simple_cranelift_scripts.check.cert.redeploy_gate.fixtures.hello_world.o
   ERROR: 1 unit(s)
     - scripts.check.cert.redeploy_gate.fixtures.hello_world
         reason: native-capsule-receipt-invalid:scripts.check.cert.redeploy_gate.fixtures.hello_world
```

Same shape as the Windows bare-invocation row: codegen completes and the object
file is emitted, then `driver_native_capsule_result_v1_valid`
(`80.driver/driver_aot_native_output.spl:365-376`) rejects the receipt. Dropping
`--entry-closure`, and building an out-of-tree `/tmp` fixture, both give the
identical verdict. So the backend is not the variable either — Windows was LLVM,
this is cranelift-direct.

**Not a shared-`/tmp` race, ruled out by measurement.** The emitted object is
`/tmp/simple_cranelift_<module>.o` — module name only, no pid or session
component — so on a multi-session box a concurrent build of the same fixture
could plausibly overwrite it between emit and the fingerprint check. It does
not: the first reproduction on this host used an out-of-tree `/tmp` fixture
whose module name (`.tmp.claude_1000._home_yoon_dev_simple.<session-uuid>.
scratchpad.hw.hw`) is unique to one session, hence a unique object path, and it
failed with `native-capsule-receipt-invalid` identically.

This is what `scripts/check/check-stage2-hello-world-native-build.shs` fails on
when the candidate is the **Rust seed** on this host:

```
FAIL — 2 case(s) checked, simple:entry-form:fail(build exited 1)
```

Scope that verdict carefully — it is candidate-specific, not tree-specific:

- Seed candidate (`bin/simple`): FAIL, cause `native-capsule-receipt-invalid`.
  Identical before and after the unrelated `llm_caret` hyphen-duplicate cleanup
  of 2026-09-06.
- Stage-2 candidate
  (`build/bootstrap/stage2/aarch64-unknown-linux-gnu/simple`): **PASS — 2
  case(s) checked**, on the cleaned tree *and* on the still-uncleaned main
  worktree.

So this gate is not evidence about the hyphen/underscore collision in either
direction. That defect only fires on the `--entry` form without
`--entry-closure`, which this gate never uses; its guard is in
`80.driver/driver_source_loading.spl:253` and emits a wholly different message,
which appears **zero** times in any build log on this host. See
`native_build_blocked_by_hyphen_underscore_module_collisions_2026-07-28.md`.
