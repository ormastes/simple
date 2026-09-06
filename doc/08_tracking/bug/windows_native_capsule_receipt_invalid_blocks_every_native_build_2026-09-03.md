# No `native-build` invocation completes a binary on this Windows host (2026-09-03)

- **Status:** FIXED 2026-09-06 — root-caused and repaired in
  `src/compiler/80.driver/driver_aot_native_output.spl`. A three-line hello
  world now `native-build`s end to end on this Windows host and RUNS. Evidence
  and the exact remaining caveats are in "2026-09-06 resolution" below.
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

## 2026-09-06 resolution

### The premise had a NEW wall in front of it (re-measured, not assumed)

The deployed `bin/simple.exe` (2026-09-02) can no longer even reach the capsule
code: it dies at `parse: in ".../src/compiler/00.common/structural_contracts/
frontend_offload_switch.spl": function arguments: expected Comma, found Colon`.
That is the `auto`-as-named-arg-label defect
(`auto_keyword_rejected_as_named_argument_label_2026-09-05.md`), whose fix is in
the Rust seed SOURCE but not in the deployed binary; `656971284f3` then dropped
the positional-construction workaround, so the deployed seed cannot parse the
tree. Rebuilding the seed (`cargo build --release --bin simple`, MSVC env
sourced) clears it. Note `native-build` spawns its worker through
`resolve_simple_binary()`, which prefers `bin/simple.exe` — the fresh build only
takes effect with `SIMPLE_BINARY=<fresh seed>` set.

### Root cause: the receipt was never written, and the write reported success

Diagnostics were added first (item 1 of "What would unblock"), splitting the six
causes into named invariants. The very first run named it:

```
reason: native-capsule-receipt-invalid:build.laneF.hello:receipt-missing:
        build/native_cache\s14310ba542f20eb64d4390d12776cfa5\object.build.laneF.hello.o.capsule-receipt
```

`ls` confirmed: object present, receipt absent — while the producer's
`if not _sffi_file_write_text(receipt_path, receipt)` had NOT fired.

`_sffi_file_write_text` called `file_write_text`, imported as
`use std.file_system.{file_write_text, file_read_text}`.
`src/lib/nogc_sync_mut/file_system/file_ops.spl:60` is a **stub**: it rejects an
empty path or nil content and then `return true` — it never writes a byte.
The name is additionally ambiguous; the same run's own JIT warning says it:

> public function `file_write_text` has 3 co-compiled definitions with 2
> differing signatures ((text,text)->() vs (text,text)->bool); ... falling back
> to the last definition when types are ambiguous

Both variants take `(text, text)`, so arg-type matching cannot separate them and
the fallback picks whichever definition happens to be last. On this host it
landed on the stub. (The `(text,text)->()` sibling,
`src/lib/nogc_sync_mut/env/config.spl:235`, is no better on Windows — it shells
out to `/bin/sh -c "echo ... > path"`.) It was never a path-form, hash, or CRLF
problem.

### Fix (producer side; the validator was correct and was NOT weakened)

`src/compiler/80.driver/driver_aot_native_output.spl`:

1. `_sffi_file_write_text` / `_sffi_file_read_text` now call
   `file_write_exact` / `file_read_nullable` from `std.io_runtime` — both are
   single-definition names (a repo-wide census finds exactly one `fn` for each)
   backed by one direct `rt_file_write_text` / `rt_file_read_text` call, so they
   are real and unambiguous.
2. New `driver_native_capsule_result_reason_v1` returns `""` or the ONE failing
   invariant; `driver_native_capsule_result_valid_v1` is now
   `reason == ""`, and the verdict is
   `native-capsule-receipt-invalid:{module}:{reason}`. Every branch is the same
   fail-closed condition as before — nothing is accepted that was rejected.

### Verification transcript (2026-09-06, this host)

Seed: `src/compiler_rust/target/release/simple.exe`, rebuilt 14:19, 39,194,112 B.
(A first rebuild silently failed with `failed to remove file ... simple.exe:
Access is denied` — the known Windows locked-exe trap; the exe was moved aside
and rebuilt.)

| run | result |
|---|---|
| before fix | `native-capsule-receipt-invalid:...:receipt-missing:...` (rc 1) |
| after fix, no MSVC env | past codegen, past the capsule gate, dies at `error: LLVM native linking failed: No C compiler found` |
| after fix, MSVC env sourced | **rc 0**, `build/laneF/out/hello.exe` (1,183,744 B) produced, executed, printed `hi`, exit 0 |

The receipt now exists and is byte-correct (973 B, LF-only, `od -c` verified:
`native-capsule-result-v1\nnative-capsule-v1|17:build.laneF.hello|64:955f...`).
The `.cache_scope`, `phase.marker`, and `native-module-witness-shadow-v1.receipt`
files in the same directory also appear for the first time — they were being
silently no-op'd by the same stub.

### Not proven / still open

- **The stdlib stub itself is untouched.** `std.file_system.file_write_text`
  still returns `true` without writing, and `file_write_text` still has 3
  co-compiled definitions over 2 signatures. Every other caller of that import
  is silently no-op'ing on some hosts. This lane fixed only the capsule
  producer's import; the stub and the name collision need their own record.
  Same shape applies to `file_read_text`, `dir_create`, `dir_list`, `env_get`,
  `file_size`, `process_wait`, `shell` and ~10 more names the same run warns
  about.
- **Only a hello world was verified.** `native-build src/app/mcp/main.spl` was
  not run, so a running `simple_mcp_server.exe` is still unproven.
- **The deployed `bin/simple.exe` was NOT replaced** (other lanes hold it), so
  the fix requires the fresh seed plus `SIMPLE_BINARY` until a bootstrap
  redeploy lands.
- **No regression spec was added** for the capsule-reason split.
- The `main resolves to image base` defect did not appear on this fixture; it
  was neither reproduced nor cleared here.
- **Warm/cross-run reuse:** a second `native-build` of the same fixture over the
  now-populated cache also exits 0, so the cross-process receipt-validation path
  (`driver_aot_native_output.spl:~1097-1108`) does not reject the receipt. Whether
  it took a genuine cache HIT or silently recompiled was NOT distinguished — the
  worker log is truncated and carried no `cache_hit`/`native_cache` line.
