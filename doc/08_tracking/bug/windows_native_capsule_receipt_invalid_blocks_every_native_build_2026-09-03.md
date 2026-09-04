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
