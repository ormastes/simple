# `native-capsule-receipt-invalid` blocks EVERY native-build on this Windows host (2026-09-03)

- **Status:** OPEN — filed from the module-global lowering lane, not fixed there.
- **Severity:** blocking for any Windows `native-build` deliverable. It is the
  reason the MCP lane cannot yet show a running `simple_mcp_server.exe`, once
  the MIR defect in front of it was cleared.
- **Scope:** not program-specific. A three-line hello world reproduces it.

## Symptom

```
$ bin/simple.exe native-build -o /tmp/hello.exe /tmp/hello.spl
...
ERROR: 1 unit(s)
  - C_.Users.ormas.AppData.Local.Temp.claude.fx.hello
      reason: native-capsule-receipt-invalid:C_.Users.ormas.AppData.Local.Temp.claude.fx.hello
```

Exit 1, no artifact produced. The failure is AFTER MIR, AFTER LLVM codegen and
AFTER `llc` — those all succeed; the build is rejected at the owner-only
authenticated cache checkpoint.

## Where

`src/compiler/80.driver/driver_aot_native_output.spl`

- `driver_native_collect_capsule_result_v1` returns
  `"native-capsule-receipt-invalid:{module_name}"` (line ~392) when
  `driver_native_capsule_result_valid_v1(capsule)` is false.
- That predicate fails closed on any of: identity invalid, object file missing,
  cache-source identity mismatch, **`<object_path>.capsule-receipt` missing**,
  object fingerprint unavailable, or receipt content not byte-equal to
  `"native-capsule-result-v1\n{capsule_identity}\n{object_path}\n{size}\n{content_hash}\n"`.

Which of those six conditions fires here has NOT been isolated — the verdict
string is the same for all of them, which is itself part of the problem: the
message names the module, never the failed invariant.

## Evidence that it is program-independent

| fixture | module globals | verdict |
|---|---|---|
| `hello.spl` (3 lines, `print` + `0`) | none | `native-capsule-receipt-invalid` |
| `vstr.spl` (`var G_S: text`) | 1 | `native-capsule-receipt-invalid` |
| `varr.spl` (`var G_ARR: [i64]`) | 1 | `native-capsule-receipt-invalid` |
| `gvar.spl` (`var G_DICT: Dict<text,i64>`) | 1 | `native-capsule-receipt-invalid` |

The hello-world control is load-bearing: it has no module-level binding at all,
so none of the MIR module-global code paths touched by commit
`fix(mir): mirror module statics into global_statics_by_id` execute for it. This
blocker is independent of, and pre-existing relative to, that fix.

Deleting `.simple/native_cache` and `.simple/native-objects-*`, and running with
a fresh `SIMPLE_CACHE_SCOPE`, did not change the verdict — so it is not simply a
stale cache entry.

## Likely direction (unverified)

Windows path handling around the object/receipt pair is the first place to look.
This host already carries
`doc/08_tracking/bug/windows_bootstrap_max_path_262_2026-08-30.md`, and the
scope-directory derivation in the same file documents at length that NTFS
forbids `:` in a path component while the raw cache key always contains one. A
receipt written to, or read back from, a path that Windows rejects or truncates
would produce exactly this fail-closed verdict.

## What would unblock

1. Make the verdict name the invariant that failed (missing receipt vs content
   mismatch vs missing object vs fingerprint failure). Six causes behind one
   string is why this record cannot say which one it is.
2. Then fix the named one.

## Consequence for the MCP lane

`native-build src/app/mcp/main.spl` can no longer be blocked by
"assignment target has no local binding" (fixed 2026-09-03), but a running
`simple_mcp_server.exe` on Windows still requires this gate to pass. The
interpreted MCP server (`bin/simple run src/app/mcp/main.spl`) is unaffected and
continues to answer real MCP protocol.
