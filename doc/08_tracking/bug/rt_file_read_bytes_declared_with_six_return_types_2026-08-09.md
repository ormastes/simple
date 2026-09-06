# `rt_file_read_bytes` extern declared with SIX incompatible return types

- **Filed:** 2026-08-09 (stream I3)
- **Status:** PARTIALLY CONVERGED — six return types reduced to four. Guard spec
  landed intentionally RED on the remainder.
- **Guard:** `test/01_unit/compiler/extern/rt_file_read_bytes_single_extern_signature_spec.spl`
- **Layer above (already done, do not redo):** stream G2, commit `47adbf730ca`,
  `doc/08_tracking/bug/file_read_bytes_has_six_definitions_with_three_return_types_2026-08-09.md`

## The defect

`rt_file_read_bytes` is an `extern`, so every module that wants it re-declares
it locally. At `HEAD` on 2026-08-09 there were **93 such declarations across six
mutually incompatible return types**. The compiler resolves an extern by NAME,
so which declaration a module sees depends on its import closure. A caller can
silently start decoding a different element width because an UNRELATED module
entered the closure — and nothing at the call site changes.

The runner corroborates this independently; every spec run in this tree prints:

```
warning: public function `file_read_bytes` has 2 co-compiled definitions with 2
differing signatures ((text)->[i64] vs (text)->[u8]); JIT call sites resolve by
exact arg-type match ... falling back to the last definition when types are
ambiguous — a fallback hit may still dispatch to the wrong one.
```

### The 93 sites at HEAD, by return type

| return type | count | verdict |
|---|---|---|
| `[u8]` | 65 | **authoritative** — matches the C ABI |
| `[u8]?` | 23 | invents an absence path the ABI does not have; harmless in practice (`?? []` is identity on a bare array) but it is a second signature |
| `[i64]?` | 2 | element-width disagreement: 8-byte decode of a 1-byte-element array |
| `[i64]` | 1 | same |
| `List<i32>` | 1 | same, 4-byte — **FIXED** |
| `i64` | 1 | raw tagged handle, no array decode at all — **FIXED** |

(Two further occurrences in `test/*/sffi/rsa_sha512_reference_import_spec.spl`
are inside a string literal — a source fixture the spec compiles at runtime —
and are correctly excluded by the anchored scan.)

The filed count of "47" was a `src/`-only measurement. `src/` alone holds 44;
the repo-wide figure against `HEAD` is 93. Measured with an anchored
`/usr/bin/grep` against `HEAD` (`git grep`), not the dirty working tree — the
working tree carries other sessions' uncommitted declarations and reads 102.

## The authoritative signature

**The C runtime is the authority, not agreement between the declarations.**
`src/runtime/runtime_native.c:9071`:

```c
int64_t rt_file_read_bytes(const uint8_t* path_ptr, uint64_t path_len) {
    ...
    SplArray* result = rt_byte_array_new_len((uint64_t)file_len);
    ...
    return (int64_t)(uintptr_t)result;   // 0 on every failure path
}
```

It returns a tagged pointer to an array built by `rt_byte_array_new_len` —
**one-byte elements** — or `0` on failure. The interpreter binding
(`src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:546`) returns a
bare `Value::Array` on success and `Value::Nil` on failure, and its own doc
comment is explicit that this is *not* `Option::Some`/`None` — the Option wrap
was removed as a landmine in `fec74762272`
(`native_build_fresh_seed_optionwrap_landmine_2026-07-18.md`).

So the one correct declaration is:

```
extern fn rt_file_read_bytes(path: text) -> [u8]
```

## What converged

Caller audit first, per the standing rule that deleting a declaration REROUTES
rather than deduplicates.

1. **`src/compiler_rust/lib/std/src/sys/sffi/io.spl:15` — `-> i64` — REMOVED.**
   Zero uses in-file (the module declares it and never calls it) and **zero
   importers of the module anywhere in the repo**. It could therefore only ever
   poison an unrelated module's import closure with a sixth, wrong shape. A
   comment in its place records the ABI and points here.
2. **`src/compiler_rust/lib/std/src/infra/file_io.spl:69` — `List<i32>` → `[u8]`.**
   Its only consumers are the two wrappers in the same file (`read_bytes`,
   `read_bytes_unsafe`); a repo-wide grep found no importer of either symbol, so
   both wrapper signatures moved to `[u8]` with the decl. No caller loses a nil
   path — the shape was never optional.

Six return types → four.

## What did NOT converge, and why

- **`[i64]` / `[i64]?` (3 sites):** `src/lib/nogc_sync_mut/io/file_ops.spl:7`,
  `src/lib/nogc_sync_mut/sfm/container.spl:15`,
  `src/lib/nogc_sync_mut/io/telnet_serial_bridge.spl:31`. These are **deliberate**
  divergences with written rationale. `container.spl`'s header states outright:
  *"We do NOT redeclare the extern as `->[u8]` (that triggers the known SFFI
  signature-conflict hazard)."* Their callers are written to i64-element
  semantics — `container.spl` pre-sizes and index-pokes `raw[i] & 0xff` into a
  `[u8]`, and `cache_validator.spl` has a dedicated `cache_i64_slice_to_u8`
  helper for `file_ops`' wrapper. Converging the decl means converging those
  callers and the `std.io_runtime` / `std.nogc_sync_mut.io.file_ops`
  wrapper-level split that G2 already found hazardous. Out of scope for a
  declaration-layer change; tracked by the RED guard.
- **`[u8]?` (23 sites):** a nil-handling difference, not a width difference. The
  ABI has no absence value beyond `0`/`Nil`, and `?? []` is identity on a bare
  array, so these are *behaviourally* safe today. They are still a second
  signature and still make closure-dependent resolution possible. Converging
  them is 23 files of caller-visible churn with no defect to point at, so it is
  tracked rather than done blind.

## Guard and sabotage proof

`test/01_unit/compiler/extern/rt_file_read_bytes_single_extern_signature_spec.spl`
asserts the whole-repo property (exactly one return type, and it is `[u8]`)
rather than trusting `SIMPLE_DIAG_SAME_SIGNATURE_COLLISION=1`, which reports
only the pair that collided in one particular closure and therefore
UNDERSTATES the problem.

Baseline, intentionally RED on one example:

```
declared>=7 executed=7 passed=6 failed=1 dropped=0
✗ declares exactly one return type repo-wide -- expected 4 to equal 1
```

Sabotage: adding one file containing a `List<i32>` and an `i64` declaration:

```
declared>=7 executed=7 passed=4 failed=3 dropped=0
✗ no module declares the raw i64 handle form    -- expected 1 to equal 0
✗ no module declares a List<i32> element width  -- expected 1 to equal 0
✗ declares exactly one return type repo-wide    -- expected 6 to equal 1
```

Both convergence guards fired and the type count moved 4 → 6, so the oracle is
proven able to fail rather than failing open.

**Do NOT make this spec green by relaxing the assertion, widening the accepted
set, deleting the example, or marking it pending.** Converge the declarations.

## Measurement trap hit while doing this

A recursive `/usr/bin/grep` from the repo root walks `build/`, `.git/`, and
`src/compiler_rust/target/`, does not finish inside 120s, and **a timed-out grep
returns empty output, which reads as "no declarations, all clean"**. The guard
spec therefore names its four scan roots explicitly and carries a comment
forbidding a widening to `.` without re-checking wall time.

---

## Re-verification 2026-08-17 (io lane) — STILL LIVE; 4 distinct return types remain

Content classification (`/usr/bin/grep -rn "rt_file_read_bytes" src/ --include=*.spl`,
declaration sites only). The divergence is smaller than the filed six but is
not closed:

| return type | sites (examples) |
|---|---|
| `-> [u8]`   | `src/lib/nogc_sync_mut/io_runtime.spl:26`, `ffi/io.spl:40`, `sffi/io.spl:40`, `sffi/package.spl:7`, `archive/zip_{reader,writer}.spl:17`, `common/encoding/font_registry.spl:20`, `compiler/70.backend/linker/smf_source.spl:7`, `compiler/80.driver/shb/shb_reader.spl:415`, `compiler_rust/lib/std/src/infra/file_io.spl:78` (+ ~15 more in `src/os`, `src/app`) |
| `-> [u8]?`  | `src/lib/nogc_sync_mut/fs.spl:625`, `nogc_async_mut/fs.spl:625`, `gc_async_mut/gpu/browser_engine/browser_file_ops.spl:4`, `os/port/sqlite/sqlite_vfs_impl.spl:71`, `app/startup/launch_meta_check.spl:33`, `app/editor/editor_controller.spl:47`, `app/editor/mcp_tools_helpers.spl:15` |
| `-> [i64]`  | `src/lib/nogc_sync_mut/io/file_ops.spl:7` |
| `-> [i64]?` | `src/lib/nogc_sync_mut/sfm/container.spl:15`, `src/lib/nogc_sync_mut/io/telnet_serial_bridge.spl:31` |

The authoritative signature is `[u8]` — stated at
`src/compiler_rust/lib/std/src/infra/file_io.spl:70-78` and backed by the C
runtime; `src/runtime/simple_core/core_fs.spl:154` returns a raw `i64` handle.

**Not fixed by this lane, and deliberately so.** The convergence is tractable but
it is NOT confined to `src/lib/nogc_sync_mut/io/**`: only 2 of the 4 non-`[u8]`
declaration sites (`io/file_ops.spl`, `io/telnet_serial_bridge.spl`) fall inside
this lane's file scope, and `io/file_ops.spl:146` `file_read_bytes() -> [i64]` is
a public helper whose callers live outside it. Converging 2 of 4 sites would
leave the ABI split intact while breaking typed callers — strictly worse than
the status quo. This needs a single cross-cutting change with the whole caller
set in scope.

Guard spec `test/01_unit/compiler/extern/rt_file_read_bytes_single_extern_signature_spec.spl`
remains correctly RED.

### Corroboration 2026-08-17 — the COMPILER ITSELF now warns about this

An unrelated spec run in this lane surfaced the divergence as a first-class
compiler diagnostic, which is stronger evidence than the grep census above
because it proves the two signatures are genuinely co-compiled into one closure
and that dispatch between them is resolved heuristically:

```
warning: public function `file_read_bytes` has 2 co-compiled definitions with 2
differing signatures ((text)->[i64] vs (text)->[u8]); JIT call sites resolve by
exact arg-type match (mangled `$dupN` variants), falling back to the last
definition when types are ambiguous — a fallback hit may still dispatch to the
wrong one. Rename the conflicting helper(s) to a unique name.
[compiler_cross_module_private_symbol_collision]
```

Note the failure mode named in the diagnostic: **an ambiguous call site falls
back to "the last definition"**, i.e. lowering order decides which ABI a caller
gets. That is a silent-wrong-result mechanism, not merely a tidiness issue, and
it is the same shape as the `enum_payload_struct_names` last-one-wins collision
described in
`native_build_cross_module_result_payload_struct_name_collision_2026-08-09.md`.

Two sibling collisions were reported in the same run and are likely the same
class of defect, filed here only as a pointer:
- `dir_remove_all` — 2 definitions, `(text)->bool` vs `(text)->i32`
- `shell` — 3 definitions, `(text)->ProcessResult` vs `(text)->ShellResult`

### Guard-spec run 2026-08-17 — still correctly RED, and precisely one example red

```
Results: 7 total, 6 passed, 1 failed

  ✓ positive control: the scanner finds the declarations that certainly exist
  ✓ negative control: the anchor does not match a return type nobody uses
  ✓ control: the scan produces a non-empty type set
  ✓ no module declares the raw i64 handle form
  ✓ no module declares a List<i32> element width
  ✗ declares exactly one return type repo-wide
  ✓ the one return type matches the C runtime ABI

SPEC FILE VERDICT: test/01_unit/compiler/extern/rt_file_read_bytes_single_extern_signature_spec.spl declared>=7 executed=7 passed=6 failed=1 dropped=0
```

Both control examples and both narrowed-form examples pass, so the scanner is
working and the red is real rather than infrastructural. The single failing
example is exactly the convergence assertion, which matches the 4-type census
recorded above. Nothing in this spec needs changing; it goes green when the
declarations converge on `[u8]`.

(First attempt at this run exited `rc=2` with a zero-byte log — the resource
slot wrapper never launched it. That is UNVERIFIED, not a failure; the numbers
above come from the retry.)
