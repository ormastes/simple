# `File.write` reports Ok and writes NOTHING — all 13 `rt_io_file_*` externs are undefined and RT_KEEP-stubbed

Date: 2026-08-05
Lane: IO-REWIRE
Status: CONFIRMED. Silent data loss in an exported stdlib API.
Severity: HIGH (silent, exit 0, engine-divergent)

## Summary

`src/lib/nogc_sync_mut/io/file.spl` — the public `FileHandle` / `File` API,
re-exported from `std.nogc_sync_mut.io` — declares 13 `extern fn` symbols that
**are defined nowhere in the repo**. Under native/JIT they are silently replaced
with fabricated zero-returning stubs, so `File.write` returns `Ok`, creates no
file, and every subsequent read returns empty. Exit status is 0 throughout.

## The 13 undefined symbols

Declared at `src/lib/nogc_sync_mut/io/file.spl:504-516`:

```
rt_io_file_open   rt_io_file_read     rt_io_file_read_all  rt_io_file_read_line
rt_io_file_write  rt_io_file_write_all rt_io_file_seek     rt_io_file_flush
rt_io_file_close  rt_io_file_metadata  rt_io_file_set_permissions
rt_io_file_exists rt_io_file_delete
```

None is defined in `src/compiler_rust/runtime/**`, `src/runtime/*.c`, `build.rs`
codegen, or the interpreter's extern registry.

## Evidence — `nm`, with a positive control

```
$ /usr/bin/nm -g --defined-only src/compiler_rust/target/bootstrap/libsimple_runtime.a \
    | /usr/bin/grep -c 'rt_io_file'
0
$ /usr/bin/nm -g --defined-only src/compiler_rust/target/bootstrap/libsimple_runtime.a \
    | /usr/bin/grep -c ' T rt_file_'
43
```

The positive control matters: the *other*, correctly-defined family `rt_file_*`
(43 symbols — `rt_file_open`, `rt_file_read_text`, `rt_file_write_text`,
`rt_file_size`, `rt_file_exists`, `rt_file_delete`, …) is present in the same
archive. So the zero is a real absence, not a broken `nm` invocation.

## Mechanism — RT_KEEP suppresses the link-time check

`src/compiler_rust/compiler/src/linker/native_binary/stubs.rs:569` is supposed
to hard-fail a native link on any undefined `rt_*` symbol:

```rust
.filter(|s| s.starts_with("rt_") && !RT_KEEP.contains(s) && !real.contains(*s))
```

All 13 are listed in `RT_KEEP` at `stubs.rs:195-208`, so the filter drops them
and each one instead receives the fabricated zero-returning stub that the file's
own header comment warns about. The allowlist that exists for *compiler-internal
bootstrap placeholders* is here shielding a user-facing data path.

## Observed behavior (engine-divergent)

| engine | behavior |
|--------|----------|
| native / JIT | `File.write` returns **Ok**; no file on disk; `File.exists` = false; size 0; reads return `''`. **Exit 0.** |
| `SIMPLE_EXECUTION_MODE=interpret` | fails closed: `unknown extern function: rt_io_file_open` |

Probe verdict line:

```
VERDICT: FAIL rt_io_file family broken (4 failures)
```

This divergence is why a single-engine check is not evidence: the interpreter
refuses to run the path at all, so an interpreter-only suite never sees the data
loss, and a JIT-only suite sees a green `Ok` on a write that did nothing.

## Blast radius

- `file.spl` **is** in the Stage-3 closure via
  `src/lib/nogc_sync_mut/io.spl:153` (`export use ... {FileHandle, File}`), so
  it compiles and links in every bootstrap.
- It has **zero owned callers.** All 29 `File.open(` call sites live in the
  vestigial `src/compiler_rust/lib/std/**`.
- Owned code uses the *other* family, `io.file_ops` (426 references, backed by
  the defined `rt_file_*` symbols) — which is why this has never been noticed.

So today the damage is latent: the API is exported, documented-looking, and
importable, and the first owned caller to use it silently loses data.

## Why the `rt_file_*` family cannot simply absorb it

`rt_file_*` is overwhelmingly **path-level** (`read_text(path)`,
`write_text(path, ...)`). `file.spl` is an **fd-level** API. Only 4 of the 13
have a counterpart (`open`, `close`, `exists`, `delete`); the other 9 —
`read(fd,size)`, `read_all(fd)`, `read_line(fd)`, `write(fd,data)`,
`write_all(fd,data)`, `seek(fd,off,whence)`, `flush(fd)`, `metadata(fd)`,
`set_permissions(fd,ro)` — have none. `src/compiler_rust/runtime/src/value/
sffi/file_io/descriptor.rs` is the natural home: it already holds the fd-level
`rt_file_open` / `rt_file_get_size` / `rt_file_close`, and stops there.

## Ordering hazard for any fix

Removing entries from `RT_KEEP` converts every native build into a hard failure
for any symbol still undefined, and a Stage-3 bootstrap runs off the live
working tree. **Define the symbols first, verify with `nm`, and only then touch
`RT_KEEP`.** Never the reverse.

## Related cleanup landed with this report

`test/01_unit/lib/io/file_seek_openmode_native_check.spl` (lane FFI-ENUM) was
deleted. It asserted seek positions on this exact broken path, so it could only
ever fail — and it would have failed against the zero-stubs, not against the
FFI enum-crossing defect it claimed to test. Its header also asserted that an
interpreter run is "vacuous for this defect"; in fact the interpreter fails
closed with `unknown extern function`, which is the single clearest signal
available. Both of its conclusions were false.

---

## Re-verification 2026-08-17 (io lane) — STILL LIVE, and worse than filed

Classified by CONTENT, then reproduced on the deployed binary.

### What HAS changed since 2026-08-05 (so the original prose is stale)

All 16 symbols now have real implementations in BOTH engines:
- native C-ABI: `src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs`
  (`rt_io_file_open`:82, `read`:116, `read_all`:134, `read_line`:150,
  `write`:175, `write_all`:188, `seek`:199, `flush`:219, `close`:227,
  `set_permissions`:248, `meta_size`:268, `meta_flags`:278, `meta_modified`:313,
  `meta_created`:322, `exists`:331, `delete`:340)
- interpreter: `src/compiler_rust/compiler/src/interpreter_extern/io_file.rs`,
  registered at `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1379-1393`

`RT_KEEP` still lists 12 of them at
`src/compiler_rust/compiler/src/linker/native_binary/stubs.rs:209-221`, with a
`TODO(rt_io_file)` at :195 saying they may be dropped "once the deployed runtime
carries it". So the stub-fabrication shield is still armed.

### The family is nonetheless non-functional on the deployed binary — IN INTERPRET MODE

Binary: `bin/release/x86_64-unknown-linux-gnu/simple`, 59536728 bytes, mtime
2026-08-16 22:59:37. `strings` confirms it CONTAINS the interpreter module
(`rt_io_file: argument` present, `rt_io_file_open` x5), so this is not a
"predates the fix" staleness story.

New run-path probe `test/01_unit/lib/io/probe_rt_io_file_family.spl` — every
oracle is an absolute filesystem fact, cross-checked against the independently
implemented `rt_file_*` family as a positive control:

```
$ SIMPLE_RUST_SEED_WARNING=0 bin/simple run test/01_unit/lib/io/probe_rt_io_file_family.spl
PASS control_rt_file_write_text
PASS control_rt_file_exists_true
PASS control_rt_file_read_text
FAIL rt_io_file_exists_agrees_with_control
FAIL rt_io_file_open_returns_nonnegative_fd
FAIL rt_io_file_write_all_reports_ok
FAIL rt_io_file_meta_size_is_three
FAIL rt_io_file_close_reports_ok
FAIL written_bytes_visible_to_control_family
FAIL rt_io_file_delete_really_removes_file
RT_IO_FILE PROBE: FAILURES
```

The control arm passing is what makes this non-vacuous: the same process, the
same path, the same binary — `rt_file_write_text`/`rt_file_exists`/
`rt_file_read_text` all work, and every `rt_io_file_*` call fails.

Narrowest reduction — the path argument is not arriving:

```
$ ls -l /etc/hostname
-rw-r--r-- 1 root root 3 Aug 24  2025 /etc/hostname
$ bin/simple run <probe calling rt_io_file_exists("/etc/hostname")>
exists_etc_hostname=false
open_ro_etc_hostname=-1        # mode passed as a typed i64 local
open_ro_literal=-1             # mode passed as a literal
```

`rt_io_file_exists` returning `false` for a file that provably exists, rather
than erroring, rules out "unknown extern" and rules in a wrong dispatch: the
registered interpreter implementation (which would `Err` on a non-`Value::Str`
arg 0, and whose `OpenOptions` mode table at io_file.rs:112-127 is correct) is
evidently not the code being reached. The prime suspect is the dynamic dlsym
fallback (`dynamic_sffi.rs`), which marshals one leaked `i64` per `Value::Str`
instead of the `(ptr, len)` pair the native `rt_io_file_*` signatures require —
exactly the mechanism this doc's own header comment in
`interpreter_extern/io_file.rs:9-14` warns about. NOT PROVEN: I did not
instrument the dispatch to confirm which of the two paths is taken.

### Consequence for the downstream row

`test/fixtures/rt_io_file_roundtrip/main.spl` fails at its FIRST step
(`VERDICT: FAIL open WriteOnly failed`, `/tmp/rt_io_file_roundtrip_probe.txt`
never created) under plain `bin/simple run`. Any lane using that fixture to
measure the native-build `Result<T,E>` payload-struct-name collision
(`native_build_cross_module_result_payload_struct_name_collision_2026-08-09.md`)
is measuring THIS defect first.

### Scope note

No fix was made here: `src/lib/nogc_sync_mut/io/file.spl` is correct — its 16
`extern fn` declarations at lines 515-530 match the Rust signatures, and its
`FileMode` lowering at :98-101 matches the documented 0/1/2/3 encoding. The
defect is entirely in the Rust extern-dispatch path, which is outside this
lane's file scope.

Specs added (both fail today, deliberately):
- `test/01_unit/lib/io/probe_rt_io_file_family.spl` (run-path probe)
- `test/01_unit/lib/io/rt_io_file_family_real_disk_spec.spl` (reproducing +
  class-detection; shells out to a subprocess under both `interpreter` and `jit`
  because a spec body always runs interpreted)

---

## ROOT CAUSE FOUND 2026-08-17 — the prose above is STALE on every point

All 16 symbols now have real implementations and are registered in both
directions: 16 `pub unsafe extern "C" fn rt_io_file_*` in
`src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs`, 16 `pub fn` in
`src/compiler_rust/compiler/src/interpreter_extern/io_file.rs`, 16
`insert_simple!` at `interpreter_extern/mod.rs:1379-1394`. Nothing is undefined
and nothing is missing from a registry. This is a **marshalling** defect.

### Measured (deployed seed `bin/release/x86_64-unknown-linux-gnu/simple`, 59536728 bytes, mtime 2026-08-16 22:59; rc read off the line AFTER each command)

| probe | interpreter | jit (== default) |
|---|---|---|
| `test/01_unit/lib/io/probe_rt_io_file_family.spl` | rc=0, `RT_IO_FILE PROBE: ALL PASS` (10/10) | rc=1, 3 control PASS / 7 `rt_io_file_*` FAIL |
| `test/01_unit/lib/io/probe_rt_io_file_fd_only.spl` (new) | rc=1 — see "second defect" below | rc=0, `RT_IO_FILE FD PROBE: ALL PASS` |

"Non-functional even in interpret mode" is **FALSE**: `bin/simple run` defaults
to JIT. Interpret mode is green. "The whole family is broken under JIT" is also
false — the fd-only probe takes its descriptor from the working control family
and shows `meta_size`/`meta_flags`/`seek`x3/`flush`/`close` all PASS under JIT.
Four of the seven original JIT failures were **collateral** inside the probe's
`fd >= 0` branch.

### Root cause

`text_arg_indices()` — `src/compiler_rust/compiler/src/codegen/instr/calls.rs:2535`
(cranelift/JIT) and `src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs:99`
(LLVM/AOT) — is a hand-maintained **allowlist** of which extern arguments get
expanded from one Simple `text` (a RuntimeString handle) into the `(ptr, len)`
pair the runtime's C ABI declares. `rt_file_exists` is on it
(`instr/calls.rs:2599`, `llvm/.../calls.rs:145`); **`rt_io_file_open`,
`rt_io_file_exists` and `rt_io_file_delete` appear in neither table**. The JIT
therefore passes the handle as `path_ptr` and whatever occupies the next
argument register as `path_len`. No link error, no crash: `exists` returns
false for a file that exists, `open` returns -1, exit 0.

Exactly three members of the family take `text`
(`io_file.rs:82` open, `:331` exists, `:340` delete); the other 13 are i64/bool
only, which is why they were already correct under JIT.

The dlsym-fallback hypothesis is **REFUTED**: `rt_file_exists`
(`file_io/metadata.rs:241`) has the identical `(*const u8, u64)` shape and works
under JIT, so the shape itself is not the problem — table membership is.

### Fix (edit prepared, NOT applied — both `calls.rs` files are held by another lane)

Add to `text_arg_indices()` in BOTH tables:

```rust
"rt_io_file_open" | "rt_io_file_exists" | "rt_io_file_delete" => Some(&[0]),
```

Same class as the `rt_file_write_text` / `rt_dir_create` fixes already recorded
in comments in that same function.

### Second, independent defect found by the new fd-only probe

`interpreter_extern/file_io.rs:2082-2096` — `rt_file_open` returns a hardcoded
`-1`, `rt_file_get_size` `-1`, `rt_file_close` `false`, commented "Simplified -
return -1 (not implemented for interpreter)". These are registered
(`interpreter_extern/mod.rs:1340`) and work under JIT, so the **control**
family is silently engine-divergent in the mirror-image direction. Not fixed
here: `interpreter*` is owned by another lane.

### Third instance of the same class, found by the class detector

`test/01_unit/lib/io/extern_text_arg_marshalling_scan.shs` derives the required
table membership from the runtime's own C signatures. Offenders, over 32
classified text-taking symbols:

- missing from **both** tables: `rt_mkdir_p` — a live, unfiled instance;
- missing from the **LLVM/AOT** table only (present in cranelift): `rt_dir_create`,
  `rt_dir_create_all`, `rt_file_append_text`, `rt_file_write_text`,
  plus the three `rt_io_file_*` above. The two tables have silently diverged.

### Specs added

- `test/01_unit/lib/io/rt_io_file_text_arg_jit_marshalling_spec.spl` — reproducing;
  runs both probes as subprocesses under each engine (a spec body runs
  interpreted, where this defect does not exist).
- `test/01_unit/lib/io/extern_text_arg_marshalling_completeness_spec.spl` +
  `extern_text_arg_marshalling_scan.shs` — class detection for "extern symbol
  registered but dispatched with the wrong marshalling", non-vacuity asserted
  via the scan's own `SCANNED <n>` receipt.

### Spec-run note (2026-08-17) — the first spec shape blew the daemon budget

The initial four-example version of `rt_io_file_family_real_disk_spec.spl`
spawned four subprocesses (three interpreter + one JIT). Each pays the ~300s
fixed session setup, so the file exceeded the 900s test-daemon budget and
produced NO `Results:` line at all:

```
ERROR: test daemon timed out: test/01_unit/lib/io/rt_io_file_family_real_disk_spec.spl
ERROR: no response from the light daemon within 900000ms + 2000ms grace.
SPEC FILE VERDICT: test/01_unit/lib/io/rt_io_file_family_real_disk_spec.spl declared>=1 executed=1 passed=0 failed=1 dropped=0 timeout=1 reason=daemon-no-response budget_ms=900000
```

That outcome is UNVERIFIED, not RED — and it is worth recording because it is
shaped exactly like the silent-green class being hunted: a shell-out spec whose
subprocess budget is exceeded reports no `Results:` line, and a lane skimming
exit codes could read it either way. The spec was consolidated to exactly TWO
subprocess runs (one per engine), with a header comment forbidding a third.

The defect evidence above does not depend on the spec: it comes from direct
`bin/simple run` invocations of the probe.

### VERIFIED BY REBUILD 2026-08-17 — the text-arg table alone is NOT enough

Isolated `CARGO_TARGET_DIR=/mnt/data/tmp_cargo_iofile`, `cargo build --release
--bin simple`, rc read off the line after the command (BUILD_RC=0 both times).

1. **text_arg_indices entries alone: NO CHANGE.** Rebuilt with
   `"rt_io_file_open" | "rt_io_file_exists" | "rt_io_file_delete" => Some(&[0])`
   added to `instr/calls.rs`; JIT probe still 3 control PASS / 7 FAIL. The
   entries were **dead**.
2. **Why.** The entire text-expansion block sits inside
   `else if let Some(&runtime_id) = ctx.runtime_funcs.get(sffi_name)`
   (`instr/calls.rs:3341-3383`). `ctx.runtime_funcs` is populated from
   `RUNTIME_FUNCS`/`RuntimeFuncSpec` in `codegen/runtime_sffi.rs`, and
   `grep -c rt_io_file runtime_sffi.rs` = **0**. Without a spec the branch is
   never taken, so no table is ever consulted. This is exactly the hazard
   already written down at `instr/calls.rs:2559` ("for those the `runtime_funcs`
   branch is never taken and these entries would be dead").
3. **Both together fix it.** Adding, next to `rt_file_open`
   (`runtime_sffi.rs:1888`):

```rust
RuntimeFuncSpec::new("rt_io_file_open", &[I64, I64, I64], &[I64]), // path_ptr, path_len, mode -> fd
RuntimeFuncSpec::new("rt_io_file_exists", &[I64, I64], &[I8]),     // path_ptr, path_len -> bool
RuntimeFuncSpec::new("rt_io_file_delete", &[I64, I64], &[I8]),     // path_ptr, path_len -> bool
```

| probe oracle (JIT) | before | after |
|---|---|---|
| `rt_io_file_exists_agrees_with_control` | FAIL | **PASS** |
| `rt_io_file_open_returns_nonnegative_fd` | FAIL | **PASS** |
| `rt_io_file_close_reports_ok` | FAIL | **PASS** |
| `rt_io_file_delete_really_removes_file` | FAIL | **PASS** |
| `rt_io_file_write_all_reports_ok` | FAIL | FAIL (residual, below) |
| `rt_io_file_meta_size_is_three` | FAIL | FAIL (collateral of write_all) |
| `written_bytes_visible_to_control_family` | FAIL | FAIL (collateral) |

Interpreter arm stayed `RT_IO_FILE PROBE: ALL PASS` and the fd-only probe stayed
`RT_IO_FILE FD PROBE: ALL PASS` under JIT — no regression on the 13 members that
were already correct (only the 3 text-taking members were given specs, on
purpose).

### Residual, distinct sub-defect: `[u8]` arguments have no (ptr, len) expansion

`rt_io_file_write(fd, data: [u8])` and `_write_all` map to C
`(fd, data_ptr, data_len)` (`io_file.rs:175,188`), but there is **no byte-array
analogue of `text_arg_indices`** — `process_c_runtime_arg_indices` is
`rt_process_*`-only (argv), not a bytes (ptr,len) expansion. The repo's existing
answer to this elsewhere is a runtime-side `RuntimeValue`-taking wrapper
(`rt_file_write_bytes_array`, `file_ops.rs:1344`). Fixing it therefore needs an
edit in `runtime/src/value/**`, which this lane does not own. Filed here rather
than attempted.
