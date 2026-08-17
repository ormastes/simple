# Native cross-module arithmetic probe exits 5

## Status

Source-fixed; rebuilt execution pending. Stage2/3 rebuilt successfully from
pre-fetch HEAD `74269ec415`, but the
focused dual-backend gate still stopped before printing
`native-crossmodule-result-u8: pass`. A later mandatory fetch advanced current
source to `448317ea5d`, so those binaries are retained diagnostic evidence, not
current-tip admission artifacts.

## Reproduction

Use the current Stage3 compiler and bootstrap runtime with
`scripts/check/check-native-crossmodule-result-u8.shs`.

Latest retained bounded rebuild evidence (HEAD `74269ec415`):

- Stage2 build log: `build/bootstrap/hir-param-repair/stage2-diagnostic.log`
- Stage3 build log: `build/bootstrap/hir-param-repair/current-tip-stage3-direct.log`
- Stage2 SHA-256: `68520a4fc367af15c5126da3b996141ac176ca42aa188878f1821d94f761b7dc`
- Stage3 SHA-256: `d82ad2d3c7a0a2cd781267cca7f6709752367831dd68f9e982834847fffbad49`
- Stage3 generic admission: version, unsupported `run`, native p2 build, and
  executable output `5` all passed.
- Dual-backend gate: exit `5`; no PASS marker.

Older retained default-LLVM evidence:

- build log: `/tmp/check-native-crossmodule-result-u8-final-2850000/build.log`
- executable: `/tmp/check-native-crossmodule-result-u8-final-2850000/result-u8-default`

The build reports three compiled modules and no failures. Running the binary
returns 5 with empty stdout.

## Boundary

Exit 5 maps to `cross_target_arithmetic_ok()` in
`test/fixtures/native_crossmodule_result_u8/main.spl`. Object inspection and
GDB isolate the bad value to the `high > 0.0` / `0.0 < high` condition: GDB
stops at false-return block `0x40b34d`, and the machine code materializes
`0x8000000000000000u64` as f64 bits `0xc3e0000000000000` (negative 2^63)
instead of positive 2^63.

The textual LLVM backend primes unsignedness from MIR locals, but
`translate_copy_move` overwrote the annotated `u64` destination flag with its
signed literal temporary's flag. Preserving destination-or-source provenance
compiled through fresh Stage2/3 but did not make the final focused gate pass.
Higher review rejected that attempted OR rule because a known signed
destination must not inherit unsignedness. A later destination-preserving
nested guard was correct in source but not in the emitted Stage2/3: disassembly
proved the bootstrap seed resolved both `dest_id` and `src_id` dictionary keys
as `src_id`. The resulting binaries retained the old source-first overwrite.
The cast path itself correctly calls `get_operand_unsigned` and
`value_as_type_signed`; it is not the remaining owner.

## Source fix (2026-07-23)

Copy propagation now uses direct operand-to-ID calls so the bootstrap seed
cannot collapse the two local aliases. An already-primed destination keeps its
authoritative MIR signedness; only an unregistered destination inherits a known
source flag:

```spl
if not self.unsigned_locals.has(self.local_id_value(dest)):
    if self.unsigned_locals.has(self.local_id_value(src)):
        self.unsigned_locals[self.local_id_value(dest)] = self.unsigned_locals[self.local_id_value(src)]
```

The focused source regression rejects the former source-first overwrite. Next,
rebuild Stage2/3 incrementally and run the unchanged cross-module fixture once.
If it still fails, disassemble the keys before considering the separate
`translate_load` provenance audit. Do not weaken or delete the fixture, and do
not advance to Stage4/QEMU until it passes.

## Triage 2026-08-17 — exit code mapped to its exact predicate

Classified against current source, not SHA ancestry.

Exit 5 is now pinned to a specific check. In
`test/fixtures/native_crossmodule_result_u8/main.spl`, `fn main()` returns 5 from
exactly one site: `if not cross_target_arithmetic_ok(): return 5`. So the probe
is not failing generically — `cross_target_arithmetic_ok()` is the failing
predicate, and it is the ONLY thing exit 5 can mean.

That function tests, in order: mixed i64/f64 relational comparison
(`signed_int < 41.5`); u64-vs-i64 comparison across the sign bit
(`high = 0x8000000000000000u64` against `small = 1` for `< <= > >=`); u64-vs-f64
comparison (`high > 0.0`, `high <= 9223372036854775808.0`); u64 division and
modulo (`high / 2u64`, `high % 3u64`); u64 logical shift (`high >> 63u64 == 1u64`);
arithmetic (sign-propagating) right shift by an unsigned count
(`negative >> unsigned_count == -1` where `negative = -2i64`); and
truncation-toward-zero signed division (`-9 / 2 == -4`, `-9 % 2 == -1`).

Every one of those is a mixed-signedness / mixed-width numeric lowering
behaviour, which puts the root cause in the native codegen path, i.e. under
`src/compiler/50.mir/**` or `src/compiler/70.backend/**`. Those trees are CLAIMED
by other lanes in this sweep, so no fix is attempted here. Handing off: bisect
`cross_target_arithmetic_ok()` one predicate at a time — the u64-across-sign-bit
comparisons and the arithmetic-vs-logical shift distinction are the highest-prior
suspects, since both are classic silent-wrong-result lowering bugs.

NOT proven here: the probe was not executed, so it is not confirmed that exit 5
still reproduces today — only that IF it does, this is the predicate at fault.

## Re-triage 2026-08-17 (m9a_tests lane)

**Verdict: STILL RED — and the check script is undiagnosable by construction.**

`sh scripts/check/check-native-crossmodule-result-u8.shs` -> **rc=1** (read
directly into a variable on the line after the command, never through a pipe).
Not a signal, so this is a genuine failure rather than the rc=143 load-kill
seen elsewhere in this batch.

**But it produced ZERO bytes on stdout and stderr.** That is a defect in the
gate itself, independent of the bug it is meant to catch:

- the script is `set -eu`, so the first failing command aborts it silently;
- both `native-build` invocations redirect all output into
  `"$WORK_DIR/result-u8-$backend.log"` (lines 22-27);
- `trap rm -rf "$WORK_DIR" EXIT HUP INT TERM` (line 14) **deletes that log
  on the way out**, including on the failure path;
- the final check is a bare `test "$actual" = "$EXPECTED"` (line 30) with no
  message.

So a failing run destroys its own evidence and prints no verdict line at all,
violating the repos `PASS —/FAIL —/ERROR —` convention used by every
`scripts/check/` guard. Overriding `WORK_DIR` does not help: the EXIT trap
removes whatever path it is given. As written, this gate cannot distinguish
"the LLVM build failed", "the cranelift build failed", "the binary was not
produced", and "the binary ran and printed the wrong string" — which is
precisely the information the bug doc needs.

Recommended (owner of `scripts/check/**`, not this lane): emit a verdict line,
and either skip the cleanup on failure or copy the logs out before the trap
fires.

Reproduction was therefore re-driven manually with the trap out of the picture;
see the parent report for the outcome. The `exit 5` claim in the title is not
confirmed by this run — the observed script status is 1, and the underlying
per-backend statuses are the ones the script discards.

## Re-triage 2026-08-17 (m9a_tests lane) — ROOT CAUSE FOUND, and it is not arithmetic

**Verdict: LIVE, but MISDIAGNOSED. The probe never reaches `main()`, so it
never evaluates any arithmetic. The NATIVE-BUILD FAILS FIRST.**

The `exit 5` in the title is emitted by `main()` at
`test/fixtures/native_crossmodule_result_u8/main.spl` when
`cross_target_arithmetic_ok()` returns false. That line is unreachable today:

```
$ env -u SIMPLE_BOOTSTRAP SIMPLE_NO_STUB_FALLBACK=1 bin/simple native-build \
    --source test/fixtures --source src/lib --entry-closure \
    --entry test/fixtures/native_crossmodule_result_u8/main.spl \
    --cache-dir <tmp>/cache --output <tmp>/bin
BUILD rc=1
no binary produced

error: unresolved import 'native_crossmodule_result_u8.provider' (used in
test/fixtures/native_crossmodule_result_u8/main.spl): no source file found for
this module path relative to the working directory, src/, src/lib/, or
'test/fixtures/native_crossmodule_result_u8'
error: native-build worker exited with code 1.
  interpreter: /mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple (exit code 1)
```

### The imported module is present on disk

```
$ ls -la test/fixtures/native_crossmodule_result_u8/
-rw-rw-r-- 1 ormastes ormastes 16889 Aug 11 22:10 main.spl
-rw-rw-r-- 1 ormastes ormastes   551 Aug 11 22:10 provider.spl
```

`provider.spl` exists and defines exactly the symbols `main.spl:1` imports
(`enum BytesError`, `enum CrossProviderIdentity`, ...). So this is **not** a
missing fixture file, and it is not path drift.

### The `--source` root is being ignored

Read the resolver's own error text: it lists the roots it searched as *"the
working directory, src/, src/lib/, or
`test/fixtures/native_crossmodule_result_u8`"*. The invocation passed
`--source test/fixtures`, under which `native_crossmodule_result_u8.provider`
resolves trivially to `test/fixtures/native_crossmodule_result_u8/provider.spl`.
**`test/fixtures` does not appear in the searched list at all** — the
`--source` flag is not reaching module resolution on the native-build path.
Note the entry directory is searched, but a sibling module is addressed by its
*package-qualified* name (`native_crossmodule_result_u8.provider`), which the
entry directory alone cannot satisfy.

**DIAGNOSIS ONLY — the fix is in the native-build module resolver / `--source`
plumbing (`src/**`), owned by another lane.** No source edit made from the test
lane. The fixture itself needs no change.

### Secondary defect: this gate destroys its own evidence

Independently of the above, `scripts/check/check-native-crossmodule-result-u8.shs`
cannot be diagnosed from its own output. Running it plain gives **rc=1 with
ZERO bytes on stdout and stderr**, because:

- it is `set -eu`, so the first failure aborts silently;
- both `native-build` calls redirect all output into `"$WORK_DIR/result-u8-$backend.log"` (lines 22-27);
- `trap 'rm -rf "$WORK_DIR"' EXIT HUP INT TERM` (line 14) deletes that log on the failure path too;
- the verdict is a bare `test "$actual" = "$EXPECTED"` (line 30) with no message.

Overriding `WORK_DIR` does not rescue the logs — verified: the EXIT trap removed
the supplied directory, leaving `ls` reporting *No such file or directory*. The
root cause above was only recoverable by re-running the `native-build` command
by hand outside the script. The gate also prints no `PASS —/FAIL —/ERROR —`
verdict line, unlike every other guard in `scripts/check/`.

Recommended (owner of `scripts/check/**`): emit a verdict line, and preserve
the per-backend logs on failure.

### Not covered

Only the `default-llvm` backend was driven manually. The `cranelift` arm of the
loop was not reached, so no claim is made about it.
