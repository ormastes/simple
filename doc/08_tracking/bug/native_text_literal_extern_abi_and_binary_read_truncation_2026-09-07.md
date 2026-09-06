# Native runtime: text literals never reach a `text` extern, and binary reads truncate at the first NUL

- Date: 2026-09-07
- Arch measured: aarch64-unknown-linux-gnu
- Status: two defects FIXED in `src/runtime/runtime_native.c`; two further
  findings below are OPEN and unowned by this change.

## How this was found

Chasing the Stage-2 positional `native-build` failure of the hello-world
fixture. The preserved failing binary is
`build/bootstrap/stage2/aarch64-unknown-linux-gnu/simple.rejected`; the failing
invocation is the one in `scripts/check/check-aot-failure-speaks.shs`.

Two facts constrain every claim below.

1. **That binary does not read compiler source at runtime.** Inserting a bare
   literal `print "ZZPROBE-..."` at the top of
   `driver_native_capsule_result_invalid_reason_v1` and again at the top of
   `_compile_frozen_module_capsule` produced ZERO occurrences in the output of a
   fresh failing run, and the binary prints the pre-`a820c8fd10e` form of the
   summary line (no `[empty-at-record]` tag) although the working tree carries
   the new one. It opens `src/compiler/**` (356,657 `openat` calls under
   `strace`) but executes a baked-in copy. **No `src/**` edit can be validated
   against it without rebuilding Stage 2.**
2. The object it emits is **correct**: `object.….hello_world.o`, 1080 bytes,
   `ELF 64-bit LSB relocatable, ARM aarch64`, defining `T __simple_main` and
   referencing `U rt_println` / `U rt_interp_cstr`. The compile succeeded.

Probes were therefore built by having the Stage-2 binary emit an object for a
small `.spl` file and hand-linking that object against the C runtime archive
(`scripts/check/native_text_abi_probe.c` is the C-level distillation).

## Defect 1 — `rt_string_data` has no raw-literal fallback (FIXED)

The compiler lowers a `text` extern argument to the PAIR
`(rt_string_data(v), rt_string_len(v))` — visible in the disassembly of any
natively compiled call site:

```
bl rt_string_data ; mov x21, x0
bl rt_string_len  ; mov x1, x0
mov x0, x21
bl rt_file_size
```

A `text` **literal** is not a heap `RtCoreString`; it is a bare pointer into
`.rodata.str1.4`. `rt_string_len` already carried
`return string >= 0x10000 ? strlen(...) : -1;` for that case. `rt_string_data`
did not, and returned `NULL`. `rt_text_arg_to_path` then rejects `(NULL, 13)`
via `if (!ptr && len != 0) return 0;`.

Measured on a Stage-2-compiled probe, before the fix:

```
literal direct=-1        # rt_file_size("/etc/hostname")
built   direct=11        # rt_file_size("/etc/" + "hostname"), same bytes
```

After the fix both report 11. Every `text`-ABI extern called with a string
literal was failing in every natively compiled Simple binary.

## Defect 2 — `rt_file_read_text` truncated at the first NUL (FIXED)

It called `spl_file_read(path)` and then `strlen()` on the result. An ELF
object's `e_ident` has a NUL at offset 7, so a 1080-byte aarch64 `.o` came back
as a **non-nil 7-byte** text.

`FileFingerprint.from_file`
(`src/compiler/80.driver/driver_build/incremental.spl:350`) documents "Text read
is nil for a missing OR non-UTF-8 file … fall back to a byte-level digest" and
only takes `rt_file_hash_sha256` on that nil. A non-nil short read made that
fallback **dead code on the native runtime**, so the native capsule receipt
recorded `rt_hash_text` of 7 bytes of ELF magic —
`-8673224916767039355`, identical for **every** aarch64 object ever emitted.
`driver_native_capsule_result_valid_v1` is an authenticated cache checkpoint; a
checkpoint keyed on a constant authenticates nothing.

Measured on the real 1080-byte object, before/after:

```
obj read SOME len=7    hash=-8673224916767039355
obj read SOME len=1080 hash=290620426953303896
```

`rt_file_size` was never wrong: it reports 1080 both before and after.

Neither defect is visible to `check-c-runtime-compiles-push.shs`, which only
runs `-fsyntax-only`; both compile cleanly. Gate added:
`scripts/check/check-native-text-abi-and-binary-read.shs` (behavioural — it
builds and RUNS the runtime; `--selftest` reintroduces both defects and requires
a FAIL). Pre-fix verdict on the committed tree:
`FAIL — 4 contract(s) checked, 3 failed`.

## OPEN 1 — the receipt's `size` and `content_hash` are still unexplained

The receipt the Stage-2 binary writes records, reproducibly across three runs:

```
line 4 (fp.size)         = 16     # the object is 1080 bytes
line 5 (fp.content_hash) = 161
```

Neither value is producible by the runtime that binary is linked against:
measured directly through that runtime, `rt_file_size` = 1080 and
`rt_hash_text` of the (truncated) read = `-8673224916767039355`. A Stage-2
**compiled** probe that builds the same 4-field struct behind the same
`Some(...)`/`if val` shape and interpolates `{fp.size}`/`{fp.content_hash}`
renders them correctly (`size=1080`, `hash=h`), so this is not a struct-field or
interpolation defect in Stage 2's *output*. It remains a defect in Stage 2's own
code, i.e. in what **Stage 1** emitted, and Stage 1's output was not measured.

This is NOT the failing sub-check, and the "size=16" lead should not be chased
as if it were: `strace` shows the collection checkpoint running to completion in
the failing process — `hello_world.spl`, the object twice, the receipt, all
twice over — and then `build_cache.sdn` opened `O_WRONLY|O_CREAT|O_TRUNC`, which
is only reachable after every sub-check has passed. The process exits 1 with
that write as its last syscall. Producer and verifier compute the fingerprint
with the same function on the same unchanged file, so the receipt comparison
cannot be what fails.

## OPEN 2 — Stage 2's compiler SEGVs on a struct plus externs

`.wk/probe7.spl` / `.wk/probe8.spl` shapes — a 4-field struct built inside a
function that also calls a `text` extern and `.to_text()` — kill the Stage-2
native-build worker with `signal 11` at the MIR step, with or without the
`Optional` return. The struct alone (`probe9`) compiles and runs correctly. Not
reduced further here.

## What is NOT claimed

That either fixed defect is *the* Stage-2 blocker. It cannot be shown from here:
the failing binary executes a baked-in compiler and a statically linked runtime,
so neither a `src/runtime/**` nor a `src/compiler/**` fix changes its behaviour
without a Stage-2 rebuild. `check-aot-failure-speaks.shs --candidate` still
reports `FAIL — 1 invocation(s) executed, failure exit 1 is UNATTRIBUTED
(unattributed-none-recorded)` on it, and will keep doing so until a Stage 2 is
rebuilt from a tree containing `a820c8fd10e`.
