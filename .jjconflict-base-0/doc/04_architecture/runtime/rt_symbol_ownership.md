# rt_* symbol ownership: Rust runtime vs C runtime

Date: 2026-08-18. Analysis-only; no runtime code was changed to produce it.

## 1. Census

Extraction reuses the exact regexes/logic of
`scripts/check/check-runtime-api-regression-push.shs` (`defined_symbols_rust` /
`defined_symbols_c`), so the numbers are consistent with that guard. The only
deliberate difference: the guard reads COMMITTED content at a rev; this census
reads the working tree at HEAD.

- RUST set — `src/compiler_rust/runtime/src/**/*.rs`, `pub extern "C" fn rt_*` or
  `pub fn rt_*`: **1799**
- C set — `src/runtime/**/*.c` and `*.h` (vendored excluded:
  `src/runtime/vendor/**`, `miniaudio.h`, `stb_image.h`, `stb_truetype.h`),
  definition form `^<type> rt_NAME(...) {`: **1450**
- Intersection (defined in BOTH): **455**
- Rust-only: **1344**
- C-only: **995**

The 455 duplicated names are listed in
[`rt_symbol_duplicates.md`](rt_symbol_duplicates.md).

Known extraction limits (same as the guard, so stated rather than papered over):
the C regex requires the definition to open on one line and is blind to
macro-generated definitions; the Rust regex counts `pub fn rt_*` even where the
item is not `extern "C"`. Neither list has been cross-checked against `nm` output
of a built archive — that cross-check is **unverified**.

## 2. Why the two sets overlap at all, and why a stale archive persists

`src/runtime/runtime_native.c` is a parallel C implementation that tracks the
Rust runtime's coverage (its own comments say so). The guard therefore evaluates
the two sets **separately and never unions them** — a union masks a real Rust
removal whenever a same-named C fallback still exists (that is exactly how the
2026-08-11 44-symbol clobber went undetected in development).

Staleness mechanism, from
`doc/08_tracking/bug/stage3_links_stale_rust_runtime_archive_runtime_fixes_are_noops_2026-08-17.md`
and `scripts/bootstrap/bootstrap-from-scratch.sh` (~lines 1225-1250):
`seed_inputs_hash` fingerprints the Rust inputs by CONTENT and correctly detects
staleness, but the rebuild (`rust_authority_root=...`) sits inside
`if [ "${full_bootstrap}" -eq 1 ]`. Without `--full-bootstrap` the run prints
`WARNING: Seed/runtime stale, but this is not --full-bootstrap; reusing the
existing Rust seed.` and proceeds on the known-stale
`libsimple_native_all.a`. Consequence: **any edit under
`src/compiler_rust/runtime/**` is a silent no-op for stages 2 and 3** while the
source tree claims the fix. The bug doc measured exactly this for
`8510a8368ca` (`rt_clear`): the source has the Dict arm, the linked archive does
not.

## 3. Which archive actually wins at link time

- The C runtime is compiled by `src/compiler_rust/runtime/build.rs`
  (`compile_c_runtime_sources`) into `libruntime_sffi_c.a` from an **explicit,
  curated source list** — `runtime_native.c` itself is deliberately NOT on that
  list; only a hand-copied `runtime_native_gpu_stub.c` is, precisely because
  pulling the whole TU in would duplicate-symbol against the crate's own Rust
  definitions (`host_gpu_lane.rs`). So most of the 455 duplicates never reach the
  same link.
- Linkage is `cargo:rustc-link-lib=static=runtime_sffi_c` (selective archive
  extraction: a member is pulled in only to satisfy an *undefined* symbol).
  Because the Rust CGUs already define the name, the C member is simply not
  extracted — **Rust wins by default**.
- The one exception is the `runtime_symbol_table` feature, which links
  `static:+whole-archive=runtime_sffi_c`. Whole-archive forces every C member in;
  a genuine same-name collision there is a hard duplicate-symbol link error, not
  a silent pick. That this feature currently links cleanly implies the curated
  list avoids all 455 overlaps in practice — **unverified**, not measured here.
- The stage-3 binary examined in the bug doc contained **zero** C-runtime
  definitions (`nm --defined-only` found no `rt_core_as_dict`), and no runtime
  `.so` exists, so there is no late-binding escape either.

## 4. Reader command — what is actually linked into a given binary

Two steps. First, confirm the symbol exists and is defined locally:

```sh
nm --defined-only bin/release/x86_64-unknown-linux-gnu/simple | grep -w rt_clear
```

Then attribute it to an implementation by disassembling it and reading the
callee mangling — Rust callees are `_ZN14simple_runtime...`, C callees are plain
identifiers:

```sh
objdump -d --disassemble=rt_clear bin/release/x86_64-unknown-linux-gnu/simple \
  | grep -oE '<[A-Za-z_0-9:$.]+>' | sort -u
```

Verified 2026-08-18 on `bin/release/x86_64-unknown-linux-gnu/simple`: `rt_clear`
resolves to the Rust implementation (callees
`_ZN14simple_runtime5value11collections13string_as_str...`,
`...refuse_non_text_receiver...`, `...SHORT_STRING_CACHE...`). Absence of a
second `get_typed_ptr` call is the pre-fix (stale) shape the bug doc describes.

To attribute an archive member instead of a binary:

```sh
nm -A --defined-only build/bootstrap/.../libsimple_native_all.a | grep -w ' T rt_clear'
```

The `-A` prefix names the `.o` member (`...-cgu.NN.rcgu.o` for Rust CGUs,
`runtime_*.o` for C), which is the definitive answer for which side supplied it.

## 5. Recommendation

1. **Rust owns every one of the 455 duplicated names on hosted targets.** That
   is already the de-facto outcome of selective archive extraction; make it
   explicit rather than incidental, so nobody "fixes" a hosted bug in the C copy
   and sees no effect.
2. **C owns the 995 C-only names**, plus the baremetal/no-Rust lanes where the
   Rust crate is not linked at all. Those are the only lanes where editing
   `runtime_native.c` changes behaviour of a hosted product build.
3. **Do not union the two sets** in any tooling — keep the guard's separation.
4. **Before claiming any `src/compiler_rust/runtime/**` fix took effect, run the
   §4 command on the actual binary.** Given §2, source-level evidence is not
   evidence; a rebuild without `--full-bootstrap` reuses the stale archive.
5. Open follow-up (not done here): decide whether the non-`--full-bootstrap`
   stale path should hard-fail instead of warning. Tracked in the 2026-08-17 bug
   doc.
