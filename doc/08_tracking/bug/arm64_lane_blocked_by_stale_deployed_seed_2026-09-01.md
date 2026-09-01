# arm64 lane: the parse failures are a STALE DEPLOYED SEED, not bad sources (2026-09-01)

Status: **ROOT CAUSE IDENTIFIED**. Supersedes the diagnosis in
`arm64_desktop_engine2d_media_chain_blockers_2026-09-01.md` § "Still blocked" item 4.

## The prior diagnosis was wrong on both sites

That record attributed the seed's parse rejections to the arm64 server-payload
sources themselves:

- `src/os/userlib/fs.spl:537` — "the only multi-line `export a, b,` /
  continuation form in `src/os/`: expected expression, found Dedent".
- `src/os/apps/dbd/dbd.spl` — "expected expression, found Newline".

Neither holds.

### 1. Multi-line `export` is NOT the problem — the seed supports it explicitly

Minimal fixture, compiled with the deployed seed, exit 0:

```
fn alpha() -> i64:
    return 1
fn beta() -> i64:
    return 2
export alpha,
    beta
```

The Rust seed hand-consumes Newline/Indent/Dedent inside a comma-continued
export list — `src/compiler_rust/parser/src/stmt_parsing/module_system.rs:820-845`
(`parse_export_use`), comment: *"Skip newlines and indents after comma to
support multi-line export lists"*. `fs.spl:537` is well within that.

### 2. The real failure is in the STDLIB, not in `src/os/`

`simple compile src/os/userlib/fs.spl` reports:

```
parse: in ".../src/lib/common/encoding/utf8.spl":
  Unexpected token: expected Newline, found Identifier { name: "rt_text_count_codepoints_cached" }
```

The failing file is `src/lib/common/encoding/utf8.spl` — a stdlib dependency —
and the failing construct is a **single-line `unsafe` suite body** at
`utf8.spl:255` (also `:260`, `:265`):

```
unsafe(capabilities: [ffi]): rt_text_count_codepoints_cached(s)
```

Reduced fixture, RED on the deployed seed with the identical message:

```
extern fn rt_text_count_codepoints_cached(s: text) -> i64

fn f(s: text) -> i64:
    unsafe(capabilities: [ffi]): rt_text_count_codepoints_cached(s)
```

The indented form of the same code parses fine — confirming the gap is the
inline suite, not the capability list.

The originally-reported line number (21, the multi-line braced
`use std.encoding.simd_text_ffi.{...}`) is a **misreported location**: prefix
fixtures of `utf8.spl` lines 1-25 parse clean. The seed points at the first
occurrence of the identifier's *name*, not the failing token's site. That
misdirection is what sent the prior lane at the `use`/`export` forms.

## This is case (a) — a parser bug — and it is ALREADY FIXED IN SOURCE

`src/compiler_rust/parser/src/unsafe_inline_body_test.rs` exists at
`origin/main` and pins this exact defect, quoting the exact error text:

> `unsafe(capabilities: [...]): expr` with a ONE-LINE body was rejected with
> "expected Newline, found Identifier": `parse_unsafe_block_primary` called
> `parse_block`, which accepts only the indented form. This is the shape used
> at 8+ sites in `src/os/kernel/boot/mmio_hardware.spl`, which had been
> expanded to indented blocks as a workaround.

The fix (`parse_inline_or_block`, `src/compiler_rust/parser/src/parser_helpers.rs:178`)
landed **2026-08-30** (`9d74c705e53`). The deployed seed binary
`bin/release/x86_64-unknown-linux-gnu/simple` was built **2026-08-26** — four
days earlier. It predates its own regression test.

**So: no product source should be reformatted, and no parser fix needs
writing. The deployed seed binary is simply stale relative to its own source
tree.** The regression test already ships in the parser crate; a redeploy is
the whole fix.

## Consequence for the "bootstrap redeploy" question

A full pure-Simple bootstrap redeploy (to clear the stage-binary SEGV,
`stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`) is
strategically still needed, but it is **not required to unblock this gate**:
the runner's designed fallback parses the server payload with the Rust seed,
and rebuilding the seed from `origin/main` un-stales that path.

## Separate, genuine finding: self-hosted parser lacks multi-line `export`

While the seed supports comma-continued `export`, the **self-hosted** parser
does not — `src/compiler/10.frontend/core/parser_decls_use.spl:380-383`
(`parse_export_decl`) breaks out of its item loop on any non-comma token and
never skips Newline/Indent. **56 `.spl` files under `src/` use the multi-line
form.** This is a real bootstrap divergence that a redeploy will hit, and it
matches the "found Dedent" signature the prior record reported — but against
the self-hosted parser, not the seed. Filed here for whoever performs the
redeploy; out of scope for this lane.

## Resolved: the `get_arm64_wm_qemu_target()` spec contradiction

The prior record left this open. It is settled: **the two `wm_entry.spl`
assertions are stale; the production-render contract spec is correct and is
currently RED because the SOURCE is what lags.**

Evidence chain:

1. `src/os/_QemuRunner/runner_targets.spl:545` still has
   `entry: "examples/09_embedded/simple_os/arch/arm64/wm_entry.spl"`, with
   `output: "build/os/simpleos_arm64_wm.elf"`. The predicate
   `_is_arm64_wm_qemu_target` (`os/_QemuRunner/os_build_run.spl:712-714`, and its
   mirror at `src/os/qemu_runner_part2.spl:628`) matches the same string.
2. `wm_entry.spl` is explicitly **legacy**:
   `scripts/check/check-simpleos-x86-64-wm-render-event-evidence.shs:4` —
   *"The old implementation built arch/x86_64/wm_entry.spl, a hand-drawn legacy…"*.
3. **x86_64 already completed this migration**: `runner_targets.spl:720`
   `get_desktop_gui_target()` uses `arch/x86_64/gui_entry_desktop.spl`.
   arm64 is lagging a finished migration.
4. **Decisive**: the arm64 readiness gate has ALREADY migrated —
   `scripts/check/check-simpleos-arm64-wm-qemu-readiness.shs:8,88` sets
   `ENTRY=.../arch/arm64/gui_entry_desktop.spl`. So the lane *script* builds
   `gui_entry_desktop.spl` while the QEMU *target* still names `wm_entry.spl`.
   That is an internal inconsistency in the product, not in the contract spec.
5. History: the contract spec's intent-bearing commit is `f2ffa11a188`
   *"feat(simpleos): require process-owned arm and riscv desktops"* — newer than
   the substantive commits behind the two asserting specs (`ae55a746719` /
   `6f86ff32a7d`, `f12958a4d51`). It is a **requirement** spec, deliberately
   written ahead of the source.
6. Both entries exist; `get_arm64_desktop_engine2d_target()`
   (`runner_targets.spl:558-573`) already uses `gui_entry_desktop.spl`.

Correct fix (NOT applied here — it repoints the shared `arm64-wm-ramfb` lane,
which cannot be revalidated until a kernel builds, and is not needed for the
Engine2D gate):

1. `runner_targets.spl:545` — `entry:` -> `.../arch/arm64/gui_entry_desktop.spl`,
   KEEPING `output: "build/os/simpleos_arm64_wm.elf"` (the contract spec asserts
   exactly that pairing, and the `output` is what keeps the predicate
   distinguishable from the engine2d target).
2. `os_build_run.spl:713` and the mirror `qemu_runner_part2.spl:628` — same
   string swap so the predicate keeps matching.
3. `test/01_unit/os/qemu_runner_extended_spec.spl:301` and
   `test/03_system/gui/arm64_wm_qemu_contract_spec.spl:156` — expect
   `gui_entry_desktop.spl`. Their `target.output` assertions stay valid.
