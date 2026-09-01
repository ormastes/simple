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
