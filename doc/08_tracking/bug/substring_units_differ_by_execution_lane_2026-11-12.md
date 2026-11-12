# `text.substring` slices bytes on some lanes and characters on others

**Status:** OPEN (observed 2026-11-12, aarch64, Linux; lane bootstrap-fable-9)
**Area:** language semantics / runtime (text)

## Observation

Probe (`/tmp/café/simple/src/app/cli/main.spl`, `é` = 2 bytes; byte index of
`/src/` is 17, character index 16):

| lane | `p.substring(18)` | unit |
|---|---|---|
| Rust seed `run` (JIT) and seed native (`native-build`) | `rc/app/cli/main.spl` | characters (MIR lowering → `rt_slice(text, start, end, 1)`, `lowering_expr_method.rs:1510`) |
| Rust seed interpreter method dispatch | bytes (`interpreter_helpers/method_dispatch.rs:174-182`, `s.as_bytes()`) | bytes |
| Stage 2 pure-Simple native (cranelift) | `src/app/cli/main.spl` (byte 18 = `s`); with the char index 17 it printed `/src/app/cli/main.spl` | bytes (`spl_str_slice`, `runtime.c:607`) |

`byte_at`/`byte_len` are bytes on every lane and `len()` is characters on
every lane; only `substring` disagrees. The 2026-08-30 record
`text_len_substring_bytes_but_index_chars_2026-08-30.md` documents the
byte-indexed form only.

## Why it matters

`module_source_relative_path` (and the Stage 2 admission fixture mirroring it)
finds `/src/` by byte scan and then slices with `substring`. With one multibyte
character before `/src/` the seed JIT lane produced `rc.app.cli.main` and the
Stage 2 lane (after the literal-length fix `b65bd26a49f`) `.src.app.cli.main`
when given the character index. The 11-07 `len() -> byte_len()` sweep
(`4183b795175`) assumed byte-indexed `substring` throughout; every caller that
computes an index from `byte_at`/`byte_len` and slices with `substring` is
correct on exactly one lane.

## Workaround in tree

`_module_path_naming_suffix_after` slices at the byte index, verifies the
suffix starts with the needle, and falls back to the character index. It is
correct on all three lanes and keeps the gate fixture `stage2_module_path_naming`
honest, but it is a workaround: the language needs one unit for `substring`
(and the seed's two engines must agree with the pure-Simple runtime).

## Unanswered

- Which unit is the contract. `doc/07_guide/quick_reference/syntax_quick_reference.md`
  should say; the three implementations should then be aligned and a
  cross-lane spec added (`bin/simple test ... --mode=interpreter|jit|native`).
