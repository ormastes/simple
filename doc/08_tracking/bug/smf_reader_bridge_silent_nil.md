# BUG: SMF reader bridge returns silent nil — six unimplemented `rt_smf_reader_*` externs

- **Filed:** 2026-08-01
- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 04).
  decision for the SMF bridge itself needs the **link owner**
- **Severity:** High. Not a crash — a silent wrong answer. The reader reports
  success for files it never read.
- **Related:** `doc/02_requirements/language/features/eliminate_dummy_impls.md`
  (STUB-007-010, REQ-PREV-002)
- **Gate fix landed:** `61ad6b7f53b40557ffd0b6d8e2984f65e04c63b0`

## Summary

`src/compiler/70.backend/linker/smf_reader.spl` declares six
`extern fn rt_smf_reader_*` symbols and calls all six. **None of them is
implemented anywhere in the tree.** An unregistered extern does not fail to
link, so the failure is silent.

The practical behaviour is worse than a crash. `rt_smf_reader_open` returns `0`;
the guard is `if handle < 0`, which is false; so `SmfReaderFfi.open()` returns
`Ok(..)` for **any** path, including one that does not exist. Every subsequent
read returns hardcoded empty data. The net effect is a reader that claims every
SMF file parses cleanly and contains zero symbols.

## Enumerated surface — every `rt_smf_*` extern

Enumerated with `/usr/bin/grep` (pinned; the default `grep` here is ugrep and
the two have silently disagreed on exclusion patterns).

| Symbol | Declared at | Implemented? | Called? | Disposition |
|---|---|---|---|---|
| `rt_smf_reader_open` | `smf_reader.spl:31` | **NO** | yes (`:43`) | defer — needs owner |
| `rt_smf_reader_read_header` | `smf_reader.spl:32` | **NO** | yes (`:50`) | defer — needs owner |
| `rt_smf_reader_read_section` | `smf_reader.spl:33` | **NO** | yes (`:73`, `:230`) | defer — needs owner |
| `rt_smf_reader_read_symbol_table` | `smf_reader.spl:34` | **NO** | yes (`:77`) | defer — needs owner |
| `rt_smf_reader_read_string_table` | `smf_reader.spl:35` | **NO** | yes (`:81`) | defer — needs owner |
| `rt_smf_reader_close` | `smf_reader.spl:36` | **NO** | yes (`:85`) | defer — needs owner |
| `rt_smf_write` | `smf_writer.spl:268` | **NO** | **NO** — dead | **DELETED** this change |
| `rt_smf_parse_relocs` | spec-local | **YES** — `interpreter_extern/file_io.rs:539,550` | yes | keep, healthy |
| `rt_smf_relocs_from_path` | spec-local | **YES** — `interpreter_extern/file_io.rs:646,654` | yes | keep, healthy |

Name-variant check performed before concluding anything was missing (precedent:
`ffi_regex_*` turned out to exist as `sffi_regex_*`). No `sffi_smf_*`,
`ffi_smf_*`, or any other prefix variant of the reader entry points exists. The
source comment points at `src/rust/loader/src/smf/ffi.rs`; **`src/rust/` does
not exist in this repo.**

## A working pure-Simple SMF reader already exists

`SmfReaderMemory` — `smf_reader_memory.spl`, a re-export facade over
`_SmfReaderMemory/header_parser.spl` (666 lines) and
`_SmfReaderMemory/symbol_parser.spl` (253 lines), **no externs** — already
implements the whole capability against a `[u8]`: magic detection
(`has_smf_magic_at`), header parsing (`parse_header_from_bytes`), string table
location (`locate_string_table`), symbol parsing, `read_code`,
`read_elf_object`, `read_relocations`.

It also has **more consumers** than the FFI reader (`module_loader`,
`object_provider`, `object_mapper`, `module_loader_lib_support`,
`linker_wrapper_lib_support`, `smf_getter`) and a spec
(`smf_reader_memory_spec.spl`).

So the correct resolution is almost certainly **not** to write six new Rust
externs. It is to re-route `SmfReaderImpl` onto `SmfReaderMemory` — read the
file to bytes, then `SmfReaderMemory.from_data` — and delete the six
declarations. Same shape as the `ffi_regex_*` de-duplication: the right move was
deleting the dead duplicate, not registering a second unreachable copy.

## Why this is not being done in this lane

The rework crosses the `SmfReaderImpl` / `SmfReaderMemory` type seam
(`SmfHeader` vs `SmfMemoryHeader`, `Dict<text, SmfSymbol>` population,
`read_template_section`, `read_note_sdn`, the `find_section_by_type` fallback
table) and touches every consumer of `SmfReaderImpl`: `smf_cache.spl`,
`smf_getter.spl`, `object_resolver.spl`, `object_provider.spl`, `link.spl`,
`module_loader.spl`. That is a subsystem re-scope in the linker's core
object-reading path, not a straggler cleanup. **Link owner's call.**

## Decision requested from the link owner

1. Re-route `SmfReaderImpl` onto `SmfReaderMemory` and delete the six externs
   (recommended — the capability already exists in pure Simple), **or**
2. implement the six externs in the Rust runtime (contradicts pure-Simple-first
   policy, and duplicates working code), **or**
3. delete `SmfReaderImpl` outright and migrate its six consumers directly to
   `SmfReaderMemory`.

`@extern("bare", ...)` is **not** an option for any of these: none is a
baremetal intrinsic, and `bare` is a declaration-side marker that never reaches
the link layer — it is not a parking space.

## What this change does

- **Deletes** the dead `extern fn rt_smf_write` declaration
  (`smf_writer.spl:268`). Proved dead: exactly one occurrence in the tree — its
  own declaration inside a function body that returns `Ok([])` unconditionally,
  never calling it. Repo rule: never leave unused code.
- **Adds six `pass_todo` markers**, satisfying REQ-PREV-002, whose absence in
  `smf_reader.spl` / `smf_writer.spl` is exactly why this gap stayed invisible.
  `pass_todo` lowers to `Value::Nil` (`interpreter_call/builtins.rs:698`), so
  adding it as a leading statement does not change any return value.
- **Corrects** the false source comment claiming the externs are implemented at
  `src/rust/loader/src/smf/ffi.rs`.
- Does **not** implement the bridge. See above.

## Gate defect found and fixed first (landed separately)

`scripts/check/check-extern-registration.shs` was supposed to catch exactly this
class and **did not report `rt_smf_reader_open` at all**. Root cause: its
declaration extractor matched only lines containing `@extern`, so the bare
`extern fn sym(...)` form — how all six SMF externs are declared, and the
dominant form in the tree (~9,554 lines / ~3,797 distinct bare-only symbols vs
~172 `@extern` lines) — was invisible.

The script's own header proves the silent-nil behaviour using
`extern fn rt_bogus`, the very form it could not parse.

- **RED (before):** `extern_decl_total=164`, `rt_smf` findings **0**,
  `extern_registration_ok=true`
- **GREEN (after):** `extern_decl_total=9718`, `rt_smf` findings **7**,
  `extern_unregistered=2332`

Both self-test controls proved non-vacuous:

- sabotage A — drop the bare-form grep: vacuity guard trips, rc=1
- sabotage B — bare-form extractor silently drops one symbol while the
  declaration count stays high (invisible to the vacuity bound): the new
  `rt_array_len` per-form control trips, rc=1

The pre-existing `rt_file_read_text` control could not have caught this: it is
declared in **both** surface forms, so it stays green even when the bare-form
extractor dies. `rt_array_len` is bare-only and heavily registered, so it
reaches the registered set only via the bare-form path.

Vacuity bound raised 100 → 5000 (strengthened, not weakened): the old bound was
low enough that losing ~97% of declarations still sailed past it.

**The 2,332 unregistered externs the fixed gate now reports are a pre-existing
backlog made visible, not new debt.** The gate remains report-only by default;
`--strict` still exits 1.

## Lane coverage caveat

The behavioural claims above (`open()` returns Ok for a nonexistent path; reads
return empty) are **INFERRED** from the unregistered-extern truth table plus
source reading, not executed. They were not re-measured here because
`bin/simple` currently has no `run`/`test` subcommand and `bin/simple_seed` is a
Jul-25 build. Note also that `simple_seed test` runs the tree-walking
interpreter, so any spec written against this would gate the **interpreter**
lane only — **not** the native/link lane where the weak zero-size stub
behaviour lives. A spec is therefore not sufficient certification for whichever
resolution the owner picks.

The enumeration table, the absence of implementations, the absence of
name-variants, the dead `rt_smf_write`, and every gate measurement above are
**PROVED** by direct grep and by running the gate.

## 2026-08-17 — fail-closed on a nonexistent path

Status: PARTIALLY FIXED.

Reproduced against current source: `rt_smf_reader_open` still has zero
implementations tree-wide (`git grep` finds only the declaration at
`smf_reader.spl:61` and its single call site). An unregistered extern returns 0,
the guard was `handle < 0`, so `open()` returned `Ok` for every path.

Fixed: `SmfReaderFfi.open` now checks `file_exists(path)` first and returns
`Err("failed to open SMF reader: no such file: ...")`. Behaviour for a path
that DOES exist is byte-identical, so no caller (link.spl:267,
object_provider.spl:222, lazy_instantiator.spl:190 — the only three) changes
outcome on any input it can succeed on today. That bounds the latent breakage
to zero without needing a full-suite measurement.

Still open (pass_todo retained): the five remaining `rt_smf_reader_read_*`
externs are still unimplemented, so a file that exists still reads back an
empty header, no symbols and no sections. The prescribed rework — re-route onto
`SmfReaderMemory.from_data` and delete the six dead externs — spans the
SmfReaderImpl/SmfReaderMemory type seam and is unchanged by this commit.

Spec: `test/01_unit/compiler/linker/smf_reader_open_fails_closed_spec.spl`
