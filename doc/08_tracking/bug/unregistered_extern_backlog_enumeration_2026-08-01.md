# Unregistered `extern` backlog — real enumeration after the extractor fix

Companion to `unregistered_extern_silent_nil_2026-08-01.md`. That document's
counts (385 declarations, 75 actionable) were produced by an extractor that
matched **only lines containing `@extern`**, so the bare `extern fn sym(...)`
form — the dominant declaration style in this tree — was invisible to it. The
extractor was fixed in `61ad6b7f53b`; this file records the real population.

**This is not new debt.** Every symbol below predates the fix. The jump from 75
to ~2.4k is a measurement correction, not a regression, and must not be read as
one.

## Measurement

Run at tip `e57d171eba2e`, `scripts/check/check-extern-registration.shs`,
default (report) mode. Counted with `/usr/bin/grep` (GNU); the host default
`grep` is ugrep and the two were checked to agree.

```
extern_decl_total=14321
extern_registered=2614
extern_bare_exempt=30
extern_unregistered=2377     <- 1308 unique symbols
```

`--strict` exits 1 at this count, as intended. It stays unflipped.

## What each lane does with an unregistered symbol

Unchanged from the parent doc, repeated because every triage decision depends on
it: an unregistered extern does **not** fail to link.

| lane | behaviour | reachable by a spec? |
|---|---|---|
| A1 pure-Simple MIR interp | silent `0` | yes |
| A2 seed, `@extern fn` | silent `Value::Nil` | yes |
| A2 seed, `extern fn rt_*` | logged, then `0`, exit 0 | yes |
| B Cranelift JIT | errors, de-JITs into A2 | yes |
| C1 seed native link | **weak `return 0` stub** for any non-`rt_` name | **no** |
| C2/C3 freestanding | weak `return 0`, ratcheted / `auto_stubs.c` | **no** |

`simple test` runs the tree-walking interpreter through the seed child, so a
spec gates lanes A1/A2 only. The weak-stub behaviour that makes this dangerous
lives in the **native/link** lane, which no spec in this repo reaches. Any claim
about C1/C2/C3 needs a native build, not a green suite.

## Population by bucket

Rows are declaration sites; `uniq` is distinct symbol names (many symbols are
declared in several modules).

| bucket | rows | uniq | first-pass disposition |
|---|---:|---:|---|
| `lib-other` (`src/lib/**` misc) | 473 | 356 | triage individually; largest unknown |
| `os-baremetal` (`src/os/**`) | 374 | 291 | **likely `@extern("bare", ...)`** — freestanding by construction |
| `app-io` (`src/app/io/**`) | 315 | 210 | live CLI surface; highest wrong-answer risk |
| `gpu-ml` (gpu/engine2d, engine3d, torch) | 286 | 202 | check for pure-Simple twins first |
| `other` | 262 | 231 | triage individually |
| `generator-spec` (sffi_gen/specs, app/ffi_gen.specs) | 200 | 124 | scope question, not a gap — see below |
| `net` | 194 | 92 | check for pure-Simple twins first |
| `trace32-debug` | 165 | 12 | 12 symbols x ~14 duplicate declarations |
| `test` | 108 | 61 | fixtures; several are deliberate negatives |

## Cheap first passes, measured

**Prefix rename (`ffi_` / `sffi_` / `rt_` / `_`).** Only **58 of 1308** unique
symbols have a same-stem variant present in the native sources. This precedent
is real — it retired the 8 `ffi_regex_*` — but it does **not** scale: it explains
~4% of the population. Machine list: `extern_backlog_variant_hits.tsv`.

**Pure-Simple twin (the SMF pattern).** **328 of 1308** unique symbols have a
same-named (69) or same-stem (259) pure-Simple `fn` somewhere in the tree. This
is the highest-yield lead by a wide margin and is where triage should start —
but each hit still needs confirming by hand, because Simple resolution is
**module-scoped**: a same-named `fn` in another module does not resolve the
extern. That exact mistake is why `fn _cos` in `engine3d/types3d.spl` never
fixed `game2d/transform.spl`. Machine list:
`extern_backlog_simple_twin_candidates.txt`.

**Baremetal tagging.** 374 rows sit under `src/os/**`. `bare` is the sanctioned
exemption and only 30 declarations carry it today. If most of `src/os/**` is
genuinely freestanding, tagging it is a large, low-risk reduction that needs one
owner decision rather than 291 investigations. This is a labelling gap, not an
implementation gap — but it must be confirmed per family, not assumed, and
`bare` must not become a parking space for merely-unimplemented host symbols.

**Generator specs.** 200 rows are inputs to code generators. Treating these as
out of scope by *scope rule* is defensible; treating them as exempt is not. Note
one such file was already found to be entirely dead (`sffi_gen/specs/treesitter.spl`,
deleted in `c22135e98a7a`): it was not wired to the generator at all. So
"generator input" must be verified per file, not assumed from the path.

## Scope

2,377 declaration sites across 1,308 symbols is a program of work, not a lane.
It needs an owner and a per-bucket plan. What is defensible to do incrementally,
in this order:

1. Confirm/deny the `src/os/**` baremetal tagging question (1 decision, 374 rows).
2. Work the 328 pure-Simple-twin candidates — each resolved one either deletes a
   dead declaration or re-points it, with no new implementation.
3. Work `app-io` (315 rows) on live-call risk, since that is the shipping CLI.
4. Decide the generator-spec scope rule (200 rows) as a rule, once.

`--strict` cannot be flipped until this reaches 0, and nothing here should be
retired by adding a stub, an allowlist, or an env hatch — those were refused by
design, and a fabricated stub converts a silent nil into a silent nil with
paperwork.

## Already retired

`c22135e98a7a`, `a89db70d01cd`, `35bac4c475fa`, `502af609d9a5` retired 71 of the
originally-visible 75 by deletion of dead code and by re-pointing
`walk_directory` at the registered `rt_dir_walk`. Those remain valid — they were
real unregistered symbols — they were simply a ~3% sample of the family.

Full machine-readable enumeration: `extern_backlog_enumeration.tsv`
(`symbol<TAB>file:line`, 2377 rows).
