# enum_assoc_fn_residual_exposure — non-spec blast radius of the enum-static defect

Lane: ENUMEXP (2026-07-28). **Triage and measurement only — no `src/**` file was
modified.** Report:
`doc/08_tracking/bug/enum_assoc_fn_residual_exposure_2026-07-28.md`.

Parent bugs: `enum_associated_fn_never_called_on_jit_2026-07-28.md`,
`enum_associated_fn_vacuous_spec_sweep_2026-07-28.md`.

**Parallel session overlap (not a clobber, but read this first):** another
session is editing `src/compiler_rust/compiler/src/mir/lower/lowering_expr_call.rs`
(+44 lines, mtime 10:58) — the call-lowering path this bug lives on. The binary
measured here was built 05:45, **before** that edit, so all numbers describe the
deployed seed and not the in-flight fix. Re-run `build/enum_exposure/probe_*.spl`
after the next seed rebuild. This lane touched no `src/**` file.

## Result

| | |
|---|---|
| src/** non-spec files with a high-confidence hit | 51 (146 sites) |
| proven reachable from a bootstrap entry (import closure) | 7 |
| empirically wrong under the JIT today | 3 of 5 probed |
| protected today by whole-program JIT demotion | 2 of 5 probed |
| ambiguous bucket | 229 files / 1611 sites / 80 names — **mostly false positives** |
| fixed immediately | none (rationale in the report) |

## Three findings that change the picture

1. **Not JIT-only.** An AOT artifact from `simple compile -o …smf` gives the same
   wrong answer (`EQ_NEITHER`) as the JIT. The interpreter is the only correct
   engine, and the native/board path has no fallback. Also: plain `==` is wrong,
   so this is not a `match` artifact.
2. **The ambiguous bucket shrinks, it does not grow.** The prior sweep dropped
   `SdnValue.*` (351 hits) as ambiguous. Resolved: 66 of the 77 src non-spec hits
   are **lowercase-named enum VARIANTS** (`SdnValue.i32`, `.f32`, `.text`,
   `.bool` in the seed stdlib), which both sweeps misread as calls because their
   variant detector requires an uppercase initial. Only 7 are real. The other 79
   ambiguous names are still unresolved and must not be counted as exposure.
3. **Two of the five "clean" probe results were measuring the wrong engine.**
   `OptimizationConfig.speed()` and `ChecksumAlgo.from_tag(0)` came back green
   until the demotion grep showed the whole program had fallen back to the
   interpreter (`Unknown type: Lexer`; `[W1006] mutation without mut capability`
   — both pre-existing, unrelated). Every JIT probe must be checked for
   `falling back to interpreter`.

## Live-wrong sites (JIT, not demoted, real production modules)

- `Platform.from_u8(1)` (`src/compiler/70.backend/linker/smf_enums.spl`) —
  neither `Linux` nor the documented `Any` fallback. SMF wire decoder.
- `CompileMode.from_text("aot")` (`src/compiler/00.common/driver_core_types.spl`)
  — a mode that is not `Aot`; `--mode aot` silently degrades to interpret.
- `SdnValue.int(42)` (`src/lib/common/sdn/value.spl`) — repo-wide config format.

Latent, not live: `bin/simple` is the **Rust bootstrap seed** today, so
`src/compiler/**` is not in the normal tool path. It lands the moment a
self-hosted binary is deployed.

## Method notes for whoever picks this up

- `SIMPLE_NO_JIT` is a decoy — no reader in `src/compiler_rust/`. Only
  `SIMPLE_EXECUTION_MODE` (`driver/src/exec_core.rs:73`) works.
- One probe per site, no dicts and no payload-binding `match` — both demote.
- `bin/simple run` has no `--source` flag; run probes from the repo root and let
  module resolution find `compiler.*` / `os.*` / `std.*`.
- The CPU guard kills a long run at 60s: `SIMPLE_TIMEOUT_SECONDS=<secs>`.
- Reachability instruments used, in order of strength: import closure from
  `src/app/cli/{main,bootstrap_main}.spl` (817 files, 238 module paths
  unresolved — presence proves reachable, absence proves nothing); runtime
  demotion check; entry-in-its-own-right; empirical A/B.

## Tooling bug fixed (build/ only)

`build/enum_vacuous_sweep/sweep.spl` crashes on the full file list —
`string index out of bounds: index is 22 but length is 22` on a `# … O(n²) …`
comment. Byte-vs-character family: `.len()` is bytes, `[i]` is characters, so
`tail_ident`'s backward walk from `s.len()` overruns, and
`substring(0, index_of("#"))` leaks comment text. Fixed in the adapted copy
`build/enum_exposure/sweep2.spl` (character-array walk; `split("#")[0]`).
The original is untouched. **Earlier `sweep.spl` results undercounted.**

## Next

1. Parent-bug step 1 (JIT `func_ids` miss → hard error) gates all 146 sites.
2. `FsNodeKind.from_u8` (`src/os/userlib/fs.spl:59,83`) has **no definition
   anywhere** — implement or delete.
3. Confirm `35.semantics/semantics/binary_ops.spl` (13 sites) and
   `30.types/bidir_phase1a.spl` (6) are dead; no importer found for either.
4. Resolve the remaining 79 ambiguous names.
5. Teach both sweeps that enum variants may be lowercase.
