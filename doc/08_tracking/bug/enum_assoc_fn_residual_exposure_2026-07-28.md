# Residual exposure of the enum-associated-function defect in NON-spec code

- **Date:** 2026-07-28
- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
  immediate fix")
- **Parent bugs:**
  `doc/08_tracking/bug/enum_associated_fn_never_called_on_jit_2026-07-28.md`,
  `doc/08_tracking/bug/enum_associated_fn_vacuous_spec_sweep_2026-07-28.md`
- **Binary under test:** `bin/simple` →
  `bin/release/x86_64-unknown-linux-gnu/simple`, which prints *"this Rust-built
  Simple binary is a bootstrap seed only"*. **All evidence below is attributed to
  the Rust bootstrap seed**, not to a pure-Simple self-hosted binary.
- **Concurrent work — read before re-measuring.** A parallel session is editing
  `src/compiler_rust/compiler/src/mir/lower/lowering_expr_call.rs` (+44 lines,
  mtime 10:58), i.e. the call-lowering path this bug lives on. The binary
  measured here was built at 05:45, **before** that edit. Every result below
  therefore describes the *deployed* seed, not the in-flight fix. Re-run the
  probes in `build/enum_exposure/` after the next seed rebuild; do not assume
  they still hold. This lane did not touch that file.

## Headline

| | |
|---|---|
| src/** non-spec files with a high-confidence hit | **51** (146 call sites) |
| …of those, **proven** reachable from a bootstrap entry | **7** |
| …of those, **empirically confirmed wrong under the JIT today** | **3 of the 5 probed** |
| …**protected today** by whole-program JIT demotion | **2 of the 5 probed** |
| src/** non-spec files in the ambiguous bucket | 229 (1611 sites, 80 receiver names) — **substantially false-positive**, see below |
| Files needing an immediate fix | **0** (reasoning below) |

The defect is **not JIT-only**. An AOT artifact produced by `simple compile` is
wrong in exactly the same way, so "run it interpreted" is the only safe engine
and the native/board path has no interpreter to fall back to.

## Baseline reproduction (this session, this binary)

`build/enum_exposure/p_base.spl` / `p_eq.spl` — a 12-line enum with one
`static fn make() -> E1: E1.B`, no imports, no dicts:

| engine | invocation | result |
|---|---|---|
| JIT (default) | `bin/simple run p_base.spl` | `got NOTHING` |
| interpreter | `SIMPLE_EXECUTION_MODE=interpreter bin/simple run p_base.spl` | `got B` |
| JIT, `==` instead of `match` | `bin/simple run p_eq.spl` | `EQ_NEITHER` |
| interpreter, `==` | same | `EQ_B_OK` |
| **AOT artifact** | `simple compile p_eq.spl -o p_eq_native.smf` then `bin/simple p_eq_native.smf` | **`EQ_NEITHER`** |

The AOT row is new and matters: the repo rule *"production wrappers should
execute cached compiled artifacts, not raw source"* means the wrong answer is
what a production wrapper ships.

`match` is not the trigger — plain `==` against the correct variant is equally
wrong, so the value really is neither variant, not a pattern-matching artifact.

## How the file list was produced

Adapted from the prior tooling at `build/enum_vacuous_sweep/sweep.spl` into
`build/enum_exposure/sweep2.spl` (input list = `git ls-files '*.spl'` minus the
two vendor trees, 34,281 files; 2,583 enum declarations, 1,515 unique enum
names).

### Two corrections to the prior sweep

**1. The dropped-ambiguous-name weakness, handled explicitly.** The original set
`strict = false` for any receiver whose name is *also* declared as a
class/struct/trait anywhere in the tree, which silently discarded `SdnValue.*`
(351 hits). `sweep2` keeps those in an explicit `AMBIG` bucket and records
**both** declaration site lists (`build/enum_exposure/ambiguous_names.tsv`) so
each name can be resolved by hand. 80 names, 1,611 sites in src/** non-spec.

**2. Resolving the ambiguity shows the bucket is mostly FALSE POSITIVES — the
real count is LOWER than the lower bound, not higher.** Worked through on
`SdnValue`, the name that motivated the concern:

- `enum SdnValue` at `src/lib/common/sdn/value.spl` and
  `src/compiler_rust/lib/std/src/sdn/value.spl`; the `struct SdnValue` at
  `src/compiler/70.backend/backend_types.spl` and
  `src/compiler/80.driver/init.spl` is an unrelated compiler-local type.
- Of the 77 `SdnValue.*` hits in src/** non-spec, **66 are variant
  constructions, not associated calls**: the seed stdlib enum declares
  *lowercase-named variants* — `bool(bool)`, `i32(i32)`, `f32(f32)`,
  `text(text)` — and both sweeps' variant detector only accepts an
  uppercase-initial body line, so `SdnValue.i32(x)` was misread as a call.
- Only **7** are real associated functions (`SdnValue.null` ×6,
  `SdnValue.empty` ×1, in `src/lib/common/sdn/`), plus `typed_table` /
  `named_table`.

**Therefore the whole `AMBIG` bucket (1,611 sites) must be treated as unresolved,
not as exposure.** Lowercase-named enum variants are legal here and are the
dominant false-positive class. Resolving the remaining 79 names is the obvious
follow-up; it is not exposure until resolved.

### A bug found in the tooling itself

`sweep.spl` crashes on this repo's file list with
`string index out of bounds: index is 22 but length is 22`. Root cause is the
known byte-vs-character family (`.claude/memory` →
`reference_byte_vs_character_index_bug_family.md`): `.len()` returns **bytes**
but `[i]` indexes **characters**, so `tail_ident`'s `var i = s.len(); s[i - 1]`
walks off the end of any line containing a multi-byte character — here a
`# ... O(n²) time complexity` comment. The same mismatch made
`substring(0, index_of("#"))` leak comment text. Both are fixed in `sweep2.spl`
(character-array walk; `split("#")[0]`); the original `sweep.spl` is left
untouched. **Any earlier result from `sweep.spl` on a list containing that file
stopped early and undercounted.**

## How reachability was determined

Four independent instruments; **no rating below is inferred from the path name.**

**Method A — import closure from the documented bootstrap entries.**
`build/enum_exposure/closure.spl` BFSes `use` edges from
`src/app/cli/bootstrap_main.spl` and `src/app/cli/main.spl` — the entry points
named in `.claude/rules/bootstrap.md` (line 31, and the `native-build --source
src/compiler --source src/lib --source src/app --entry …` recipe at 163–165).
Result: **817 files**, output at `build/enum_exposure/closure.txt`.
*Limitation, stated plainly:* 238 module paths did not resolve (numbered
directory components like `70.backend`, repeated components like
`99.loader/loader/`, and the `src/compiler` symlink spellings). **Presence in
the closure is proof of reachability; absence is not proof of unreachability.**

**Method B — runtime demotion check.** Compile the real module under the JIT and
grep the run for `JIT compilation failed, falling back to interpreter`. This is a
*measurement*, not an assumption: a module that cannot be HIR-lowered is never
JIT-executed today, whatever the import graph says. Two of five probed modules
are in this state (reasons quoted below). Note this is exactly the trap in the
brief — the first `OptimizationConfig` and `ChecksumAlgo` probes came back
**green and were measuring the interpreter**; only the demotion grep exposed it.
`SIMPLE_NO_JIT` was never used (confirmed decoy: no reader in
`src/compiler_rust/`; the only env reader is `SIMPLE_EXECUTION_MODE` in
`driver/src/exec_core.rs:73`).

**Method C — entry in its own right.** `src/compiler/80.driver/main.spl` is a
`main`, reachable when run directly, not by being imported.

**Method D — empirical A/B on the real module.** Import the production module,
call the production associated function, compare against the correct variant
with `==` (no dicts, no payload-binding `match` — both demote), run under default
and `SIMPLE_EXECUTION_MODE=interpreter`, capture to a file, read the tail, take
`$?` from the command under test.

## Empirical results — top sites (Method D)

| # | Site | Probe | JIT | interpreter | demoted? | verdict |
|---|---|---|---|---|---|---|
| 1 | `src/compiler/70.backend/linker/smf_enums.spl` via `smf_header.spl` | `Platform.from_u8(1) == Platform.Linux` | `SMF_PLATFORM_BOGUS` | `SMF_PLATFORM_OK` | no | **LIVE WRONG** |
| 2 | `src/compiler/00.common/driver_core_types.spl` via `80.driver/main.spl` | `CompileMode.from_text("aot") == CompileMode.Aot` | `COMPILEMODE_WRONG_VARIANT` | `COMPILEMODE_OK` | no | **LIVE WRONG** |
| 3 | `src/lib/common/sdn/value.spl` | `SdnValue.int(42) == SdnValue.Int(42)` | `SDN_INT_BOGUS` | `SDN_INT_OK` | no | **LIVE WRONG** |
| 4 | `src/compiler/60.mir_opt/mir_opt_integration.spl` | `OptimizationConfig.speed() == Enabled(2)` | `OPT_SPEED_OK` | `OPT_SPEED_OK` | **yes** | not JIT-reachable today |
| 5 | `src/os/services/nvfs/core/pmap.spl` | `ChecksumAlgo.from_tag(0) == Ok(CRC32C)` | `CKSUM_CRC32C_OK` | `CKSUM_CRC32C_OK` | **yes** | not JIT-reachable today |

Probes: `build/enum_exposure/probe_*.spl`; outputs `*.jit.txt` / `*.interp.txt`.

Demotion reasons for #4 and #5 (quoted from the run, and both are *pre-existing,
unrelated* lowering failures — not a fix):

- #4 `HIR lowering error: Unknown type: Lexer`
- #5 `HIR lowering error: Memory safety error [W1006]: mutation without mut capability … _put_u64_le at 108:22`

Result #1 is the sharpest: `Platform.from_u8` is documented to return
`Platform.Any` for unknown input, and the JIT returns something that is neither
`Linux` *nor* the documented fallback — so no defensive `else` in the caller
catches it.

## Ranked exposure list

Rating key — **HIGH**: wrong value steers a build/wire/policy decision;
**MEDIUM**: wrong value corrupts a user-visible result or diagnostic;
**LOW**: cosmetic, dead, or protected today.

### HIGH

| Sites | File | Symbols | Consequence of a value matching no arm |
|---|---|---|---|
| 4 | `src/compiler/70.backend/linker/smf_header.spl` | `Platform.from_u8`, `Arch.from_u8`, `CompressionType.from_u8`, `SmfAppType.from_u8` | **Wire-format decoder.** A compiled module's platform/arch decode to no known value, so an object for the wrong target is neither accepted nor rejected correctly, and a compressed section is decompressed with an unknown algorithm. **Empirically live (#1).** In closure (A). |
| 3 | `src/compiler/70.backend/linker/smf_reader.spl` | same three | Same decoder, reader path. In closure (A). |
| 3 | `src/compiler/70.backend/linker/_SmfReaderMemory/header_parser.spl` | same three | Same decoder, in-memory path. In closure (A). |
| 6 | `src/compiler/80.driver/main.spl` | `CompileMode.from_text` ×6 | **Build-pipeline decision.** `--mode aot` selects a mode that is not Aot; `_compile_mode_or` (L26–29) then silently lands on the `CompileMode.Interpret` fallback, and `apply_option` (L250) reports `Unknown mode:`. Users get an interpreted build when they asked for a compiled one. **Empirically live (#2).** Entry in its own right (C). |
| 1 | `src/compiler/80.driver/init.spl` | `CompilerMode.from_text` | Same class, driver initialisation. |
| 6 | `src/compiler/00.common/config.spl` | `CompilerProfile.from_text`, `TypeDefault.from_text` ×4 | Compiler profile and default-type policy resolve to no known value → silently the wrong global compile policy. In closure (A). |
| 5 | `src/compiler/60.mir_opt/mir_opt_integration.spl` | `OptimizationConfig.none/debug/size/speed/aggressive` | Optimisation level for codegen. In closure (A), but **JIT-demoted today (#4)** — exposure is via the AOT/native build only, where there is no fallback. |
| 2 | `src/compiler/80.driver/pipeline_fn.spl` | `OptimizationConfig.debug`, `.speed` | Same. In closure (A). |
| 3 | `src/compiler/99.loader/loader/smf_cache.spl` | `Platform.from_u8`, `Arch.from_u8`, `InstantiationStatus.from_str` | **Cache identity.** A cached module keyed on a bogus platform/arch is served to the wrong target, or never hits. |
| 1 | `src/os/services/nvfs/core/pmap.spl` | `ChecksumAlgo.from_tag` | **On-disk integrity.** A stored checksum tag decodes to no algorithm → data verified with the wrong algorithm or not at all. JIT-demoted on host (#5); the board takes the native path with no interpreter. |
| 2 | `src/os/userlib/fs.spl` | `FsNodeKind.from_u8` ×2 (L59, L83) | **VFS `stat`/`readdir` node kind.** Files vs directories vs devices become indistinguishable. Worse than the rest: `grep` finds **no definition of `FsNodeKind.from_u8` anywhere** — it is the undefined-method form the parent bug describes, which the JIT accepts silently and the interpreter rejects. |
| 1 | `src/os/kernel/replay/mode.spl` | `KernelReplayMode.from_i32` | Kernel replay/record mode selection on the board. |
| 1 | `src/compiler/70.backend/interrupt.spl` | `CpuException.from_vector` | Exception vector → exception kind; a mis-decoded vector mishandles a fault. |

### MEDIUM

| Sites | File | Symbols | Consequence |
|---|---|---|---|
| 13 | `src/compiler/35.semantics/semantics/binary_ops.spl` | `BinaryOpResult.error` ×11, `.string` ×2 | Binary-operator type errors become a value matching no arm → **type errors silently not reported**. Downgraded from HIGH on reachability: **`grep` finds no `use …semantics.binary_ops` anywhere and it is not re-exported from `35.semantics/__init__.spl`** — apparently dead. Confirm before spending a fix. |
| 6 | `src/compiler/30.types/bidirectional_checking.spl` | `InferMode.is_check`, `.is_synthesize`, `.expected` | Type-inference direction (check vs synthesize) chosen wrongly. Re-exported from `30.types/__init__.spl`, but that `__init__` is not in the CLI closure. |
| 6 | `src/compiler/30.types/bidir_phase1a.spl` | same | Same; **no importer found at all** — likely a superseded phase file. |
| 19 | `src/compiler_rust/lib/std/src/core/persistent_list.spl` | `PList.of` | Persistent-list constructor in the seed stdlib; loaded for `use std.*`. Wrong list identity in any consumer. |
| 10 + 5 | `.../host/async_nogc_mut/io/term.spl`, `.../host/async_gc_immut/io/term.spl` | `TermError.from_code` | Terminal error codes decode to no known error → wrong or swallowed I/O errors. |
| 3 | `src/compiler_rust/lib/std/src/tooling/lint_config.spl` | `LintName.from_str`, `LintLevel.from_str` | **Lint policy.** A configured level decodes to nothing → a rule is silently neither on nor off. |
| 7 | `src/lib/common/sdn/` (`SdnValue.null` ×6, `.empty` ×1) | | **Wire/serialisation.** SDN is the repo's config/data format. **Empirically live (#3).** Only 7 real sites — the other 66 `SdnValue.*` hits are lowercase variants, not calls. |
| 3 | `src/lib/common/ui/builder.spl` | `SizeClass.to_wire`, `Orientation.to_wire` | UI **wire encoder**: widget size class / orientation serialise to a bogus tag. |
| 2 | `src/lib/common/ui/widget_store_ops.spl` | `WidgetKind.from_wire`, `LayoutKind.from_wire` | Decoder half of the same wire format. |
| 2 | `src/compiler_rust/lib/std/src/mcp/core/protocol.spl` | `ContentBlock.text` | MCP protocol content block — wire format for the shipped MCP servers. |
| 1 | `src/compiler_rust/lib/std/src/mcp/multi_lang/__init__.spl` | `Language.from_extension` | Wrong language inferred for a file in MCP tooling. |
| 1 | `src/compiler_rust/lib/std/src/tooling/deployment/containers.spl` | `Platform.from_string` | Container target platform. |
| 1 | `src/lib/hardware/fpga_linux/riscv_fpga_linux.spl` | `Xlen.isa_string` | rv32 vs rv64 ISA string for FPGA bring-up. |
| 3 (files) | `src/lib/{nogc_sync_mut,nogc_async_mut,gc_async_mut}/package/installer/__init__.spl`, `…/package/dist.spl` | `InstallerPlatform.all`, `Platform.all` | Package installer/dist platform matrix. |
| 1 | `src/compiler/80.driver/trace_config.spl` | `TraceLevel.from_text` | Trace verbosity resolves to nothing → tracing silently off (or on). |
| 4 | `src/compiler/00.common/effects.spl` | `EffectTag.combine_all` ×4 | **All four sites are inside `test_effect_combine_all` in the same file** (L369–372), not production effect inference — MEDIUM only because those in-file assertions are themselves vacuous. |

### LOW

Debug/report/replay-metadata decoders and enumerations of a fixed set; a wrong
value shows up as a mislabelled record rather than a wrong decision:

`src/lib/nogc_sync_mut/replay/{event_log,event_kinds,trace_format}.spl`,
`…/replay/process/{replayer,event_types}.spl`,
`…/replay/semantic/trace_events.spl`, `…/replay/adapters/jit_replay.spl`,
`src/lib/nogc_async_mut/replay/qemu_replay.spl`
(`Arch.from_text`, `*EventKind.from_i32`) — replay/trace record labels;
`src/lib/{nogc_sync_mut,nogc_async_mut,gc_async_mut}/src/exp/run.spl`
(`RunStatus.from_text`) — experiment status text;
`src/lib/nogc_async_mut/process_set/config.spl`
(`ProcessMode.from_text`, `IpcTransport.from_text`);
`src/app/qemu/commands.spl` (`Arch.from_text`) — QEMU harness arch flag;
`src/lib/nogc_sync_mut/websocket/{frame,handshake}.spl` (`Platform.timestamp`) —
a clock read, not a decision;
`src/compiler_rust/lib/std/src/tooling/compiler/severity.spl`
(`Severity.reset_color`) — terminal colour;
`src/compiler_rust/lib/std/src/spec/gherkin.spl`
(`Given.to_string/description/is_setup/summary`) — spec report text;
`src/compiler_rust/lib/std/src/core/primitives_numeric.spl` (`E.ln`);
`src/app/interpreter/collections/persistent_dict/node.spl`
(`HamtNode.split_leaf`);
`src/app/model3d/main.spl`, `src/lib/common/wfc.spl` (ambiguous bucket).

## Nothing needed an immediate fix — why

The brief allows fixing a HIGH-risk site whose wrong behaviour is *provably live
today*. Three sites are provably wrong under the JIT (#1 `Platform.from_u8`,
#2 `CompileMode.from_text`, #3 `SdnValue.int`), but "the constructor returns the
wrong value when called" is not the same as "a production run is producing wrong
output today", and the difference decides the fix:

- #1 and #2 are in `src/compiler/**`, the **pure-Simple self-hosted** compiler.
  `bin/simple` is currently the **Rust bootstrap seed**, so that code is not
  executing in the normal tool path today. The exposure is real but **latent**,
  and it lands the moment a self-hosted binary is deployed — which is exactly
  when a native build, with no interpreter fallback, makes it unconditional.
- #3 is live whenever a `.spl` tool calls `SdnValue.null()` / `.empty()` under
  the default engine, but only 7 such sites exist and none was shown to run in a
  current production path. Patching them would be the churn the brief forbids.

Applying the free-function/class-static workaround at any of these would also
*mask* the compiler defect from the next person measuring it. The correct order
is the parent bug's step 1 — make the JIT's `func_ids` miss an **error** instead
of a silent fall-through — after which every one of these 146 sites either
compiles or fails loudly, and this list becomes mechanical.

**One thing was fixed:** the byte-vs-character crash in the sweep tooling
(`build/enum_exposure/sweep2.spl`), because the measurement could not run
otherwise. No `src/**` file was modified by this lane.

## Follow-ups

1. Parent bug step 1 (JIT `func_ids` miss → hard error) gates everything else.
2. Confirm whether `35.semantics/semantics/binary_ops.spl` and
   `30.types/bidir_phase1a.spl` are dead; if so delete them rather than fix them.
3. `FsNodeKind.from_u8` has **no definition** — implement or remove the two
   call sites in `src/os/userlib/fs.spl`; this one is wrong on every engine that
   does not error.
4. Resolve the remaining 79 ambiguous receiver names the way `SdnValue` was
   resolved here. Expect most to be lowercase-variant false positives.
5. Teach both sweeps that enum variants may be lowercase, so the
   variant-vs-associated-call split stops depending on capitalisation.
6. The spec suite still cannot see any of this: `test_runner_single.spl:328-329`
   forces `SIMPLE_EXECUTION_MODE=interpret`. Until a JIT/AOT lane exists, every
   number here has to be measured by hand.

## Artifacts

All under `build/enum_exposure/` (not committed):
`sweep2.spl`, `closure.spl`, `all_calls.tsv`, `src_files_strict.tsv`,
`src_per_symbol.tsv`, `ambiguous_names.tsv`, `ranked_raw.tsv`, `closure.txt`,
`probe_*.spl` with paired `.jit.txt` / `.interp.txt` outputs.
