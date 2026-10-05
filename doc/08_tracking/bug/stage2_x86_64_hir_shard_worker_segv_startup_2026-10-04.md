# Stage 2 x86_64 Linux: HIR-shard worker SEGV at startup (claimed=0)

- **Filed:** 2026-10-04
- **Status:** FIXED for the crash (root cause repaired upstream by `01c7e678a79`,
  re-qualified here on x86_64 Linux); release tip additionally needed three
  nominal-field repairs (this change) before Stage 2 would build at all.
  The bootstrap sanity smoke's 180 s budget, exceeded by the cold source
  inventory alone, is met since 2026-10-05 (see "Remaining blocker: fixed").
- **Host:** WSL2 Ubuntu 26.04, x86_64, clang/lld 21, no LLVM 23, so Stage 2 used
  `--backend=cranelift`.
- **Related:** `native_extension_method_default_argument_2026_10_04.md` (same root
  cause found on Windows; that record says "native qualification pending" —
  this record is the x86_64 Linux qualification),
  `2026-10-04_seed_nominal_field_slot_zero_fallback.md` (the slot-zero guard whose
  fail-closed errors the three repairs below clear).

## Reproduction (before)

Checkout at `6bdf543f91d` (release/1.0 line), bootstrap:

```
LLVM_CONFIG=/usr/lib/llvm-21/bin/llvm-config SIMPLE_NATIVE_FILE_TIMEOUT=1800 \
  sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2 \
  --mode=dynload --jobs=8 --backend=cranelift
```

Stage 2 built, sanity failed: `candidate_frontend_smoke: p2_add-build failed (raw rc=124)`.
Running the smoke's command by hand with the rejected candidate `$C`
(`SIMPLE_SCV_INVENTORY_COLD_INIT=1 ... $C native-build --backend cranelift
--runtime-bundle core-c-bootstrap --entry-closure --entry
src/compiler/bootstrap_admission/p2_add.spl --mode one-binary ...`) gave, after
~500 s (cold source inventory), and 1304 s under `strace`:

```
[hir-shard] owner=0/1@0 status=CRASH exit=-139 claimed=0 sealed=0 finished=false
error: HIR aggregate failure; final worker and artifact publication blocked
```

The worker is spawned by `run_hir_shards` (`src/app/cli/native_build_main.spl`)
as `$C run src/app/cli/native_build_worker.spl <args> --hir-shard=0/1`.

## Faulting frame

Core dump of the worker (`ulimit -c unlimited`, unstripped candidate, gdb):

```
SIGSEGV SEGV_MAPERR si_addr=0x28
#0 native_entry_closure_owner.native_entry_closure_request_open_v1+685
     and 0x20(%rdx),%rcx   ; rdx = request & ~7 = 0  (request.binding)
#1 driver_source_pipeline_loading.CompilerDriver.load_sources_impl+1776
#2 driver_orchestration.CompilerDriver.compile_with_reverse_reference_owner_v1+1643
#3 driver_orchestration.CompilerDriver.compile
#4 driver.compiler_driver_run_compile
#5 native_collection_profile.native_build_compile_with_collection_profile
#6 compile_targets._cli_native_build
```

At `#2` the caller sets only `rdi` (receiver) before `call load_sources_impl`;
`rsi` held a stale `0x8`. In `#1`, `if val request = preclosed:` evaluated
`rt_is_some(0x8)` = true (nil is `3`), `rt_unwrap_or_self` gave `0`, and the
callee dereferenced it. Worker died before claiming any module.

## Root cause

`load_sources_impl(preclosed: NativeEntryClosureRequestV1? = nil)` is defined in
an `impl CompilerDriver:` block in `driver_source_pipeline_loading.spl`, and is
called as `self.load_sources_impl()` from `driver_orchestration.spl` (and
`driver.load_sources_impl()` from `driver_source_llvm_ir.spl`), neither of which
imports the defining module. The Rust seed's HIR lowerer only padded omitted
trailing defaults from the caller's own declarations or from directly imported
modules, so the extension method's default was never materialised and the
callee read an unset argument register. Stage 2 is built by the seed
(`SIMPLE_NATIVE_BUILD_RUST=1`), so the miscompile is in the seed.

Not a transplant rewind: owner files checked against `88aac2ffe28`; only
`driver_source_llvm_ir.spl` matches an older blob, and it was unchanged by the
transplant (pre == post).

## Fix

1. **Defaults (the crash):** already on release/1.0 as `01c7e678a79`
   "fix(bootstrap): propagate native extension method defaults to callers"
   (global unambiguous `Owner.method` default map in `native_project/imports.rs`,
   consulted by `lower_method_call`; folded into the cross-module fingerprint).
2. **Stage 2 build on the release tip (`8287f9bc3a6`, unchanged at `487d64cfac3`)**
   failed with 3 files under the slot-zero fail-closed guard (`730fb7e3009`):
   - `25.traits/trait_solver.spl`: `case Named(symbol, _): symbol.name` — the
     payload is `SymbolId`, which has only `id`. The old seed silently read slot 0
     (the i64 id) as text. Now `"symbol#{symbol.id}"`, which matches the solver's
     own `impls_by_type` keying by `SymbolId`.
   - `70.backend/linker/elf/tls_relax.spl` and
     `80.driver/smf_group_object_adapter.spl`: read `obj.symbols[i].name` without
     importing `ElfSymbol`; with three `ElfSymbol` declarations in the tree the
     seed could not bind the layout (`elf_parser`'s has `name` at slot 6, not 0).
     Added `ElfSymbol` to the existing `elf_parser` import, the same narrow repair
     as the `Template` import in `lazy_instantiator.spl`.

## Evidence (red -> green)

Seed probe — three modules: `class Drv` in `drv_type`, `impl Drv: me load(p: Req? = nil)`
in `drv_load`, and `impl Drv:` callers `self.load()`, `self.load(nil)`,
`self.load(<nil var>)`, `self.load(Some(Req(x: 5)))` in `drv_orch`; built with
`SIMPLE_NATIVE_BUILD_RUST=1 <seed> native-build --backend cranelift`:

| seed | omitted | explicit nil | nil var | Some(5) | rc |
|---|---|---|---|---|---|
| old seed (`9852dae5…`, from 6bdf543f91d) | 128745488853836 | 128745488853836 | 128745488853836 | SEGV | 139 |
| new seed (`290b24b1…`, from 8287f9bc3a6) | 7 | 7 | 7 | 105 | 0 |

(The same-module `self.load()` returned 7 in both cases.)

Stage 2 build: release tip without repairs, `FAILED FILES (3)` (the three above);
with repairs, `Cache: reused 0 modules; rebuilt 1189`, candidate produced
(32,670,480 B).

p2_add, run by hand with the new candidate (same command as above, timeout 3000 s):
`[hir-shard] done shard=0/1 lowered=1 claimed=1`, `completed_workers=1
failed_workers=0`, `Artifact published`, rc=0 in 608 s; running `p2_add`
prints `5` (fixture `EXPECT stdout: 5`), rc=0. Old candidate: CRASH exit=-139,
claimed=0.

## Remaining blocker

The bootstrap's sanity smoke still reports `p2_add-build failed (raw rc=124)`
because its budget is 180 s and the new candidate needs 608 s, ~500 s of which
is the cold source inventory (`SIMPLE_SCV_INVENTORY_COLD_INIT=1`) before the
first HIR shard is spawned, plus ~75 s link. The crash is gone; the time budget
is not met. The next step is either to make the inventory warm or cheap for the
smoke, or to fix the cold-inventory performance under the native candidate.

## Remaining blocker: fixed (cold inventory performance, 2026-10-05)

Measured on the rebuilt candidate (`b17935f2…`, same command as above) by
attaching gdb every 20 s (18 samples until the first HIR shard):
44,758 `.spl`/`simple.sdn` files under `src`+`test`, 307 MB, 7.4M lines. No
per-file processes (one `git ls-files`), no re-reads; the time was runtime
calls per line and per byte:

| where | share | cause |
|---|---|---|
| `compile_source_inventory_event_from_content_v1` canonicalization | ~55% | ~35 runtime calls per source line (split, trim, `split_whitespace`'s split + per-token trim, join, seven prefix tests), each validating its operands through the global heap registry |
| `sha256_text` -> `rt_tls13_sha256` (Rust lane) | ~33% | the accelerator read its `[u8]` argument with one registry-checked `rt_array_get` per byte |
| `compile_source_inventory_digest_valid_v1` | ~10% | 64 `byte_at` calls per digest, ~4 checks per entry |

A second profile after the first fix showed `rt_contains` (what
`text.contains(text)` lowers to) at ~40%: its string branch scanned
`windows(n).any(==)`, a memcmp call per haystack byte; plus the 64-substring +
join hex encoder in `sha256_u8_fast_hex`.

Fix (digests and admission semantics unchanged; nothing was narrowed):

- `src/lib/scv/compile_source_inventory_core.spl`: files whose only
  whitespace is space/newline are canonicalized with whole-text
  replace/split (`compile_source_inventory_whole_text_*_v1`); any other
  character `trim` could remove (tab, CR, VT, FF, Unicode White_Space) keeps
  the per-line reference path. Digest validation reads one bulk byte copy.
- `src/lib/common/crypto/sha256.spl`: hex digits written into one `[u8]`.
- Rust runtime (`collections.rs`, `sffi/hash/sha256.rs`): `rt_tls13_sha256`
  reads the array through one validated borrow with the same accept/reject
  contract; `rt_contains` on strings uses the SIMD byte finder
  `rt_string_find` already used. These are runtime (not codegen) changes, so
  Stage 2 needed a `--full-bootstrap --invalidate-cache=stage2` rebuild.
- Spec: `test/01_unit/lib/scv/compile_source_inventory_whole_text_spec.spl`
  (whole-text == per-line reference for texts and all five event digests,
  ineligible-whitespace routing built from raw bytes, digest validation);
  mutation-checked. Rust: `test_bulk_byte_read_matches_per_element_contract`,
  `test_rt_contains_string_matches_window_scan`.

Timing, same command, same host, back to back (load 1.8-5.6):

| candidate | until first HIR shard | total | p2_add output |
|---|---|---|---|
| before `b17935f2…` | 276 s | 312 s | `5` |
| after `b34e25f3…` | 107 s | 139 s | `5` |

(Under load ~12 the before run took 439 s, ~360 s of it inventory.) The
bootstrap rebuild with this change passed `candidate_frontend_smoke` and
wrote `stage2-sanity: pass` for `b34e25f3…`. The run then stopped at
`stage2-compiler-tests` on an unrelated precondition: delegated rows need
`SIMPLE_MCDC_OFF_WAIVER_REASON` (or `BOOTSTRAP_STAGE2_TEST_DELEGATE=0`).

Still slow, not addressed here: 107 s of cold inventory remains; the
next costs are per-line allocations inside `split`, path/plain-checkout
validation (`split("/")` per entry), and the heap-registry lookup (a global
mutex + SipHash `HashMap`) that every runtime string/array call performs.
