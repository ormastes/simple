# sdn.value SdnValue MIR errors are a nondeterministic parallel-HIR ordering race (2026-10-13)

Date: 2026-10-13. Lane: release_phase3 self-host bootstrap campaign.
Status: DIAGNOSED, NOT FIXED (cross-module redesign required; see below).
Cycle 25 evidence: test_runner_build.log —
`undefined variable SdnValue at src/lib/common/sdn/value.spl:48:9` +
`unresolved method call: Float (module: lib.common.sdn.value)` +
`B5b: match has multiple wildcard arms` (MIR aggregate failure after
252/252 modules).

## Reproducibility verdict

NOT deterministic from compiler source. Verified twice in this cycle with a
candidate rebuilt from the exact cycle-25 compiler source (tip 6ab1fd44e18,
src/compiler unchanged 46071964e05..6ab1fd44e18):

- test_runner verifier invocation, clean env: 0 SdnValue errors; MIR 252/252
  succeeded; build reached LINK and failed only on the known cross-module
  global-symbol layer (TEST_OUTPUT_CAPTURE_BYTES / decl_nodes slots).
- A probe-instrumented candidate (SIMPLE_DBG_ENUMREG eprints in
  module_build.spl register loop and expression_core.spl constructor
  conversion) also passed: exactly ONE HIR unit of value.spl (raw-SCV-path
  key), enum registered (owner-valid, kind=enum), both `SdnValue.Float`
  calls converted to EnumLit (owner=1).

Cycle 25 hit the failure; two runs on identical compiler source did not.
The ordering variable is the parallel HIR shard lane (module_workers=2):
module lowering shares one HirLowering symbol/registration state, so the
order in which the two keyings of the same source lower is racy.

## Mechanism (from probes + code)

1. The same physical file (src/lib/common/sdn/value.spl) is admitted into
   the closure under TWO module keys: the raw SCV snapshot path
   (`/home/.../build/scv/snapshots/scv-revision-v1-H/src/lib/common/sdn/value.spl`,
   used as a module name with slashes dotted) and the logical name
   (`lib.common.sdn.value`). Same duplicate-source family as
   seed_import_map_extern_identity_precedence_2026_10_12.md and the AOT
   empty-module fix 46071964e05, one phase earlier (HIR instead of AOT).
2. `register_enum_unit_patterns` (module_build.spl:344 loop, keyed by
   `self.symbols.lookup_or_invalid(local_name)` on the SHARED table) runs
   per lowered unit. When the raw-path unit lowers first, SdnValue's enum
   registration and `generic_enum_constructor_owners` entry land before
   `float()`'s body; when the logical-keyed unit's function bodies lower in
   the other order, the constructor conversion
   (declared_enum_constructor_owner, declared_enum_constructor.spl) finds
   no registration, keeps `SdnValue.Float(f)` as MethodCall(Var, Float),
   and MIR then reports the exact cycle-25 triple (Var unbound; method
   unresolved; the `match self` in is_null degrades to scalar arms ->
   duplicate wildcard).
3. c28f4cd5baa (sentinel pass-through) did not cause this: it only removed
   an earlier fatal that stopped the MIR phase before module ~231 of 252,
   exposing this latent race. The mcp/lsp closures did not trip it because
   their shard interleavings differ.

## Why no source fix landed this cycle

The correct fix is duplicate-unit elimination (or unit-key canonicalization)
in the surface/alias materialization -- the same file must not produce two
HIR units with split declaration ownership. That is a cross-module redesign
of the SCV admission path, explicitly out of one bounded cycle. A local
fallback in declared_enum_constructor_owner cannot work: in the failing
interleaving the receiver `Var(SdnValue)` itself is unbound (module-local
scope missing), so constructor conversion is not even reachable.

## Options for the campaign

- Serialize HIR module lowering for the artifact builds (module_workers=1)
  as a mitigation; the race window closes at a ~2x HIR-phase cost.
- Or schedule the duplicate-unit elimination fix (target:
  src/compiler/80.driver/driver_source_loading.spl surface admission +
  module_logical_name_from_path canonicalization for SCV snapshot paths).
- Cycle 26 may simply not hit the race; if test_runner_build fails again
  with the same triple, the racy order recurred -- rerun once before
  treating it as a regression.

Repro harness: build/repro-stage2-fix/run_runner_sdnrepro.sh (candidate
rebuilt from tip source, passed; runner_sdnprobe.log has the probe
evidence).

## Cycle 40 (2026-10-14): unit-key canonicalization fix landed

Cycle-39 verifier evidence re-confirmed the diagnosis: the triple fired again in
the verifier's own lane (frontend-policy pins + threads=4) while standalone
repros stayed clean. Root cause re-verified against code: `SourceFile.load`
(00.common/driver_source_file.spl) derived module_name with a LOCAL rule that
only strips a leading relative `src/`, so an absolute SCV snapshot path became
its own dotted-absolute module name -- a second keying of the same file next to
its logical name, the duplicate HIR unit whose register_enum_unit_patterns
ordering races. The shared `module_logical_name_from_path` /
`module_source_relative_path` derivation already handled absolute paths
correctly; the load path just did not use it.

Fix (commit on fix/mirtype-facade-selection-20261014): `SourceFile.load` now
routes non-`src/`-prefixed paths through `module_source_relative_path` (drops
everything before `/src/` or `/examples/`; passes everything else through
unchanged), then applies the existing strip. One file == one module key at the
source; the second HIR unit can no longer exist, so the race window closes by
construction (complementing the cycle-33 per-process hir-dedup guard).

Verifier-shaped verification (frontend pins SIMPLE_SHARD_MEM_CLAMP=1,
SIMPLE_PARSE_SHARD_MAX=1, PARSE/HIR shard worker KB clamps, tree budget 3GB,
--source composition set, --threads 4, SCV cold lane):
- test_runner: hir-fatal 0, SdnValue triple 0, MIR 252/252 succeeded=0-failed
  (cycle-39 fired the triple exactly here), reached link 192/192 objects.
- Probes PASS THROUGH under the verifier-shaped config: 120 surface-ident rows
  (parent AND shard processes) + sibprobe lines reach the build output.
- compiler_cli: cycle-39's trace32 admission error GONE (0 occurrences);
  see the companion bug doc for the Failure-1 scoping fix. A residual
  'unresolved import os.cli' appears ONLY in the cold-init snapshot
  replication lane (the 3GB-clamped snapshot copy lacks src/os/cli.spl);
  the verifier's checkout-path lane has the file and passed it in cycle 39.

### mono-033 frontier classification (same session)

The verifier-shaped test_runner gate and the proven-shape cli control run both
pass the previously-failing stages and stop one layer later at monomorphize:
E-MONO-033 (127 unspecialized generic call sites, tree-wide: _sffi_tuple_get,
mutex_lock, _sffi_enum_discriminant, ...). Baseline control with the PRE-FIX
candidate (stage2-owner, cycle-39 code) hits the identical E-MONO-033 with
hir-fatal 0 -- so the mono frontier is PRE-EXISTING and latent (no logged
compiler_cli run ever reached mono before; cycles 37-39 died at HIR or
silently at the enum-contract boundary). Not a regression from the cycle-40
fixes. Next campaign target: monomorphization generic-identity keying.

## Cycle 41 in-vivo analysis (2026-10-14): single-process lane, probe verdict pending

Cycle-41 verifier evidence (build/verifier-logs-cycle41/test_runner_build.log,
probe battery exported, triple FIRED again):

1. WHY 35 PARENT-ONLY DUMP ROWS, NO SHARD ROWS: the real verifier's test_runner
   build runs HIR SINGLE-PROCESS. Zero `[hir-shard]` lines in the log; the HIR
   cache is OFF in this lane (hir-cache hits=0 misses=252 comes from the
   cache-dir probe lines but `hir_shard_mode = hir_shard_active() and
   hir_closure_digest != ""` -- without SIMPLE_HIR_CACHE the closure digest is
   empty and shard mode never engages). One process freezes one registry, so
   surface-ident dump rows are all shard=parent. The 120-row parent+shard
   captures in the standalone harness came from the harness setting
   SIMPLE_HIR_CACHE=1, which the real verifier does not.

2. WHY lib.common.sdn.value IS ABSENT FROM THE 35 ROWS: the dump only prints
   SURFICIOUS surfaces (module_name != preferred_registry_name, or canonical
   != fold(path-truth)). In the checkout lane the file's single surface is
   clean under that filter, so it simply is not dumped. The dump cannot see a
   duplicate unless the duplicate surface is itself suspicious. The file IS
   parsed once (parse current=src/lib/common/sdn/value.spl) and aliased twice
   (surface_alias done=449/450 of 502 -- two alias rows, e.g. lib./std.
   spellings of one surface -- NORMAL).

3. WHY THE ABSOLUTE-PATH CANONICALIZATION MISSES THIS LANE: this lane has NO
   absolute paths -- everything is checkout-relative (`src/lib/...`), where
   SourceFile.load's original derivation was already correct. The duplicate
   keying the canonicalization killed (dotted SCV snapshot path) does not
   exist here. Code re-verification: the cycle-33 canonical-reuse guard and
   the phase_hir_modules stores are FIRST-WINS and run unconditionally (not
   shard-gated), so a same-name overwrite or second lowering is structurally
   prevented in single-process mode. value.spl declares NO generic functions
   (no mono specialization can originate from it). Remaining candidates for
   the declaration loss: (a) the HirModule payload for lib.common.sdn.value
   reaches the ctx handoff WITHOUT its enums (loss inside lowering/reuse), or
   (b) the payload is intact and the loss is in monomorphization or MIR's
   per-module scope build.

NEW PROBE (lands with this analysis, env-gated, default off):
SIMPLE_SDN_RACE_TRACE=1 emits one line per module at each handoff:
  `[race-trace] hir-final module=<name> enums=<n> classes=<n> functions=<n>`
      (driver_hir_pipeline_lowering, at ctx publish)
  `[race-trace] mono-final module=<name> enums=<n> classes=<n> functions=<n>`
      (driver_hir_pipeline_passes, after monomorphization)
Cycle-42 verdict rule: lib.common.sdn.value with enums>=1 at hir-final but
the triple still fires -> loss is post-handoff (mono or MIR scope build);
enums=0 at hir-final -> loss is inside the HIR lowering/reuse lane (keying).
Add SIMPLE_SDN_RACE_TRACE=1 to the verifier probe battery.

### E-MONO-033 gate result + next frontier (same session, commit da1a119c29e)

Full compiler_cli closure (proven-shape harness, fresh cache, candidate
stage2-mono): mono `[mono] generic_fns=142 call_sites=942 specializations=199
unresolved=0`; E-MONO-033 = 0, E-MONO-032 = 0, E-MONO-036 = 0 (down from
127 unresolved). HIR 2564/2564 clean. test_runner verifier-shaped likewise
reached link 192/192 (stops at the known pre-existing cross-module
global-symbol layer). NEW FRONTIER: the compiler_cli MIR phase now SEGFAULTs
(signal 11) at phase start (done=0, 40 mir-lower lines) -- first time MIR
lowers the newly-specialized bridge bodies in this closure; a native crash,
not a diagnostic. Next cycle: backtrace from core per the driver's own
message.

## Cycle 42 fix (2026-10-14): MIR enum-name scope miss -- registry fallback in the static-receiver arm

Probe verdict from cycle 42 (SIMPLE_SDN_RACE_TRACE): lib.common.sdn.value
enums=1 at hir-final AND mono-final -- the payload carries the enum through
both handoffs. The loss is IN THE MIR PHASE: lowering value.spl:48 fails with
`undefined variable SdnValue` (the NamedVar PRE-DISPATCH arm at
expr_dispatch.spl:5070 -- note: no colon, a THIRD error site) + `unresolved
method call: Float`. Root cause chain: `SdnValue.Float(f)` arrives as
MethodCall(NamedVar(SdnValue), "Float"); the enum-constructor reclassification
(method_calls_literals.spl:1922) needs static_receiver_name (empty -- HIR
hint absent) or the unique-variant-leaf fallback (dead: FOUR enums declare a
Float variant -- hir inference/types.spl, gc_async_mut pure/ast.spl,
common/parser/ast.spl, SdnValue); `try_lower_declared_enum_static_call`
(static_enum_receiver_owner.spl -- the OPEN 2026-10-11 repair, tests
UNEXECUTED) should rescue it via the lexical symbol lookup, but
`self.symbols.lookup("SdnValue")` MISSED while the module's enums payload,
the numeric-id tables, and the register_enum_variants bare-name registry all
had it -- the SymbolTable NAME index is the only structure that lost the
entry (the BOOT-20 chain-table family at 252-module scale; tiny repros with
1-3 modules never reproduce it).

FIX (static_enum_receiver_owner.spl, NamedVar branch): when the lexical
lookup misses, fall back to the MIR enum variant registry
(enum_variant_index, populated from the SAME HirModule enums dict at
lower_module start), unambiguous bare name only (enum_bare_ambiguous
excluded): variant -> lower_enum_construct_named; otherwise pass the owner
hint through to lower_method_call (static-method dispatch). No broad enum
matching, no bare-homonym fallback beyond the unambiguous registry key.

Verification (checkout lane = cycle-41's real verifier configuration,
verifier pins, --source composition set, --threads 4, fresh caches):
- test_runner: SdnValue TRIPLE 0 (was: fired in cycles 25, 39, 41), hir-fatal
  0, MIR 252/252 COMPLETE for the first time in this lane; link 192/192;
  stops at the known pre-existing cross-module global-symbol layer
  (undefined g__<snapshot-revision-path>__*_slot, documented in
  module_source_relative_path's docstring).
- compiler_cli checkout-lane: hir-fatal 0, triple 0, E-MONO-033 0; blocked
  before HIR by the worktree-local os.cli snapshot-selectivity artifact
  (campaign worktree passes admission per cycle 41). Prior proven-shape run:
  HIR 2564/2564, mono unresolved=0, MIR SIGSEGV at phase start (signal 11,
  pre-existing native crash; needs a core backtrace -- unrelated to the
  enum path, which now lowers).
- Specs: numbered-path 4/4, frozen-alias-retry 6/6.
- Repro fixtures kept at test/_probe_root_tmp/sdn (out-of-tree; the plain
  and cross-module-collision variants PASS -- the miss needs the
  252-module table scale).
