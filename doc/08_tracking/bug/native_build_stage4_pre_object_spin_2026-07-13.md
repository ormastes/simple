# Native-build Stage 4 dispatch and strict-link blockers

## Status

Dispatch fixed; strict Stage-4 link blocked. The earlier quadratic entry-closure
scan and canonical Rust-seed dispatch bug are fixed. A fresh bounded build now
emits every object and fails honestly at the unresolved-symbol gate.

The 2026-07-15 source follow-up also routes the canonical Stage4 one-binary
`--entry` through the existing in-process pure-Simple project driver and clears
the raw native-all runtime path. Previously that shape still
called Rust `rt_native_build`, despite the production-path plan saying otherwise.
The route has static regression coverage; a fresh executable Stage-4 proof is
still pending and the provider-profile blocker below is unchanged.

## Reproducer

Run the Rust seed only as the bootstrap interpreter, with a fresh cache:

```sh
. scripts/setup/platform-detect.shs
PLATFORM="${PLATFORM_TRIPLE}"
SIMPLE_BOOTSTRAP=1 SIMPLE_BOOTSTRAP_STAGE4=1 \
SIMPLE_NO_STUB_FALLBACK=1 \
SIMPLE_RUNTIME_PATH=src/compiler_rust/target/bootstrap \
src/compiler_rust/target/bootstrap/simple \
  native-build --target "${PLATFORM}" \
  --backend cranelift \
  --source src/compiler --source src/app --source src/lib \
  --entry-closure --threads 4 --mode dynload \
  --entry src/app/cli/main.spl \
  --cache-dir build/native_probe/cache_stage4_targeted_4t \
  --runtime-path src/compiler_rust/target/bootstrap \
  -o build/native_probe/simple_stage4_targeted_4t
```

`PLATFORM` must be the triple returned by the canonical bootstrap platform
detector; it is intentionally not hardcoded in the command or script.

## Evidence

On 2026-07-13, a refreshed seed first exposed a parser recovery false positive:
valid Simple binders named `function` were rejected as TypeScript declarations.
The detector now requires an identifier lookahead, parser advancement reliably
buffers that token, and four focused Rust parser tests pass. A higher-capability
review accepted the Rust/Simple parity and focused Simple spec.

After that fix, a one-thread probe entered direct bootstrap discovery and found
1,043 modules, but its measured rate projected 19--20 minutes and exceeded the
900-second bound. It was stopped without loss because it had not emitted an
object. The four-thread retry reused no unproved objects, discovered the same
1,043 modules, compiled all 1,043 real object files with zero compile failures,
and preserved them in `build/native_probe/cache_stage4_targeted_4t`.

The strict link then failed with 120 unique undefined symbols: 102 `rt_*`
runtime/optional-provider symbols and 18 non-runtime Simple symbols. Inspection
of the automatically selected Stage-4 `libsimple_native_all.a` and its adjacent
runtime archive found none of those 120 definitions. The non-runtime group
includes imported-call/closure owners such as `run_check`, `run_arch_check`,
`json_serialize`, memory-debug helpers, and design-system helpers.

A final cache-preserving hypothesis check explicitly requested
`--runtime-bundle rust-hosted`; policy rejected it because that removed bundle
is not valid for `src/app/cli/main.spl`. Stage 4 already auto-selects its
authorized native-all artifact, so the flag was removed and no source or test
change was retained. No fourth build was launched after the mandatory
three-cycle cap, and no compiler or host-GPU PASS is claimed.

The earlier pre-dispatch spin exceeded the closest retained successful full-CLI
reference: 1,177 modules compiled and linked in 229.2 seconds. The fixed closure
walker itself completes about 498 files in 2.199 seconds, so CPU activity alone
was not evidence of healthy closure discovery.

## Root cause and mitigation

The seed dispatch treats a host `native-build` without `--target` as a
pure-Simple tool request and interprets `native_build_main.spl`; it does not
enter the Rust bootstrap builder. Existing retained evidence shows that adding
`--target x86_64-unknown-linux-gnu` starts discovery in seconds and completes
a 1,019-file build in 244.2 seconds.

The canonical seed Stage-4 branch now invokes the actual `native-build` command
with `--target "${PLATFORM}"`, using the already detected host triple rather than
a hardcoded architecture. The bootstrap fallback-policy integration spec locks
both the command and target into the seed branch. Instrumented verification
proves that mitigation converges through object emission.

The remaining fix belongs to two explicit owner classes, tracked by TODO 535:

1. Rebuild or correct the authorized Stage-4 hosted runtime/native-all artifact
   so required C and optional runtime owners are present without reopening a
   removed application runtime bundle.
2. Correct full-CLI entry-closure/import qualification or code generation for
   the 18 non-runtime Simple definitions.

Focused follow-up split the non-runtime group into 15 import/closure failures
and three lowering failures. The first shared import-map defect was an obsolete
blanket exclusion of every path containing `check.spl`; it suppressed the real
`cli/check.spl` and `cli/arch_check.spl` owners even though both were discovered
and compiled. The exclusion is removed, and the focused production-filename
import-map regression passes. This proves the owner fix for `run_check` and
`run_arch_check`; the strict full-CLI link has not been rerun, so the remaining
symbol count is not inferred or promoted to PASS.

The next shared closure defect was bare package facades such as
`lib.common.json.__init__`: native entry-closure discovery did not select the
cfg-active sibling that owns a bare exported name, and the re-export index used
the `__init__` file prefix rather than the package prefix. Discovery now selects
sorted, cfg-stripped AST providers with explicit export ownership preferred over
a unique implicit sibling definition, rejects ambiguous ownership, and queues
only the selected providers. Import indexing resolves direct and forwarded
owners to the parent package prefix through a deterministic fixed point; a
qualified import no longer falls back to the first global same-name candidate.
One adversarial regression executes and passes with a same-name reachable decoy,
wrong-architecture definitions, an unrelated sibling, and a two-hop forwarded
owner. Higher review rejected an intermediate first-candidate/stale-map form;
the accepted owner-set form publishes only final singleton mappings. Named
facade exports through sibling glob forwarders are queued without claiming
every name before indexing; a truly bare package `export *` now fails explicitly
instead of producing an incomplete closure. Final higher review passes. Both
direct-runtime guards pass and no direct `rt_*` use was added. The
strict full-CLI link remains deliberately unrun under the three-cycle cap, so
this is focused closure evidence rather than a compiler or QEMU PASS.

The next shared closure defect was a traversal boundary: both entry-closure
discovery and native import indexing inspected only module-level statements,
so a valid `use` nested inside a function or expression block could be parsed
and lowered to HIR but its owner never entered the native project. Both paths
now share one recursive AST walk that includes declaration bodies, statement
blocks, and expression-owned blocks. A synthetic regression places the import
under `if -> let -> lambda -> do-block`. Higher review rejected the first
partial visitor, the final bounded fix cycle closed its concrete declaration,
statement, metadata, macro, and expression carriers, and the expanded regression
passes 1/1. Final higher review passes the executable traversal and confirms
that the remaining pattern/type/signature metadata cannot hide a lowered nested
`use`. Function-local aliases still share the module-wide native use map,
so conflicting aliases in different functions remain open under TODO 556
instead of being hidden by this closure fix. The working-tree direct-runtime
guard passes and no source-level import hoist, direct `rt_*`, or symbol hardcode
was introduced. The strict full-CLI link remains unrun.

The first of the three true lowering failures was the bare `danger` symbol
emitted for standard-library `danger:` blocks. The Rust parser's generic
colon-block rule had represented the authorization boundary as a call with a
lambda argument. Rust now mirrors the pure compiler's existing `UnsafeBlock`
shape: contextual `danger:` and canonical `unsafe:` retain a lexical marker
through HIR, while ordinary `danger(...)` remains a call. MIR erases only the
marker and lowers the body once. Entry closure, suspension inference,
compilability, hygiene, symbol/security analysis, driver checks, lints, and
other material AST walkers recurse through the block. Focused parser and HIR
tests pass; an interpreter regression passes with a tail value, outer mutation,
and `continue` propagation, and the driver crate checks. TODO 557 records the
separate missing Rust safety pass that must reject raw/SFFI/asm operations
outside this retained marker. No linker exception, fake `danger` function, or
direct `rt_*` alias was added. The strict full-CLI link remains unrun, so the
two primitive method-dispatch failures and hosted runtime composition remain
open.

The final two non-runtime lowering failures had distinct semantic owners. The
parser treated every uppercase-leading identifier as a type path, so the typed
constant `DIRECTX_FRAME_HEADER_WORDS.to_u32()` became a zero-argument static
call named after the constant. Because spelling cannot distinguish an ALL_CAPS
constant from an acronym type such as `TCB`, the parser now retains all dotted
calls as receiver-bearing method syntax; HIR/interpreter semantic resolution
owns the value-versus-type decision. A focused HIR regression proves both the
typed constant conversion and `TCB.empty()` static call. Separately, native MIR mangling replaced qualified
`str.rfind` with the sole same-named method in the whole suffix index,
`DoubleEndedIterator.rfind`, despite the receiver types disagreeing. Qualified
calls now require a type-compatible candidate; only bare calls retain the
unique-candidate fallback. This preserves real class/trait dispatch and lets
the existing primitive codegen owners handle `i32.to_u32` and `str.rfind`.

The ALL_CAPS/acronym parser regression, semantic HIR regression, and adversarial
qualified-method regression each pass 1/1. A sidecar then found the interpreter's
legacy Path-only `Bitfield.new` dispatch. MethodCall now reuses the existing
bitfield constructor through the `interpreter_call` module boundary and mirrors
the old imported-enum fallback. Its focused interpreter regression executes and
passes 1/1 after the bounded continuation. The first compiler-test attempt also exposed four
recent Vulkan device-property wrappers constructing shared text from an owned
`String`; their owner now performs the required `SharedText` conversion and the
compiler test builds. No symbol exception, method-name allow-list, or new
direct `rt_*` call was added. The strict full-CLI link remains deliberately
unrun; hosted runtime/provider composition is still open and no compiler,
host-GPU, or QEMU PASS is claimed. Final higher review passes the bounded diff.

The refreshed bootstrap seed and native-all archive both build. The first
retained-cache strict follow-up then failed before compilation on ambiguous
facade ownership for `ExecutionConfig`: `config.spl` owns the public type while
`di.spl` contained stale nominal “forward declarations” for it and `LogConfig`.
DI now imports both canonical config types and deletes the duplicate structs
and impls. The next bounded run advanced to a second genuine collision:
`db.Table` is an SDN persistence detail, while `table.Table` is the public
columnar API paired with `Column`. The root facade no longer re-exports the DB
table and explicitly sources public `Table` from `table.spl`.

The next continuation verified that explicit `Table` ownership and advanced to
the frontend type-registry seam. `types.spl` owns the named, union,
intersection, and refinement registries; `type_checker.spl` now imports their
eight accessors instead of redeclaring them as extern providers. The second
strict run advanced again to `is_alpha`. The public lexer helper remains owned
by `lexer_chars.spl`; the semantically different AOP-local helpers, which also
admit underscore, are renamed for identifier start/continuation. The lexer
facade export is explicitly sourced and its redundant lexer-struct export is
removed.

The third and final bounded run verified both fixes and stopped on
`mono_cache_register`. `monomorphize.spl` owns the public key-to-declaration
cache, while `type_erasure.spl` owns an incompatible internal
name-and-type-arguments cache. The internal helper is renamed, the public export
is explicitly sourced from `monomorphize`, and the adjacent stale
`type_tag_name` extern is replaced with its canonical `types.spl` import. These
post-cap edits are intentionally unverified, uncommitted, and unsynced. The next
continuation may run one preserved-cache strict check; no resolver relaxation,
provider ordering, or symbol hardcode is allowed.

That continuation verified the monomorphization and `type_tag_name` ownership
repairs, then exposed duplicate root-facade paths for the split parser. The root
facade now sources expression and statement APIs from `parser_expr.spl` and
`parser_stmts.spl` exactly once while `parser.spl` retains its direct-import
compatibility API. The dead `parse_primary` export was removed; the real owner
is `parse_primary_expr`. The second strict run passed package discovery and
failed in `aot_compile_to_bytes` because an unannotated `Result.unwrap()` local
lost its `CompiledModule` receiver type. The existing typed-local pattern fixed
that one call; TODO 558 tracks the language inference defect rather than
silently treating the annotation as the final compiler behavior.

The third bounded run compiled every source module and reached strict link. It
now reports 112 unique undefined symbols: 101 `rt_*`, four `spl_memtrack_*`, and
seven non-runtime names. Compared with the retained 120-symbol baseline, 13 old
names are gone and five new names appear; four of those five are the correctly
lowered memory-tracker ABI names. The remaining non-runtime set is one untyped
`str.rfind` call, five design-system serialization/diff helpers, and
`font_atlas_composite_program_version_valid`. Runtime/provider composition and
those seven source owners remain open. No fourth build, host-GPU check, or QEMU
PASS is claimed.

Reuse the preserved 1,043-object cache only after one of those owners changes,
then run one bounded strict-link verification. Do not add stubs, relabel a
runtime bundle, hardcode symbols, or substitute the Rust seed as production
evidence.

The next bounded continuation restored the two historical Stitch theme-sync
owners and the shared font-atlas program-version contract that broad earlier
changes had removed while their callers remained. The theme CLI now consumes
the parsed-design-system accessors with explicit exports, and CUDA, Metal, and
OpenCL again share the same fail-closed font-program validator already used by
Vulkan. The Rust HIR keeps text-returning method results typed through
`replace(...).rfind(...)`; the pure-Simple bootstrap fallback selects the same
string runtime owner. TODO 559 records that fallback's remaining `-1` versus
Optional-nil semantic debt rather than accepting it as a general fix.

Two retained-cache strict links after the source restoration and review edits
compiled all 1,043 sources and converged on the same 105 undefined symbols:
101 `rt_*`, four `spl_memtrack_*`, and zero source-owned names. The seven prior
source gaps are therefore closed. The remaining gate is runtime/provider
composition under TODO 535; no host-GPU or QEMU PASS is claimed.

A read-only archive audit rejects using raw `libsimple_native_all.a` as a
compiler-only backfill. It defines 252 symbols also owned by the current core-C
sources, and the archive member containing `rt_cli_run_file` carries 453 global
definitions. Archive ordering, whole-archive, duplicate-definition allowances,
or symbol-name closure filters would only hide the ownership error. The safe
next boundary is a separately built compiler-hook archive whose defined-symbol
intersection with core/provider archives is gated at zero; Stage4 may compose
that disjoint artifact with core-C only after the gate exists. Provider-profile
closure and cache fingerprinting remain a separate follow-up.

The focused `src/app/cli/native_build_main.spl` probe narrows that boundary. Its
first retained-cache link reported 73 undefined names: 65 Cranelift hooks, three
runtime helpers, and five source-looking names. The source audit found two
generic `Result` receiver-inference defects, three nonexistent `to_text` method
resolutions, and a CUDA PTX constant incorrectly routed through color `to_hex`;
these are not valid reasons to import unrelated GPU, UI, or failsafe modules.
`rt_mkdir_p` already exists in core-C, while `rt_path_parent` and
`rt_time_now_monotonic_ms` have canonical pure-Simple core owners.

The focused bootstrap path now builds an ABI-disjoint compiler capsule from a
dedicated runtime-isolated crate. Its exact 73-hook contract is derived from
the crate exports and matches both canonical Simple facades; no manual symbol
manifest is used. The closure localizes every non-contract definition, removes
constructor/destructor sections, rejects undefined runtime symbols, and fails
if any definition overlaps the selected core/provider archive. The
only heap-shaped Cranelift crossing was replaced by a raw pointer/length object
emission entry behind the canonical Simple FFI/SFFI facades; the old
`RuntimeValue` entry remains a compatibility wrapper but is excluded from the
capsule. Selection is limited to the exact focused entry with both bootstrap
stage flags and forces a freshly built core-C provider. TODO 560 tracks removal
of the direct `rt_cranelift_*` ABI in favor of a typed provider surface. No
successful focused Stage4 link or QEMU receipt is claimed yet.

Focused cycle 2 used the refreshed driver, the dedicated capsule, strict
no-stub mode, and the retained cache. It stopped before link while phase 2
parsed a newly merged `launch_metadata.spl`: same-indent multiline bitwise OR
is accepted by the Rust frontend but the pure-Simple parser ended the
expression at the newline and reported the following pipe. The source now uses
the established whole-expression parenthesized form; TODO 561 tracks grammar
parity instead of treating that spelling as the language fix. The failure path
then dispatched `result.get_errors()` on the active
`CompileResult.ParseError` variant and lost the enum method owner. The CLI
failure funnel now calls the existing bootstrap-safe
`compile_result_errors(CompileResult)` owner directly.

The retained object cache was not the source of the parse failure—phase 2
reparses before object-cache use—but its key still omits imported-source hashes
and resolved provider ownership, and the pure-Simple cache records empty
dependency lists. TODO 562 tracks that independent invalidation hole. The final
bounded cycle therefore uses a fresh cache and will not be retried.

The third and final bounded cycle used that fresh cache and the refreshed seed.
It again stopped during phase 2 on the first bitwise pipe in
`launch_metadata.spl`, before any cache object or capsule link was produced.
Whole-expression parentheses did not alter the pure-Simple parser failure, so
that unsuccessful source normalization was reverted. The recovery fix did
work: the erroneous `ParseError.get_errors` dispatch is gone and the CLI now
reports the parser failure without a secondary semantic error. Per the
three-cycle cap, no fourth run is allowed. TODO 561 is the next root blocker;
the new compiler capsule remains unit/integration verified but has not yet been
exercised by a successful Stage4 link or QEMU run.

The follow-up root fix centralizes the lexer continuation contract in
`token_requires_rhs` and applies it to both the struct lexer and the legacy
module scanner. A trailing required-RHS token now suppresses physical newline
and continuation indentation without mutating the enclosing indentation stack;
open-ended `..` and ambiguous unary/postfix operators remain structural. The
focused pure-Simple regression mirrors `_launch_meta_le_u32`. Its execution is
currently blocked before the spec starts because the canonical release binary
identifies itself as the Rust bootstrap seed and aborts on unresolved
`rt_cli_arg_count`; the seed was not accepted as a normal test fallback. The
Stage4 three-cycle cap remains exhausted, so neither parser PASS nor a capsule,
host-GPU, or QEMU PASS is claimed.

The Linux compiler-only follow-up is now complete: the dedicated capsule derives and
exports exactly the 73 `rt_cranelift_*` hooks and rejects runtime/provider
ownership, overlap, unexpected globals, and constructors. A later strict full
CLI link still converged at 105 host-provider names with no Simple/source-owned
names, so TODO 535 no longer tracks compiler-backfill creation.

Independent Spark closure audits and highest-capability review on 2026-07-14
selected one remaining architecture: an internal, exact-entry
`stage4-cli-hosted` provider profile. The full CLI's SQLite, HTTP, GPU/font,
window, memtrack, SMF, and compiler command paths are advertised surfaces, not
safe import-pruning candidates. Stage4 must therefore link Simple objects, the
existing compiler capsule, capability-owned provider archives, core-C, and
system libraries in that order. It must not select or filter native-all, expose
a public hosted-bundle alias, add stubs, or broaden core-C.

The profile contract is fail-closed: derive requested `rt_*`/`spl_*` names from
the final object closure, require exactly one provider for each, reject every
pairwise defined-symbol intersection and constructor/destructor, and allow a
provider's undefined names only when core-C or system libraries uniquely own
them. Its cache namespace must include the target/backend/options, Stage2/3
compiler hash, sorted entry-source hashes, core/capsule/provider hashes, and the
resolved symbol-to-owner table. The authoritative final 105-name stderr was not
retained in this worktree, so no symbol manifest is inferred from older caches;
one fresh strict Stage4 run in a new bounded verification session must capture
that contract before provider components are accepted. macOS, FreeBSD, and
Windows full-CLI capsule preparation remain fail-closed until their archive
localization/constructor gates are ported.

A disabled native-GNU/Linux component-builder slice now stages three independently
validated archives for timestamp/progress, SQLite, and memtrack ownership. The
timestamp source is physically split from the core-C clock owner; SQLite uses
the canonical two-argument core string ABI; each archive is constrained to one
member, an exact export/undefined-symbol contract, no constructors, pairwise
definition disjointness, and verified libc/SQLite ownership. Source-level
behavior probes cover SQLite strings through core-C and the memtrack lifecycle.
These archives are not selected by any production linker path. The aggregate
requested-owner validator, cache fingerprint, remaining providers (including
CUDA/SMF/GPU), and fresh strict runtime evidence remain open.

Related:

- `doc/08_tracking/bug/native_build_entry_closure_quadratic_hang_2026-07-12.md`
- `doc/08_tracking/bug/cpu_simd_direct_fill_full_bootstrap_stage4_spin_2026-07-08.md`
- TODO 548

## 2026-07-15 UI-access deployment follow-up

A cache-preserving strict bootstrap reached verified pure-Simple Stage 3, then
failed at the full-CLI Stage 4 link. The command used the Stage-2 compiler with
`--entry-closure`, `SIMPLE_NO_STUB_FALLBACK=1`, the exact
`src/app/cli/main.spl` entry, core-C, and the dedicated compiler backfill. It
did not select `native_all` or another Rust-hosted runtime.

- Stage 2 SHA-256: `de30977f2e7284c722b275e7e29401da7c760228b0c46ecfc6be5b2a1e553e13`
- Stage 3 SHA-256: `5ab6582155d53e12e486aee57aae5cc9271757bda5aea963a21cb64b475f667e`
- Pure-Simple `simple-core` archive SHA-256:
  `637f2c2be4a44857f17e1a1464998ac19d9729505da0720ab4535896ac8bd2c2`
- Unique unresolved names from the retained Stage-4 linker log: 207
- Names supplied by the generated pure-Simple archive: 11 (`panic`,
  `rt_array_extend_i64`, `rt_array_first`, `rt_array_sort`, `rt_dir_list`,
  `rt_file_copy`, `rt_file_stat`, `rt_getpid`,
  `rt_is_debug_mode_enabled`, `rt_string_rfind`, and
  `rt_time_now_monotonic_ms`)

The unresolved set groups into 105 GPU/accelerator names, 25 SQLite names, 18
platform-window names, 10 process/thread names, 6 HTTP names, 29 core host
helpers, and 14 other command/runtime hooks. This supersedes the earlier
105-name observation for the current UI/play/T32-expanded full-CLI closure; it
does not invalidate that earlier retained evidence.

The bounded third cycle built the pure-Simple archive successfully but proved
that selecting it alone cannot close this graph. Rust-hosted/native-all
selection, generated stubs, ignored undefined symbols, or import pruning would
respectively violate Rust-as-seed-only, strict no-stub verification, runtime
safety, or advertised CLI compatibility. The next implementation remains the
exact-entry `stage4-cli-hosted` provider composition already specified above,
using capability-owned Simple or C archives with disjoint ownership and a
provider-aware cache fingerprint. No deploy/live PASS is claimed, and
fail-closed release-bundle enforcement was deliberately not landed because it
would remove existing launch links before a valid replacement bundle exists.

## 2026-07-15 bounded strict rerun

One fresh full-bootstrap cycle completed strict pure-Simple Stage 2 and Stage 3
with hashes `0309eadf67a61b80331d20ac4a03d949042c26c3bf6f539db93994a49f4ee908`
and `21058880e0c4d6533b38a8060e56047eedf968e05a3e62bbb5b5d0b8589e37db`.
Stage 4 reached the linker and failed on the already-owned provider closure,
including dynamic-load/font WFFI, sleep/string helpers, platform window
backends, and process-timeout symbols. It did not spin or crash. A subsequent
Stage2/3-only rebuild after the narrow bootstrap admission-contract fix
produced the admitted Stage 3 hash
`1764d74b2ff77f558b07cdf27a041d5e3e96824a7ef4b563151a6c29ba7a6816`.
No full CLI, deployment, native-all selection, stub, or ignored symbol is
claimed; TODO535 remains the provider-composition owner.

## 2026-07-16 aggregate final-request derivation

The shared pure-Simple final-link boundary now derives the exact Stage4
`rt_*`/`spl_*` request set after the generated entry object exists. One
fail-closed `nm -g` scan covers the final Simple objects plus entry shim,
normalizes Mach-O prefixes, subtracts sibling definitions, and returns a sorted
unique closure. The exact Stage4 profile also rejects `libsimple_native_all.a`.
Because LLVM-default and explicit-Cranelift objects share this boundary, the
derivation is backend-neutral. Unique production owner selection, capability
archive wiring, the separate link-profile fingerprint, and fresh strict/native
proof remain open; this change does not infer a manifest from the historical
207-symbol grouped baseline.

## 2026-07-16 pure-Simple unique-owner selection

The shared Stage4 closure module now validates candidate archive symbol scans
without linking them. It rejects empty or mismatched inventories, archives with
no global definitions, repeated definitions within one archive, every
cross-archive definition overlap, and requested symbols without exactly one
owner. Selected archive indexes remain in declared order, duplicate requests
are harmless, and Mach-O runtime prefixes normalize through the same closure
rule. The focused contract includes the current core-C/memtrack overlap as a
rejection case.

Production inventory discovery and archive localization remain open, so the
selector is intentionally not wired to raw compiler/provider archives. HTTP ABI
ownership, the remaining provider families, platform-specific constructor
gates, final link-profile fingerprinting, and strict native proof are still
required before Stage4 composition can be enabled.
