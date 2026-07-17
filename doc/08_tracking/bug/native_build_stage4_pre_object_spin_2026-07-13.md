# Native-build Stage 4 dispatch and strict-link blockers

## Status

Dispatch and the quadratic entry-closure scan are fixed; strict Stage-4 link
composition remains blocked. The latest bounded exact-entry run resolved its
source closure without an import or phase diagnostic, then terminated with
SIGBUS before emitting objects. That post-resolution phase boundary is not yet
localized.

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

TODO 562 source invalidation is now fixed conservatively: the object scope
includes a length-delimited fingerprint of every loaded source, so any direct
or transitive source change moves the build to a fresh scope. Source paths
shared by module aliases are uncacheable because the current `BuildCache` key
is path-only. This deliberately trades hit granularity for correctness without
adding a second dependency-snapshot schema. Resolved provider/archive ownership
remains separate and must enter the Stage4 link-profile fingerprint, not the
per-module object key.

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

## 2026-07-16 source-only link-profile fingerprint canonicalization

The pure Stage4 closure contract now has a source-level owner resolution and
cache-input boundary. `stage4_resolve_requested_archive_owners` preserves the
selector's declared archive order while also returning sorted, unique
`symbol=label` rows for requested symbols. The versioned
`stage4_link_profile_fingerprint_input` canonicalizes target, backend, link
options, compiler hash, source hashes, archive hashes, and the resolved
symbol-to-owner rows. Named row groups are sorted and reject empty, malformed,
or duplicate names, so caller iteration order cannot change the canonical
input and no ownership dimension can disappear silently.

This is source-only canonicalization, not production cache correctness.
Production still lacks a complete capability-owned provider archive inventory,
so neither owner resolution nor its fingerprint input is wired into the final
link or cache namespace. Archive discovery/localization, provider completeness,
the actual digest/store boundary, invalidation proof, and strict native evidence
remain open. No manifest is inferred, and raw `native_all`, generated stubs, or
broad core-C are not accepted as substitutes for the missing inventory.

## 2026-07-16 explicit-input archive inventory boundary

The pure Stage4 contract now validates an explicit pair of archive labels and
paths before any filesystem probe or `nm` scan. Empty or mismatched inputs,
duplicate labels, duplicate paths, raw `libsimple_native_all`, and broad
`libsimple_runtime` candidates fail closed. The LLVM adapter preserves the
caller's declared order, requires every named path to exist, and returns only
the corresponding symbol scans. It does not search directories, infer a
provider manifest, or manufacture missing candidates.

The LLVM adapter now supplies hosted path semantics explicitly. On Windows,
all candidate paths—including relative MinGW `.a` paths—normalize separators
and case before duplicate detection; Unix candidates retain case-sensitive
identity. This closes a source-only ambiguity where `build/Provider.a` and
`build/provider.a` could select the same Windows archive twice.

This boundary is intentionally not called from the production
`link_llvm_native` body. The complete capability-owned provider archive set is
still missing, so candidate inventory, unique-owner selection, archive hashing,
link-profile cache keys, and selected archive inputs remain unwired. The
validation boundary alone therefore makes no production-link or cache-
correctness claim and does not permit stubs, `native_all`, or broad core-C as a
fallback.

The strict Stage4 path now fails closed after deriving its final requested
symbols instead of discarding that closure and falling through to the ordinary
runtime-object link. Temporary runtime, entry, and bootstrap-support objects
are cleaned before the error. Production linking remains disabled until the
complete inventory, unique-owner selection, and fingerprint are wired.
The fail-closed diagnostic includes the sorted requested symbol closure so the
next authorized run yields the exact required-symbol contract instead of
discarding it.

The font runtime now defines `STBTT_STATIC` before instantiating the vendored
`stb_truetype` implementation. Its internal `stbtt_*` implementation symbols
therefore stay translation-unit-local while the existing 18 `rt_font_*`
functions remain the public runtime ABI. This removes a future archive-owner
collision prerequisite; it does not yet create or select a font provider
archive. The production inventory update below closes the creation/inventory
half while selection remains fail-closed.

Explicit candidate validation now accepts `.a` and `.lib` archive path forms,
normalizes all hosted-Windows path separators and case, rejects `.dll.a` import
archives, and detects case/separator-equivalent Windows duplicates while
preserving Unix case sensitivity. Canonical Unix and Windows names for the
forbidden broad runtime and `native_all`
aggregates both fail closed before filesystem or symbol scans; later member and
symbol inspection still owns `.lib` static/import semantics. Production hosted
native-all discovery now uses `simple_native_all.lib` on Windows and
`libsimple_native_all.a` elsewhere.

Pure hosted builds now compile a C owner for `spl_dlopen`, `spl_dlsym`, and
`spl_dlclose`. It accepts the tagged one-word text ABI through
`rt_interp_cstr`, uses the native Unix or Windows loader, and is shared by LLVM
and Cranelift. When `native_all` is present the C object is omitted entirely so
the Rust archive remains the sole owner; this avoids archive-member duplicate
definitions. The unused raw-string platform-header helpers are removed. A
dedicated Stage4 provider archive and measured undefined-symbol contract remain
open. The Rust seed's Windows close path now follows the same documented
zero-on-success contract.

The native parity harness now has one strict dual-backend dynamic-loader case.
It constructs library and symbol names at runtime to exercise tagged text,
selects libc/libSystem/Kernel32 for Linux, macOS, FreeBSD, or Windows, and
checks open, lookup, missing-symbol, invalid-handle, and close behavior. The
same case covers default LLVM and explicit Cranelift; execution evidence is
still pending. Native parity builds explicitly unset `SIMPLE_RUNTIME_PATH` so
an ambient seed archive cannot bypass the C owner under test.

Native and shared hosted linkers now share exact-leaf native-all detection and
add transitive libraries only when that archive is present. Linux receives the
default-LLVM C++/unwind/SQLite/compression/terminfo/FFI/XML set; macOS receives
the matching libraries, Homebrew path, and all nine required frameworks;
FreeBSD receives its C++/execinfo/compression/util/rt set; and MinGW/MSVC use
their authoritative Windows library sets. Core-only links receive no helper
arguments. Executable platform proof remains pending.

## 2026-07-16 canonical core-C HTTP ownership

The legacy `runtime.c` definition of `rt_http_get` returned a raw C string even
though canonical Simple callers declare a one-word tuple handle. It is removed.
`runtime_native.c` now solely owns `rt_http_get`, `rt_http_request`, and
`rt_http_download` on the same `int64_t` runtime-handle ABI, with a structured
unavailable tuple on Windows and the existing POSIX transport on
Linux/macOS/FreeBSD. Text-header clients route through the pure-Simple adapter,
the test-daemon health check consumes the typed response facade, seed-library
reload uses the tuple signature, and raw-C-string generator compatibility has a
separate `rt_http_get_cstr` name.

Focused C and static source contracts cover GET status/body/error shape, sole C
ownership, caller declarations, reload compatibility, and generator naming.
Executable compiler/native proof remains pending under the existing bootstrap
restriction; this closes one provider ABI collision but does not enable the
incomplete Stage4 provider profile.

## 2026-07-16 target-explicit dynamic-loader provider policy

The pure-Simple Stage4 closure contract now names the dedicated dynamic-loader
archive for Linux, macOS, FreeBSD, Windows MinGW, and Windows MSVC without
building or selecting it. A target-explicit symbol validator accepts synthetic
ELF, Mach-O, COFF-MSVC, and COFF-MinGW scans only when the archive exposes
exactly `spl_dlopen`, `spl_dlsym`, and `spl_dlclose` and imports exactly
`rt_interp_cstr` plus the hosted loader APIs. It normalizes Mach-O prefixes,
COFF import thunks, MinGW decoration, and ignores COFF `@feat.00` metadata.
The eventual link owner is `libdl` on Linux, libSystem on macOS, libc without
`-ldl` on the current FreeBSD path, and the kernel32 import library on Windows.

This is policy evidence, not archive evidence. Production remains fail-closed:
the compiler does not yet create or select this archive. Compile/archive/scan
proof must establish one-member composition, deterministic bytes, forbidden-
section absence, and the measured symbol contract on each hosted platform
before the provider can enter the inventory. FreeBSD, Windows MSVC, and MinGW
archive executions are therefore still pending, but no current hosted format
remains unscheduled. The remaining providers and production
inventory/hash/cache/linking are also pending.

Hosted Linux+macOS arm64/x64+FreeBSD x86_64+Windows MSVC x64+MinGW x64
compile/archive/scan proof is source-scheduled, with first execution pending.
The checker independently compiles and deterministically archives
`runtime_dynload.c` twice, requires the exact single member, compares archive
hashes and bytes, and sends both measured ELF/Mach-O/COFF-MSVC/COFF-MinGW
archives through the existing pure-Simple forbidden-section and exact-symbol
validators. This source scheduling is not measured FreeBSD, Windows MSVC, or
MinGW archive proof and makes no production inventory/hash/cache/linking claim.

The Stage4 closure now uses one pure-Simple insertion sorter for requested
symbols, archive definitions, owner rows, and fingerprint rows. This replaces
`[text].sort()`, which is a no-op under the deployed seed, so canonical order
no longer depends on scan, dictionary, or caller iteration order.

Stage4 admission is now fail-closed at the shared native-link boundary. Once
`SIMPLE_BOOTSTRAP_STAGE4=1` is present, a missing or noncanonical CLI entry or
entry-closure companion is rejected before runtime or entry objects are
compiled; it can no longer fall through to the ordinary object linker. The
same admission precedes every SimpleOS dispatch and rejects those unsupported
routes instead of bypassing the hosted strict-composition barrier.

The Windows timestamp/progress owner now records a monotonic nanosecond epoch
on both progress init and reset, then returns the nonnegative delta. Previously
it returned absolute process-monotonic seconds, so reset did not reset elapsed
time. The provider's logical Windows dependencies remain
`rt_time_now_unix_micros` and `rt_time_now_nanos`; a dedicated archive policy
still awaits measured COFF helper symbols and is not selected by Stage4.

## 2026-07-17 production font provider inventory

The strict pure-Simple LLVM link path now reuses one deterministic single-object
archive staging helper for the already-compiled dynload and font objects. It
requires exactly one canonical `runtime_font.o`/`.obj` member, rejects forbidden
constructor/destructor sections through the shared inventory, and validates
that the measured archive exposes exactly the 18 `rt_font_*` ABI functions with
no `rt_*`/`spl_*` dependency. The validator handles ELF, Mach-O, COFF-MSVC, and
COFF-MinGW symbol spelling while allowing platform C-library imports. The
runtime now actually defines `STBTT_STATIC`, matching the earlier documented
ownership prerequisite and preventing vendored `stbtt_*` exports.

Both temporary provider archives are deleted before the existing strict
composition error. Bootstrap-support objects are now also deleted on every
earlier strict-provider failure exit instead of leaking on fail-closed errors.
This advances production provider inventory only: unique
owner selection, hashing/cache admission, link ordering, execution proof, and
the remaining provider families are still open.

Timestamp time-of-day extraction now shares one floor-day microsecond
remainder. Negative sub-second values such as `-1` therefore produce
`23:59:59.999999` for the preceding date instead of the inconsistent
`00:00:00.999999`; nonnegative timestamps retain the same result. The shared
pure-Simple time utility and bootstrap SFFI template now use the same floor-day
rule, so interpreter, hosted runtime, and generated bootstrap owners agree.

## 2026-07-17 macOS physical-path closure guard

The cached Apple Silicon Stage 3 rebuild now succeeds with the explicit
bootstrap hosted bundle: 9 modules compiled, 706 cached, zero failures, a
24 MiB executable, and version plus `rt_native_build`, Cranelift, `copy_mem`,
and array-extension symbol sanity checks all pass.

The following exact-entry Stage 4 run was terminated before object emission
after roughly two minutes because source loading repeated identical physical
files under their many module aliases, produced 19,236 trace lines, and reached
about 7 GiB RSS. The wrapper correctly seeded only `src/app/cli/main.spl`; the
remaining growth was inside the transitive closure walk.

`load_sources_impl` now tracks `closure_scanned_paths` separately from module
aliases and scans each physical file's imports once. Aliases remain in
`all_sources` for name resolution, but cannot multiply closure discovery. A
source regression pins the guard. Executable Stage 4 verification remains
pending because the bounded three-cycle bootstrap cap was reached.

The first guard-bearing retry proved that local compiled
`Dict<text, bool>` mutation/lookup is not reliable in this path: 320 unique
paths still emitted 5,014 scan events and RSS reached about 5.2 GiB. The three
closure sets now use explicitly reassigned `[text]` arrays and a scalar equality
helper. This retains bounded semantics without depending on the broken local
dictionary state.

The array-backed Stage 3 then completed with 4 compiled, 711 cached, zero
failures, 24 MiB output, 54.49 seconds wall time, and about 276 MiB maximum RSS.
Its exact-entry Stage 4 reached the source-loading boundary and exited in 8.45
seconds at about 1.26 GiB maximum RSS instead of repeating scans. It now fails
boundedly on unresolved import aliases, terminal member imports, and relative
imports. Those resolver gaps are the next blocker; they are separate from this
closed pre-object spin root cause and must be fixed in a fresh capped session.

## 2026-07-17 resolver continuation

The closure resolver now mirrors the language loader's numbered compiler-layer,
stdlib-family, dotted-package, terminal-symbol, and relative-path contracts.
Explicit imports load their resolved file even when its name or directory is
excluded only from bulk scans (`check.spl` and `hir_lowering/async`), while
test/doc/fixture trees remain excluded. A focused source spec pins the resolver
and explicit-import contracts.

The refreshed Stage 3 completed with 715 compiled, zero failed, a 24 MiB
binary, version sanity PASS, 51.86 seconds wall time, and about 518 MiB maximum
RSS. Three bounded Stage 4 observations then converged source resolution:

1. cycle 1 reduced roughly 80 unresolved imports to nine;
2. after materializing the tracked `src/os` sparse root and replacing stale
   cross-layer relative imports, cycle 2 reduced nine to two;
3. after canonicalizing `pipeline_fn.spl`, cycle 3 emitted no unresolved-import
   or phase-failure diagnostic but terminated with SIGBUS before producing objects or an output
   binary (17.67 seconds, about 1.56 GiB maximum RSS).

The apparent missing `os.*` modules were not a repository defect: the isolated
workspace's sparse profile omitted tracked `src/os`. The remaining blocker is
now the Stage 4 SIGBUS after closure resolution. The three-cycle cap was
reached, so the next continuation must capture phase tracing to locate the
exact phase boundary rather than rerunning the same command blindly.

## Next bounded phase diagnostic

No new logging code is required. Add both existing opt-ins to the reproducer:

```sh
export SIMPLE_COMPILER_PHASE_PROFILE=1
export SIMPLE_COMPILER_TRACE=1
```

The last emitted marker localizes the failure without another broad trace
patch. Check, in order, for `phase1:load_sources:done`,
`phase2:parse:done`, `phase3:hir_typecheck:done`, and
`aot:lower_to_mir:done`. All later AOT steps already have paired start/done
markers, and entry into native linking is marked by `[LLVM-LINK] enter`.
`SIMPLE_INTERP_TRACE` adds source-loading detail but does not enable the phase
profiler; `SIMPLE_BOOTSTRAP_DEBUG` does not replace this canonical driver phase
stream.
