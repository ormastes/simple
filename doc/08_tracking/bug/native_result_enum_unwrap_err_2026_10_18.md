# Native Result unwrap_err rejects named enum payloads

Status: OPEN. Native workaround mechanism PASS; production-owner probes UNRUN.
Authoritative bug DB reconciliation is pending because no qualified full CLI
or test runner is available. Canonical ID:
`native_result_enum_unwrap_err_2026_10_18`.

## Evidence

Authority source: `4f00255ec1ee6908b81e4db1333d95f1a8d5d7c0`.
Producer: `3c6eafef89dcae8f22db2ff5b4ea831cda494fe19b0dd847f186792f019a2951`.
Raw evidence: `C:/dev/p4i3b/authority-images/logs/provisional-authority.attempt1.stderr.log`.
The authority run reports 232 MIR modules, 223 successes and 9 failures; it
does not identify every failed module. Six distinct emission positions report
`unsupported Result unwrap_err payload type` before the duplicated summary.

`lower_result_unwrap_core` in
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` accepts named
Struct/Class payloads, but has no Enum arm. Its existing runtime payload
extraction returns an i64 carrier suitable for a boxed enum. The 232-source
inventory contains exactly six unwrap_err sites with declared enum errors:

| Owner | Receivers | Declared error |
| --- | --- | --- |
| `compiler.hir.archive.interface_action_archive` | symbols, actions, manifest_result_v1, payloads, result | InterfaceActionArchiveErrorV1 |
| `compiler.driver.cache.cas_batch_transaction` | inherited | CasBatchTransactionErrorV1 |

This source correspondence is a candidate mapping, not observed per-module
MIR failure attribution. `runtime_std_hir_sections_from_module_v1` returns a
text error and is deliberately unchanged. Builtin Result import warnings do
not establish a failure: `lower_named_kind` handles Result before nominal
symbol lookup.

## Prepared workaround and recovery

Six guarded unwrap_err calls become `if val Err(error) = result`, preserving
the original enum value. The install failure still closes the transaction
before returning. Calls are neither removed nor converted to fixed errors.
The generic CAS helper and every success path remain unchanged.

Source workaround candidate commit:
`e9d98a9d4eed1bbb4d2f4fef8effa2122483da1c`; native evidence below uses that
exact head. Landing projection onto
`0a1ca2f6c3f8ec8c0f7fb44fd0be366d343d37ec` preserves its eight code/fixture
blobs, with this report updated and one explicit operator-only registration in
`scripts/check/guard_wiring_optout.txt`. The launcher requires a local pinned
Windows producer/toolchain and a reviewed shared memory budget; it is not a
general CI gate. PR landing is pending; the compiler bug
is not fixed. Intended-code recovery reference:
`99e74521fb6af600bacbf99a82a2380b906be64d` (the six prior expressions).
Background fix owner: compiler MIR Result payload lowering.

Proper fix proposal: accept SymbolKind.Enum in the named-payload branch,
retain the boxed carrier and semantic HirType, and verify both unit and
data-bearing enum payloads plus wrong-variant panic behavior. Do not claim
this source workaround fixes the compiler.

## Bounded probes

Use immutable pure compiler
`C:/dev/simple-bootstrap-storage/scope-producer-3d9d-20261018/windows-async-stdio-PENDING/simple-async-stdio-variant.exe`
with SHA-256 `b441c88d477950d2118edf04ddaae1eefb9b5e91942dc821836d108ba776f1ab`,
`SIMPLE_NO_STUB_FALLBACK=1`, and `SIMPLE_COMPILER_PHASE_PROFILE=1`.
Each fixture owns a separate cache and retained logs; no mutable authority
cache writes or identity-stamp changes are allowed.

Prepared launcher: `scripts/check/check-native-result-enum-error-probes.shs`.
It requires `--run`, the exact 40-character source HEAD, a coordinator-supplied
reservation for all other jobs plus the OS, and a fresh `/c/dev/...` evidence
directory. It checks physical and commit availability against that reservation
plus its enforced 8 GiB job cap, then runs the three fixtures sequentially with
one compiler thread and a 660-second process-tree timeout. Existing output
directories are never overwritten. The source HEAD, compiler hash, entry hashes,
object paths, exit statuses and executable hashes are retained. Actual results
are recorded below; syntax validation alone is not native verification.

1. `test/fixtures/compiler/result_enum_unwrap/baseline.spl`: native baseline
   must reproduce the unsupported enum unwrap_err diagnostic.
2. `pattern_binding.spl` beside it: build, canonical link, and run; require exit 0
   and `result-enum-error-pass`. It checks exact unit/error payload variants,
   retained data value 37, and unaffected success value 41.
3. `generic_error.spl` beside it: separate diagnostic for the real
   `cas_batch_error_v1<T>` shape specialized with record/text/unit success
   types. Require exit 0 and `generic-result-error-pass`, or retain exact
   TypeParam failure ownership. It contains no unwrap_err.
4. Once budgeted, compile the actual archive/CAS owners from baseline and
   patched sources with module-error profiling; distinguish six removed
   unwrap errors from any remaining generic/type failures. Exercise malformed
   archives and transaction-close behavior through the real owner functions.

Prepared separate entries `production_archive.spl` and `production_cas.spl`
import the real public owners and are intentionally excluded from the tiny
three-entry launcher. Archive runtime checks cover the two payload decoder
error paths, a valid symbol/action pair, and the install failure's transaction
close. CAS runtime checks cover actual inheritance error variants and valid
inherited mapping contents; they do not exercise the filesystem-backed seal
propagation call site. Their builds require the real compiler/lib/app source
roots, and must be separately budgeted. Neither has been compiled or run.

The paired tiny fixtures validate only the enum extraction mechanism. They
cannot qualify all six production call sites or actual enum layouts. Production
owner compilation/execution and the next affected authority build remain
required. Likewise, a tiny generic fixture outcome alone cannot attribute the
six authority TypeParam emissions to a particular module or specialization.

## Native evidence, 2026-10-18

The source head above and immutable b441 producer were verified by the launcher.
Evidence root: `C:/dev/p4enum3`; the first two admissions in `p4enum1` and
`p4enum2` failed physical-memory gates before any compiler process started.
The third and final admission used a manually reviewed 49 GiB Phase-3 reserve,
4 GiB OS reserve and unchanged 8 GiB probe cap. Removing the earlier
discretionary 5 GiB margin was recorded as allocation review, not a job release.
No cap was lowered and no completed passing fixture was rerun.

| Fixture | Compile | Objects | Run | Outcome |
| --- | --- | --- | --- | --- |
| baseline | 1 | 0 | UNRUN | Expected unsupported enum unwrap_err; MIR 1 total, 0 success, 1 failed |
| pattern_binding | 0 | 1 | 0 | Exact `result-enum-error-pass`; unit variant, payload 37, success 41 |
| generic_error | 0 | 1 | 0 | Exact `generic-result-error-pass`; record/text/unit specializations |

Both generated objects have the AMD64 COFF machine field `0x8664`. Control:
2217 bytes, SHA-256
`d57b9a46294c3ecd3fda34e643ae6dce206896825aa4f047e7c15b895833a14b`.
Generic: 2482 bytes, SHA-256
`bb80627ec7c276c45765cc0b7713a0323a04a3ca9f09d185194539645395b811`.
Executables match their canonical warm artifact receipts (source_count 1):

- control: `8d9b72681ae3d3fa55fd273fa6a8a21273d865732a3adb8685f335255b33eab9`
- generic: `8e9582b4c104c7d7b2774de3f779e1ed8e70fd0199769f94a470ae21cd25fa8e`

Actual canonical response files retain `/FORCE:MULTIPLE`; this is not a
duplicate-symbol-free link. They contain no `/FORCE:UNRESOLVED` or
ignore-unresolved option. Stub fallback was disabled. Response-file SHA-256:
control `c640b1c0d0648eb504ccc2fd6c57a047cc7b718bb39aacb4bcdddd64a902a67d`;
generic `07ed38ffcc4e08836261bbb04dfa2386bcf00603b318d91b6051153611fb5c9e`.

`guard.env` reports complete, exit 0, root 9884, session 33356, quiescent 1,
helper integrity verified, enforced cap 8388608 KiB and peak 1171468 KiB.
Guard SHA-256:
`99a36782a0c6172df2e983bafc35fc5fbf4fddc77aeb5976280b33875a2c9af1`.
Both root and supervisor processes were absent after completion. The 8 GiB
slot is released. Source syntax, whitespace and env/process owner checks pass;
full compiler/core/test verification remains unavailable. Production-owner
fixtures and the affected authority rebuild remain UNRUN.

The three-cycle-per-bug cap includes failed probes. No fourth whole compiler
bootstrap is authorized by this plan. Full compiler, core checks and full
tests remain blocked until a qualified full CLI exists.

## Separate TypeParam investigation

The same authority log reports six unsubstituted T emissions. There is no
proven owner mapping yet. `cas_batch_error_v1<T>` and codec generic helpers
were specialization candidates, but the isolated CAS-shaped generic probe
passed and does not justify rewriting that helper. Generic functions are explicitly
skipped in MIR while marked templates, and body substitution includes Result
inner types. An unused generic class metadata issue must be reproduced before
changing template handling; Future's Poll<T> field is Named, whose MIR lowering
does not recursively lower its type arguments. No broad generic exclusion or
TypeParam-to-i64 fallback is justified by current evidence.
