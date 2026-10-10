# Native bootstrap staging and terminal evidence

Use this guide with [failure collection](bootstrap_failure_collection.md) and
[cache preservation](bootstrap_cache_policy.md). These lessons come from the
2026-10-11 Linux/WSL diagnostic lane. They do not qualify native Windows, macOS,
BSD, a later producer, or an unexecuted test. They change agent workflow, not
compiler defaults.

## Freeze execution policy before starting

For the investigated crash-repair lane, serialize native compiler invocations
through one shared compiler lock and use `--threads=1`. Hold the lock through
linking, child cleanup and final receipt publication. Source analysis and isolated
repairs can proceed in parallel; they must not start competing compiler jobs or
write a live source/cache owner. Single-thread execution is a stability control,
not proof that compiler crashes are fixed. Other lanes retain their separately
reviewed worker policy; do not reinterpret a backend thread budget as permission
for that many frontend processes.

Read the host-local bootstrap configuration and pin its bytes in the admission.
The observed host uses `~/.config/simple/bootstrap-host.json` with
`cuda_enabled: false` and three selected `host_cuda_off_release` overlay files.
Record those overlay hashes and ordered source roots. Do not commit this host's
CUDA preference as a universal language/backend default, silently change it in a
frozen source, or count CUDA as tested. Pin the actual producer, source commit,
runtime objects/archives, entry generator, backend tools and complete argv.

## Choose staging from the actual producer path

Inspect the producer's staging rule before choosing an environment variable.
The preserved bootstrap producer lineage
`4788b2a48e56a7ed2af73c8cb42771c6fa7c2197` uses
`native_object_staging_dir` in
`src/compiler_rust/compiler/src/pipeline/native_project/mod.rs` to create
`native-objects-*` under the lexical cache directory's parent. For that path,
setting `TMPDIR` alone did not move objects off the Windows-mounted volume.
This is scoped bootstrap-source inspection, not permission to substitute the
Rust seed for self-hosted tests or a claim that every producer uses that rule.

A reviewed Linux/WSL workaround supplies a fresh tmpfs parent containing one
`cache` symlink to the original physical cache. The lexical cache parent selects
RAM object staging; cache reads/writes still reach the retained cache. Under the
compiler lock, verify the mount, fresh owned parent, expected link spelling,
resolved target and `samefile` identity. Pin both lexical and physical paths,
keep the alias stable, and recheck it at the required boundaries. Never traverse
or recursively archive/delete the cache through the alias.

Preserve normal source, dependency, layout, compiler, backend, runtime and option
fingerprints. A new producer or source can legitimately miss the cache. Lexical
cache spelling can also affect a command-level warm receipt even where object
keys omit it. Do not restamp manifests, copy PASS records, force reuse, or report
an existing object as newly emitted. This cache alias does not qualify filesystem
source aliases or repair their inventory authority.

## Own descendants before publishing a terminal receipt

Start a finite watchdog after acquiring the lock; lock waiting is not compile
time. A monitoring-only policy observes RSS without inventing a memory-admission
gate. Preserve the configured deadline and measured elapsed time separately.

Protect the interval between creating a process and assigning its ownership.
If launch-time SIGINT/SIGTERM delivery is deferred, publish the owned child first,
then deliver the pending interruption and drain that child's process tree while
still holding the lock. Do not let an exec child inherit a blocked termination
signal mask. Exceptions and interrupts must reach bounded owned-child cleanup;
a direct-child timeout alone can leave linker descendants alive. Never use a
global process-name kill to clean up an owned attempt.

Keep `RUNNING_FINALIZATION` and `RUNNING_FALLBACK_LINK` nonterminal. Archive the
actual retained object paths only after their writers are quiescent; bind path,
size, hash, producer and source, then flush and verify durable copies. Preserve
RAM originals on archival failure. Publish one atomic terminal receipt after
all owned children and archival finish; reject a second terminal publication.
Consumers must also verify the exact service invocation is terminal/quiescent.
An old receipt, a collected unit without bound terminal observation, or a live
unit with an apparently final file is insufficient.

A narrow fallback for the sole `rt_file_mode` link failure needs its own reviewed
contract: normal primary exit, exactly the expected diagnostic, no other failed
stages, complete owned link inputs and pinned runtime archives. Run a fresh
natural link under an owned finite watchdog and retain both outcomes. Crashes,
timeouts, missing entry objects or unrelated errors do not satisfy the fallback.
Never fill missing objects with stubs or anonymous objects from another build.

## Report progress and qualification separately

For successful compile observation, report the last log line, actual exit code
and required object byte size; keep full logs on disk. Inspect bounded additional
diagnostics for failures. This concise observation rule does not replace SSpec
summary parsing: test admission still needs actual executed/passed counts and
unexpected-skip checks. `compile functions done failed=0` is a per-module marker
before later initializer/object work, not an aggregate build or link verdict.

A linked bootstrap compiler is `BUILT_NOT_ADMITTED` until its own Hello compile,
object, natural link and execution have passed. A nearby producer's Hello does
not transfer. Retained runtime object hashes/source equality also do not erase
missing historical header/toolchain qualification.

Keep the finite campaign's dependency order explicit. Where the coordinator has
reserved Phase 3 priority, full CLI starts only after the exact new producer's
required core cases and the recorded Phase 3 release, not merely a source review.
A bootstrap entrypoint does not own `test`/`check` just because it compiles Hello.
Build and qualify the full CLI, then prove its real test/check dispatch and
nonvacuous results; build a separate test runner only when that owner is required.
Missing capability remains BLOCKED. Do not borrow a bootstrap positional-object
source proof for a different full-CLI dispatch path.

For each workaround, use the [bug-linked tag contract](bug_linked_workarounds.md),
retain its canonical bug DB record and original failure, and name the exact
reproducer plus similar prevention tests. Distinguish authored/source-reviewed
fixtures from executed tests. Keep bounded repair counts and stopped findings;
new sessions or process restarts do not reset the same feature's budget.

## Evidence boundaries from the investigated lane

The durable investigation records live under the campaign artifact root
`simple-phase2-cuda-owner-20261011`; names below identify historical receipts,
not commands to rerun or release admission.

| Evidence | Established observation | Remaining boundary |
|---|---|---|
| `bootstrap-native-staging-lessons.md`, `cbef-shm-post-function-stage-diagnosis.json` | TMPDIR-only staging assumption failed on the inspected producer path | Other producer/platform staging is unverified |
| `cbef-attempt2-terminal-object-manifest.json` | 554 retained objects, 64,107,472 bytes; required entry/support objects absent | Partial inventory cannot qualify a compiler link |
| `build-phase4-provider-empty-ram-cache-alias-candidate/build-evidence.json` | cbef producer linked through the separately recorded fallback | Its later original Op case crashed; link success did not qualify that path |
| `method-receiver-controller-helper-regression-v1.json` | Extracted Python helpers passed launch-interrupt ownership, child SIGTERM, cleanup and atomic terminal checks | No compiler/controller main ran in this helper test |
| `method-receiver-next-source-plan.json` | b58 source materialized with exact author blobs and overlays | Source review/materialization does not assert b58 build, Hello, Op, Phase 3 or full-CLI PASS |

The controller-helper receipt SHA-256 is
`24a6008c8c9463f416a3c190c3e2ff02bca7ae3b7da9afb2e61caaa62df29edb`.
The b58 source is `b58baa89e4d65a40768fceaf8221fdbdbe58da24`;
its materialization receipt SHA-256 is
`46ff60a06bd24c460497a318c6cd2cd0bfccb84dd0ade19cbf1b9ef26a7e4340`.
These pins preserve the scope of the observations, not an executable promotion.
