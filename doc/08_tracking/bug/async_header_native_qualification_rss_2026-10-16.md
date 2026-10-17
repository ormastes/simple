# Native async header parser qualification exceeds the 4 GiB diagnostic cap

Date: 2026-10-16. Status: OPEN; native behavioral qualification blocked.

## Reproducer and authority

The native fixture `test/fixtures/compiler/async_header_lexical_native/main.spl`
imports the actual `std.nogc_async_mut.http_server.parser.HttpRequestParser`.
It fails fast with distinct nonzero return codes and emits the exact line
`ASYNC_HEADER_LEXICAL_NATIVE_PASS cases=152` only after 152 real cases pass.
It is independent of the SSpec runner and does not substitute a parser.

Producer: retained pure-Simple A174, SHA-256
`a174b8e70b0a0ea4531db2ac5b8553f216590a7fbad0567cd9e40fd8e4630994`.
MSVC vcvars64 and LLVM 23.1.3 are the same toolchain used by the passing
provisional native hello in this validation session. No Rust seed was used.

Fixture SHA-256:
`eb97d7ab1bfd66f179d3c7619d09726ddf1d5f30dec3d8a363a851bf60f07e8f`.
Repaired parser SHA-256:
`702dc9892dcf0a33f33767a4cd82bf7c0e7a2ed3e19d6300f05e786fcbd7d666`.

From `C:/dev/simple-phase3-old-header-20261016`, the guarded compiler command was:

```text
<A174>/simple.exe native-build --target x86_64-pc-windows-msvc --backend llvm
  --source src/compiler --source src/app --source src/lib --entry-closure
  --threads 1 --cache-dir <storage>/header-native-a174-cycle2/cache/header
  --mode one-binary --entry test/fixtures/compiler/async_header_lexical_native/main.spl
  --runtime-bundle bootstrap-tools --runtime-path <checkout>/src/runtime
  -o <storage>/header-native-a174-cycle3/header-native.exe
```

`<storage>` is `C:/dev/simple-bootstrap-storage/phase3-validation-20261016`.
`SIMPLE_NO_STUB_FALLBACK=1`; process-tree cap 4,194,304 KiB; initial free-memory
gate 6 GiB (4 GiB cap plus 2 GiB reserve); timeout 600 seconds; one thread.
Canonical cold-init calculation returned zero because a regular source
inventory CURRENT publication existed; no publication was forced or replaced.

## Observed final attempt

- HIR completed 21/21 modules; retained cache hits 21, misses zero.
- Guard returned 88, `status=rss-cap-exceeded`.
- Peak RSS 4,195,404 KiB; peak job commit 4,261,560 KiB.
- Guard reported `quiescent=1`, no unexpected session PIDs. Process 16732 and
  owned descendants were absent after termination.
- No executable, runtime output, MIR/object completion or behavior PASS exists.
- Fixture, parser and string-core checksums matched before and after.
- Both frozen final launchers matched their recorded live and terminal SHA-256.
  Their hashes were first captured during execution, not before it.

Final evidence is retained under `<storage>/header-native-a174-cycle3/`:
`compile.log`, `result.txt`, `source-before.sha256`, `source-after-check.txt`,
and `launcher-live-sha256.json`.

Final compile-log SHA-256:
`c8949b164017171c5d5c66a0e907a56908d4c58296e40a998b6de38529c7aeb7`.
The guard records aggregate job/tree peaks; independent parent and worker
peak attribution was not captured. Do not infer either process's peak from
the aggregate or from isolated live RSS observations.

The cap crossing follows the last recorded HIR completion. Its underlying
allocation owner and exact compiler subphase are unproved; this is not a
memory-leak diagnosis or evidence that the lexical repair fails at runtime.

## Attempt accounting and remaining work

Attempt one stopped before compilation on missing inventory admission; it
compiled zero modules. Attempt two reached HIR but its launcher was edited
while active, corrupting subsequent shell reads and overwriting its compile
log. Its recorded shell exit 127 is not a trustworthy compiler result. The
final frozen attempt reused its compatible cache; no object reuse is claimed.
All three attempts are exhausted; no fourth build or baseline build was run.

Keep the lexical repair draft and the original header-validation bug OPEN.
The 152 native cases and eight SSpec scenarios remain unexecuted. Investigate
the actual retained-state/allocation owner before a new scoped qualification
session. Whole tests, core checks, Host authority requirements and bug-DB tool
reconciliation remain pending.

Draft PR 3497 remains unfinished because the resource-aborted compile yielded
no behavioral execution evidence and the mandatory compiler/core/MCP gates
have not passed. No compiler semantic regression is established by this run.
