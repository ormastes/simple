# Legacy gzip block parser lacks an explicit optional result contract

Status: source repair authored; compilation and runtime regression **NOT_RUN**.
Repair base: `d958cce328bcd61d8b13f1b57a81f90148c3dc85` in
`D:/dev/simple-smux-phase3-suite-20261025`.

## Observed failure and provenance

The separate LLVM Phase3 candidate build in
`D:/dev/simple-devhub-release-20261025` ended at2026-10-25T07:33:32Z with
HIR aggregate failure. Its worker recorded exit1, failed_modules1,
unfinished0, claimed1542 and sealed0. No candidate executable or new-candidate
Hello proof exists. No independently retained outer-process exit receipt was
found; this report does not reinterpret the worker exit as that receipt.

The retained diagnostic says `deflate_block_parse` returns a value but declares
no return type and requests an explicit return type. The failed source was:

`D:/dev/simple-devhub-release-20261025/build/scv/snapshots/scv-revision-v1-c8f9d163b52bf76a2e53f5f6b20a2a9da667a330023c3d7128e639fbbaffe532/src/lib/nogc_sync_mut/compression/gzip/inflate.spl`

Source SHA256: `2573a6e4be64b21d9eae0294905233b8d8d332315dd1ec4008813fad7025f967`.
Terminal ledger:
`D:/tmp/simple-cache/v1/projects/7dcf7beb22f33342151bfd60494ef3d85d51da9a92b6318d2576edd1a65e5941/hir-recovery/queue-49668-0/4484fa32c0a379331604a3bc454d833fb25fa6d5131f850ff38bb8a420c0cb5c.terminal`.
Log: `D:/dev/simple-devhub-release-20261025/build/devhub-system/phase3-rebuild.log`.
Independent observation: `build/review/devhub-llvm-phase3-live-observation.md`
in the repair worktree. These paths retain historical failure evidence;
the source repair does not replace it with a success claim.

Actual producer:
`C:/dev/simple-disk-headroom-warm-bootstrap-storage-20261025/output/stage3/simple.exe`,
SHA256 `13d73267e690b2cdd46438315e2bfe6d4d6c0c37bcfc15591a921fc9728b270b`.
This was the provisional Phase2 producer; the directory name `stage3` is not
Phase3 admission evidence. Actual compiler arguments:

```text
native-build src/app/cli/bootstrap_main.spl --source src/compositions/kernel_llvm_cranelift --source src --backend=llvm -o build/devhub-system/phase3/simple.exe
```

No `--runtime-path` was supplied. The actual linked/runtime-provider identity
for this LLVM launch was not independently established. The launcher was edited
after launch, so its current environment settings cannot prove the launch
environment. Do not borrow runtime pins from the separate Cranelift attempt.

## Cause and bounded owner repair

The legacy helper's contract is optional input bytes and an optional
heterogeneous four-field array: block type `i64`, final flag `bool`, payload
`[u8]`, next byte offset `i64`. An untyped or parameter-only-typed declaration
does not express that return contract to this producer. This is an explicit
legacy inference/admission failure, not evidence that every inferred function
or optional array fails.

The owner now declares `(data: [u8]?, offset: i64) -> [Any]?`, explicitly binds
`Some(bytes)` to a concrete `[u8]` before indexed reads, and returns nil for
absent input. The marker's empty payload is explicitly `[u8]`. Stored-block
decoding, fixed/dynamic markers, flags and offsets retain their legacy shapes.
The result is not narrowed to `[i64]`, and nil-call compatibility is retained.
The normal return-type diagnostic remains enabled; no compiler guard, family
selection, backend, authority receipt or cache identity was weakened.

The obsolete source-string assertion is replaced in
`test/01_unit/lib/nogc_sync_mut/compression/gzip_inflate_negative_offset_guard_spec.spl`
with three real behavioral scenarios: nil/empty/invalid offsets/truncation;
stored final block at nonzero offset with exact zero/high-bit bytes; and full
fixed/dynamic mixed-field markers including true/false flags. No mirrored
manual for that old source-string spec was present. The existing RFC1951/1952
suite remains unchanged and supplies additional nil/stored/fixed coverage.

## Required verification

Authored scenarios3; executed0; observed passed0/failed0; all **NOT_RUN**.
Run the focused behavioral spec and existing gzip RFC suite with the admitted
compiler and its matching provider. Preserve exact producer/runtime/source
hashes, actual case counts, exit statuses and artifacts. Verify all four mixed
fields, byte values and nil behavior; parser acceptance or object count alone
does not establish the result ABI. Native LLVM and Cranelift aggregate parity
remain pending. Any subsequent compiler build must use its normal admission
flow and establish real Hello execution before dependent application tests.
No build, runtime launch, cache modification or retry was made for this repair.


## Upstream typed-result reconciliation - 2026-10-25

Status: **WARN / NOT_RUN**. The text and pins above describe historical source and remain unchanged. Upstream `f3b3d615124128de0535deb1645263380a2796cf` intentionally supersedes the earlier `[Any]?` representation with `DeflateBlockResult?` and updates RFC callers to named fields. Rebased head `a007a05292906ec5ecf07fa912d64c93a26d4a5f`, onto `3fafd89481dc07d1688e16150e0ca60ea0905825`, retains that concrete result and our nullable `[u8]?` input with explicit Some/nil unwrapping.

The four semantic values (integer block type, boolean final flag, byte payload, integer next offset), stored/marker behavior, nil input and malformed-offset/truncation failures remain covered. The focused three-case spec now asserts named fields and includes upstream's extreme-negative-offset control; no mixed-array compatibility API is restored. Current RFC callers and the asynchronous result-type reexport are preserved. Historical claims that the RFC suite was unchanged apply only to the earlier revision.

Current Git blobs: source `fdd8c379633ab723b868f583dce6a93127580402`; focused spec `13af0f7826bb82319c52853be0085ab1e7a12027`. The six-overlap integration evidence is in [the release sync source review](../../09_report/smux_release_sync_source_review_2026_10_25.md). This source reconciliation supplies no runtime validation: all three focused cases and RFC/native integration remain NOT_RUN. No compiler admission, cache policy, or guard was weakened.
