# macOS Stage 2 sanity: the smoke unit fails native-capsule receipt verification (2026-09-13)

Status: OPEN. This is the CURRENT macOS Stage 2 blocker (run 8) and it is a
DIFFERENT defect from the one it replaced. It fires EARLIER than run 7's — in
`native_compile`, before any link — so run 7's `Linking failed: nil` site is no
longer reached.

## Verdict, verbatim (run 8)

```
error: sanity FAIL - frontend smoke exited 1 (bootstrap-mode pass: 0)
bootstrap-sanity-error: version_status=0 version_output=simple-bootstrap 1.0.1-beta.1 unsupported_status=1 frontend_status=1 candidate_unchanged=true
error: native capsule collection failed -- module, tag and detail follow
scripts.check.cert.redeploy_gate.fixtures.hello_world
native-capsule-receipt-invalid
receipt-content-mismatch:expected-bytes=1648:actual-bytes=1648
error: in-process native-build: build failed: 1 failed, 0 unverified, 0 not run, 0 ok of 1 unit(s) — ERROR: scripts.check.cert.redeploy_gate.fixtures.hello_world
error: Stage 2 bootstrap compiler sanity failed
warning: stage2 native-build failed (exit 2); Stage 3/full CLI unavailable
```

Rejected Stage 2 candidate (preserved, not deployed):
`.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple.rejected`

Stage 2 itself built clean again; the failure is entirely in the smoke build the
candidate performs.

## What the numbers say

`driver_native_capsule_result_reason_v1`
(`src/compiler/80.driver/driver_aot_native_output.spl:855-896`) rebuilds the
expected receipt text

```
native-capsule-result-v1\n{capsule_identity}\n{object_path}\n{fp.size}\n{fp.content_hash}\n
```

and compares it byte-for-byte with the receipt the compile step wrote. **Both
sides are 1648 bytes and they differ**, which by that function's own comment
localises the fault to CONTENT, not truncation. The only fields that can differ
at equal length are the fixed-width ones: `fp.size` (unlikely to keep the length)
and `fp.content_hash` (a fixed-width digest — the obvious candidate). That would
mean the object file on disk hashes differently at verification time than when
the receipt was written, or one of the two hash computations is wrong in the
stage-2 NATIVE binary while being right in the interpreter.

## The differing field, measured

The written receipt is on disk; its 4th line — `fp.size` — reads

```
37196932097
```

for an object file that is **632 bytes**. The 5th line, `fp.content_hash`, is
`76e16357e568394bbe191e9c9f3633f4ba8dd5c5bf8b97d725f5474936eb327a`, which is
byte-for-byte what `shasum -a 256` gives for that object. So the hash is right
and **the size is garbage** — a value around 0x8_A8xx_xxxx, the shape of a
pointer or an undecoded box, not a file size. Both sides are 1648 bytes because
both garbage values have the same digit count; they differ because the garbage
is not stable between the write and the verify.

`FileFingerprint.size` is filled by `incremental_file_size` ->
`extern rt_file_size` (`driver_build/incremental.spl:60,639`), and it is read
back through an optional bind:

```
val object_fp = FileFingerprint.from_file(capsule.object_path)
if val fp = object_fp:
    expected = "native-capsule-result-v1\n...\n{fp.size}\n{fp.content_hash}\n"
```

`rt_file_size` itself is NOT the defect: a two-call native probe built by the
seed tier (`extern fn rt_file_size(path: text) -> i64`, printed twice) returns
the true size, twice, on this host. The suspicion is therefore the
**optional-bound scalar FIELD read** (`if val fp = object_fp: ... fp.size`) in
the stage-2 native binary — the same family as the earlier optional-bound scalar
field divergence — with `content_hash`, a `text` field beside it, surviving
intact.

Not yet established, and the next steps:
1. dump both texts (not just the lengths) for this one unit and diff them — the
   differing FIELD is the whole diagnosis and the current message deliberately
   withholds it;
2. if it is `content_hash`, re-hash the object outside the compiler and see which
   of the two sides is wrong;
3. check whether `FileFingerprint.from_file` / the hash helper is another
   native-vs-interpreter divergence, which is the family this lane keeps hitting
   (`stage2_sanity_link_fails_with_nil_error_payload_2026-09-13.md`).

## Relationship to the link-nil blocker

Run 8 carried the link-payload hardening (PR #702: every `"" == ok` status on the
darwin link path is site-named and reported unconditionally, and the orchestrator
refuses to format a nil into `Linking failed: ...`). That hardening is **not
disproven and not proven** by this run: the failure now stops before the linker
is reached, so no `[linker-wrapper]` line and no `Linking failed:` line appears
at all. The link-nil record stays OPEN until a run gets past capsule collection.

## Reproduction

```
sh scripts/bootstrap/bootstrap-from-scratch.sh --stop-after-stage2 --full-bootstrap \
   --mode=dynload --jobs=half
```
from a worktree with a virgin evidence root. ~35 min with a cold Rust seed.

## Related

- `doc/08_tracking/bug/stage2_sanity_link_fails_with_nil_error_payload_2026-09-13.md`
- `doc/10_metrics/infra/macos_bootstrap_chain_2026-09-12.md`
- PR #702
