# macOS Stage 2 sanity: the darwin link line passes `-lc`, which does not exist on macOS (2026-09-13)

Status: OPEN. This is the CURRENT macOS Stage 2 blocker, newly exposed by run 17.

## Provenance — this is a successor, not a regression

It was uncovered by fixing
`stage2_sanity_link_fails_with_nil_error_payload_2026-09-13.md` (a seed
name-resolution defect that bound `mold_path.unwrap()` to `Poll.unwrap`, so
`find_linker_path()` returned `Ok(0)` and the link died before ever invoking a
tool). With that cleared, the link resolves a tool, runs `cc`, and fails for a
stated reason — which is the first time this site has produced a real message.

## Verdict, verbatim (run 17)

```
error: sanity FAIL - frontend smoke exited 1 (bootstrap-mode pass: 0)
bootstrap-sanity-error: version_status=0 version_output=simple-bootstrap 1.0.1-beta.1 unsupported_status=1 frontend_status=1 candidate_unchanged=true
candidate_frontend_smoke: hello-world-positional-build failed (raw rc=1)
[DEBUG] CRT files not found, falling back to cc
error: in-process native-build: LLVM native linking failed: Linking failed: cc linking failed: ld: warning: ignoring duplicate libraries: '-lSystem'
ld: library 'c' not found
clang: error: linker command failed with exit code 1 (use -v to see invocation)
error: Stage 2 bootstrap compiler sanity failed
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

Rejected Stage 2 candidate (preserved, not deployed):
`.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple.rejected`,
139326760 bytes, sha256 `1a653582fc2c01d1203f…`.

Stage 1 admitted; Stage 2 built its full closure clean and was rejected solely
by this.

## The defect

`-lc` is a Linux-ism. macOS ships no `libc` to link against — `libSystem`
provides the C library, and the same link line already passes `-lSystem`
(twice, hence the duplicate-libraries warning immediately above the error).

Unlike the record it succeeds, this is pushed by **pure-Simple** source, not by
the Rust seed:

- `src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl:401, 432,
  438, 1151, 1193`
- `src/compiler/70.backend/linker/mold.spl:651`
- `native_linking.spl:1114` also lists `-lc` in a flag set alongside
  `-lpthread`, `-lm`, `-lSystem`, `-lSDL2`

Each site needs checking against the target OS; the `[DEBUG] CRT files not
found, falling back to cc` line immediately preceding the failure names the
branch actually taken on this host, so start there rather than changing all six
blindly.

## Why this is a different lane

The predecessor was fixed in `src/compiler_rust/**` (the seed builds Stage 2).
This one lives in the compiler's own Simple source, so verifying a fix requires
rebuilding Stage 2 through the bootstrap (~25 min), not a 2.6 s seed
reproducer. Do not conflate the two.

## Reproduction

```
sh scripts/bootstrap/bootstrap-from-scratch.sh --stop-after-stage2 \
   --full-bootstrap --mode=dynload --jobs=half
```

from a worktree with a VIRGIN evidence root (the tree is written read-only —
`chmod -R u+w` before `rm -rf`). Faster inner loop: reproduce the link line
alone by building the same hello-world fixture with the rejected candidate,
using the sanity child's env from
`<evidence-root>/stage3/<triple>/stage2-sanity.env`.

## Related

- `doc/08_tracking/bug/stage2_sanity_link_fails_with_nil_error_payload_2026-09-13.md`
  (predecessor, RESOLVED)
- `doc/10_metrics/infra/macos_bootstrap_chain_2026-09-12.md` (runs 1-17)
