# macOS Stage 2 sanity: the darwin link line passes `-lc`, which does not exist on macOS (2026-09-13)

Status: RESOLVED 2026-09-13 (PRs #752 and #753). The darwin link line no longer
passes `-lc`, no longer duplicates `-lSystem`, and now pins the SDK — the sanity
hello world LINKS and BUILDS. Stage 2 is still not admitted, but it now fails at
a LATER, unrelated check; see "Outcome" at the bottom and chain runs 18-19.

It took TWO fixes, because `-lc` was hiding a second defect: ld reports only the
FIRST missing library, so `library 'c' not found` masked the fact that libSystem
was never resolvable on this host either.

1. **PR #752 — target-keyed library/CRT table.** `native_all_support.spl` gains
   `native_link_std_lib_args(os, mode)`, `native_link_uses_crt_objects(os)` and
   `native_link_shared_std_libs(os)`, consumed by the direct-ld path, both
   cc-fallback arms and the shared-library line. Darwin passes no `-lc`/`-lm`/
   `-lpthread`, no crt objects, one `-lSystem` on a direct ld64 line and ZERO on
   the cc line (the clang driver appends its own — ours was the duplicate the
   warning named). The `mode` axis ("ld"/"cc-pre"/"cc-post") exists because the
   GNU cc arm interleaves the support args between two library chunks; Linux and
   FreeBSD lines are byte-identical to before, pinned by the spec's literals.
   Darwin also stops treating a missing CRT set as a strict-link-profile error —
   ld64 takes its entry glue from libSystem, so that is normal there and routes
   to the compiler driver.
2. **PR #753 — `-isysroot`.** With `-lc` gone, run 18 got one library further:
   `ld: library 'System' not found`. That reads like a missing library and is
   really a missing sysroot. `darwin_resolve_link_tool("cc")` resolves through
   `xcrun --find clang`, which prefers the Xcode toolchain; on a host whose
   active developer dir is CommandLineTools that clang's DEFAULT SDK is absent.
   Measured directly on this host:

   ```
   /Applications/Xcode.app/.../usr/bin/clang t.c -lSystem   -> library 'System' not found
   same clang with -isysroot $(xcrun --show-sdk-path)        -> links
   ```

   `native_cc_platform_flags` now adds `-isysroot <sdk>`, from `SDKROOT` when set
   else `xcrun --show-sdk-path`, and adds nothing when no SDK resolves.

Regression spec (9 examples, 0 failures under the Rust seed):
`test/01_unit/compiler/native/link_line_per_target_spec.spl`.

Not fixed here, and filed rather than attempted: a DIRECT ld64 line would need
`-syslibroot`, not `-isysroot`. Darwin never reaches it, because
`native_link_uses_crt_objects("darwin")` is false.

The original report follows unchanged.

---

Original status: OPEN. This is the CURRENT macOS Stage 2 blocker, newly exposed by run 17.

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

## Outcome (runs 18-19, 2026-09-13)

Run 18 (fix 1 only): the `-lc` error is gone; the link advances and fails with
`ld: library 'System' not found`. Stage 2 built its full closure clean
(886 compiled, 0 cached, 0 failed, 568.3s compile + 15.6s link) and the rejected
candidate was preserved at 139327304 bytes. Reproduced in ~40 s with that
candidate (`native-build` on a three-line hello world), which is what made fix 2
findable without a second 25-minute cycle.

Run 19 (both fixes): the link errors are gone entirely — the sanity hello world
compiles and links. Stage 2 is still NOT admitted; the sanity gate now fails at
a later, unrelated check:

```
  Stage 2: proving struct receiver/runtime capability
error: Stage 2 struct receiver/runtime capability failed
    | error: stage2 failed the positional pure-Simple Stage-3 route (status 1)
    | error: in-process native-build: Module surface registry graph promotion failed after phase 2
exit:  3
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

That is a module-surface/registry defect, not a linker one, and is outside this
record's scope. No Stage 2 candidate is preserved on the exit-3 path, so there is
no artifact to hand forward from run 19.
