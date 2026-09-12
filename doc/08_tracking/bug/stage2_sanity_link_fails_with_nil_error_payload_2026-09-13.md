# macOS Stage 2 sanity: the hello-world link fails with a `nil` error payload (2026-09-13)

Status: OPEN. This is the CURRENT macOS Stage 2 blocker, and it is a different defect
from the one it replaced.

## Verdict, verbatim (run 7)

```
error: sanity FAIL - frontend smoke exited 1 (bootstrap-mode pass: 0)
bootstrap-sanity-error: version_status=0 version_output=simple-bootstrap 1.0.1-beta.1 unsupported_status=1 frontend_status=1 candidate_unchanged=true
error: in-process native-build: LLVM native linking failed: Linking failed: nil
error: Stage 2 bootstrap compiler sanity failed
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

Rejected Stage 2 candidate (preserved, not deployed):
`.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple.rejected`
sha256 `b10911fc830181d11dfcdd59718d2c5d580b039063e25bac5644743171a28ffb`.

## What this is NOT any more

Runs 5 and earlier failed with `darwin-link-tool-unresolved`. That is fixed (PRs #690,
#694) and the fix is verified NEGATIVELY at the only tier that decides: the run-7
frontend failure log contains **zero** occurrences of `darwin-link-tool` or
`[linker-wrapper]`, and `darwin_link_tool_unresolved_error` unconditionally PRINTS
whenever it is reached. Link-tool resolution therefore succeeds now, through the
pinned `SIMPLE_DARWIN_LD`/`SIMPLE_DARWIN_CLANG` path, and the link proceeds past it.

The PATH hypothesis that motivated that work is separately **disproven**. The sanity
child's env dump (`stage2-sanity.env.env.txt`, added by #690) records:

```
PATH=/opt/homebrew/Cellar/llvm@18/18.1.8/bin:/Users/ormastes/.local/bin:/opt/homebrew/bin:
     /opt/homebrew/sbin:/usr/local/bin:/System/Volumes/Preboot/Cryptexes/App/usr/bin:
     /usr/bin:/bin:/usr/sbin:/sbin:/Library/Apple/usr/bin:/Users/ormastes/.cargo/bin:
     /Users/ormastes/.orbstack/bin
SDKROOT=/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk
SIMPLE_DARWIN_CLANG=/Applications/Xcode.app/.../usr/bin/clang
SIMPLE_DARWIN_LD=/Applications/Xcode.app/.../usr/bin/ld
```

`/usr/bin` is present, so `/usr/bin/which clang` had every opportunity to answer and
did not. Whatever the original cause was, a starved PATH was not it.

## What is left

`link_llvm_native` returns `Err(e)` with `e` nil, which
`llvm_native_link_orchestrator.spl:605` formats as `Linking failed: nil` and
`driver_aot_native_output.spl:843` wraps. The link phase itself reports
`state=running ... succeeded=1` for the object, so the failure is at or after the link
invocation, not in object production.

Two candidate shapes, neither confirmed:
1. a genuine link failure whose error text is being lost on the way out (same family as
   `native_tuple_return_of_texts_yields_nil_2026-09-13.md`, where a `(text, text)`
   return read as nil in the stage-2 native binary);
2. an `Err` constructed from an expression that evaluates to nil on the native path.

The first step is to make the payload non-nil, not to guess the linker flag: every `Err`
on the darwin arm of `link_native` / `link_native_cc` / `link_llvm_native` should be
audited for a payload that can be nil, and the orchestrator should refuse to format a nil
into a message (print the site instead). Only then is the underlying link error visible.

## Reproduction

```
sh scripts/bootstrap/bootstrap-from-scratch.sh --stop-after-stage2 --full-bootstrap \
   --mode=dynload --jobs=half
```
from a worktree with a VIRGIN evidence root (delete `.simple/storage/build/bootstrap`
first; note the tree is written read-only, so `chmod -R u+w` before `rm -rf`). ~18 min
with a warm seed, ~26 min cold. Stage 2 itself builds clean: 871 compiled, 0 failed,
135785 KB, linked `via clang++`, 723 s.

## Related

- `doc/10_metrics/infra/macos_bootstrap_chain_2026-09-12.md` (runs 1-7)
- `doc/08_tracking/bug/native_tuple_return_of_texts_yields_nil_2026-09-13.md`
- PRs #690, #694

## Run 10 (2026-09-13): this site is now REACHED, and it is RED

Runs 8 and 9 could not reach the linker — they failed earlier, in capsule
collection. With that cleared (PRs #708 / #710), run 10's Stage 2 smoke build
reached the link and produced, verbatim:

```
candidate_frontend_smoke: hello-world-positional-build failed (raw rc=1)
error: in-process native-build: LLVM native linking failed: Linking failed: no error payload from link_to_native (rendered nil); see the unconditional [linker-wrapper] prints for the failing site
```

Two halves, opposite verdicts:

1. **The orchestrator's half WORKS.** PR #702's refusal to format a nil into
   `Linking failed: ...` held: the message names the condition ("no error
   payload from link_to_native (rendered nil)") instead of printing a bare nil.
2. **The `[linker-wrapper]` half is EMPTY.** `grep 'linker-wrapper'` over
   `stage2-sanity.env.frontend-failure.log` matches exactly one line — the error
   above, which *references* those prints. Not one actual `[linker-wrapper]`
   line was emitted. The prints PR #702 describes as "unconditional" did not
   run, or did not reach this log.

So the failing link site is still unnamed, and the next step is to find out why
that channel is silent — is the print unreachable on this path, or is its output
going somewhere the sanity harness does not preserve? That is a different
question from the nil payload, and it is now the sole remaining Stage 2 blocker
on macOS.

Chain: `doc/10_metrics/infra/macos_bootstrap_chain_2026-09-12.md` runs 9-10.
