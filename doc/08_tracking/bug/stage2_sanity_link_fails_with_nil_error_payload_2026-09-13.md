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
collection. With that cleared (PRs #708 / #712), run 10's Stage 2 smoke build
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

## ROOT CAUSE FOUND, 2026-09-13 (run 11 diagnosis) — and run 10's reading of the evidence was wrong

The run-10 section above concludes "the `[linker-wrapper]` half is EMPTY ... Not one
actual `[linker-wrapper]` line was emitted. The prints PR #702 describes as
'unconditional' did not run." **That is false, and the method that produced it is the
lesson.** The print DID run. It rendered as an EMPTY LINE, so a `grep 'linker-wrapper'`
found nothing and the absence was read as unreachability.

Check it directly on the preserved run-10 log — `grep -n '^$'` on
`stage2-sanity.env.frontend-bootstrap-0.log.hello-world-positional` reports **line 42**,
which sits immediately before line 43, the `error: in-process native-build:` line. An
interpolation that carries a nil collapses in FULL, literal prefix included, which is
exactly what `_collect_failure` (`driver_aot_native_output.spl`) was already written to
defend against. **Rule: never infer "the print did not run" from a tag grep. Grep for the
blank line too.**

### The failing site, named

Reproduced by running the rejected candidate DIRECTLY (no bootstrap lane, ~40 s):

```
SIMPLE_COMPILER_TRACE=1 SDKROOT=... SIMPLE_DARWIN_CLANG=... SIMPLE_DARWIN_LD=... \
SIMPLE_PACKAGE_INDEX_COLD_INIT=1 SIMPLE_LIB=<worktree>/src \
  simple.rejected native-build --backend llvm --runtime-bundle core-c-bootstrap \
  --entry-closure --mode one-binary \
  scripts/check/cert/redeploy_gate/fixtures/hello_world.spl --output <out>
```

Trace tail, verbatim:

```
[LINKER] link_to_native: 34 files, output=...
[LINKER] os=macos
[LINKER] smf_inputs=0
[LINKER] calling link_native_unix...
[LINKER] link_native_unix: os=macos, arch=aarch64
[LINKER] calling find_linker...
[LINKER] find_linker returned, is_err=false
[LINKER] linker_info unwrapped
                                  <-- BLANK: the [linker-wrapper] print, collapsed
[LLVM-LINK] link_to_native returned
error: ... Linking failed: no error payload from link_to_native (rendered nil); ...
```

The window between `linker_info unwrapped` and the return contains exactly one exit:

```
src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl
    val linker_info = linker_result.unwrap()
    val linker_path = linker_info[0]                       # <-- nil here
    val execution_linker_path = darwin_resolve_link_tool(linker_path)   # -> ""
    if execution_linker_path == "":
        return Err(darwin_link_tool_unresolved_error(linker_path))      # nil payload
```

`find_linker()` was declared `-> Result<(text, LinkerType), text>` (`mold.spl`). Its
element 0 is the nil. Elimination is tight: `find_mold_path`, `find_lld_path` and
`find_ld_path` all return **absolute paths that exist** (`which ...` output or a stat'd
bundled path), and `darwin_resolve_link_tool`'s FIRST step is
`if file_exists(command): return command` — no subprocess, no PATH. A well-formed
element could not have reached the unresolved branch. A nil explains the resolution
failure, the blank print, and the nil payload simultaneously; nothing else explains all
three.

### Correction to the sibling record

`native_tuple_return_of_texts_yields_nil_2026-09-13.md` was closed as "probably a
misattribution" on the strength of the same false negative ("run 7's log contains zero
`[linker-wrapper]` lines, so the error builder was never reached"). Run 7 removed the
`darwin_resolve_link_tool_report` tuple — a DIFFERENT tuple, downstream of the nil. The
tuple defect is real; the one that matters is `find_linker`'s.

### Fix

`find_linker()` -> `find_linker_path() -> Result<text, text>`, with
`linker_type_for_path(path)` recovering the kind; `find_requested_linker` likewise
returns `Result<text, text>`. `Result<text,text>` + `is_err`/`unwrap` and a plain
cross-unit `text` return are shapes this same binary's trace proves survive native
codegen; the tuple element did not. `darwin_link_tool_unresolved_error` now prints the
literal line first and each value BARE on its own line, so a future nil localises
instead of erasing the whole diagnostic. Regression spec:
`test/01_unit/compiler/native/linker_resolution_no_tuple_spec.spl`.

## 2026-09-13 — relationship to the receipt-size defect: RELATED FAMILY, NOT PROVEN IDENTICAL

The sibling record
`stage2_sanity_native_capsule_receipt_content_mismatch_2026-09-13.md` now has
the receipt-size defect named at instruction level: `fp.size` on an
optional-bound struct compiles to a load at **byte offset 0** (`ldr x0, [x24]`)
instead of 24, so it returns the struct's `path` text pointer. The resolution
site is name-keyed field lookup in the **Rust seed**
(`src/compiler_rust/compiler/src/hir/lower/expr/access.rs`, fallbacks at
:339/:369/:404/:435), reached only when the receiver's struct type is unknown;
it bites at 834 units and not at 58.

`linker_info[0]` is a **tuple element index**, not a named field, so it does not
travel through that by-name resolution path and the two are **not proven to be
one defect**. What they share is the family — a payload behind a wrapper
(`Optional` / `Result`) read at the wrong offset once the payload's type is lost
— but the tuple case needs its own instruction-level evidence before anyone
merges the two.

Also corrected here, because this record's framing assumed otherwise: **Stage 2
is built by the RUST SEED**, not by a self-hosted Stage 1
(`bootstrap-from-scratch.sh:2732` + `SIMPLE_NATIVE_BUILD_RUST=1` at :2795, which
`src/compiler_rust/driver/src/cli/native_build.rs:583-587` documents as the
switch into the Rust pipeline). Both defects are therefore owned by
`src/compiler_rust`, and PR #717's source-level workaround (dropping the tuple)
is a workaround, not a fix.

A 5-second witness for both (no bootstrap) is recorded in the sibling file; the
key missing knob was `SIMPLE_PACKAGE_INDEX_COLD_INIT=1`.
