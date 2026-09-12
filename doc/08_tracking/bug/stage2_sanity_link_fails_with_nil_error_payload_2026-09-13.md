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

## 2026-09-13, run 14 — now the SOLE Stage 2 blocker, and the payload renders as `0`

The sibling receipt-size defect is fixed in the Rust seed
(`stage2_sanity_native_capsule_receipt_content_mismatch_2026-09-13.md`
§ RESOLVED), so run 14's Stage 2 reaches this site with nothing else in the way.
Stage 2 built its 877-unit closure clean and was **not admitted** solely because
of this.

**New, and it narrows the search a lot: `darwin_link_tool_unresolved_error`'s
unconditional print now fires, and the command it names is a bare `0`.** PR
#717's hardening (print the literal line first, each value BARE on its own line)
is what made this legible. Verbatim from
`stage2-sanity.env.frontend-failure.log`:

```
[linker-wrapper] darwin-link-tool-unresolved -- command, trail and PATH follow
0

/opt/homebrew/Cellar/llvm@18/18.1.8/bin:/usr/bin:/Users/ormastes/.local/bin:...
```

The command is `0` and the trail is EMPTY. Not nil, not `""` — the integer zero,
rendered as text. So `find_linker_path()`'s `Result<text, text>` Ok payload is
being read out of the wrong slot and yielding a zero word, exactly as
`FileFingerprint.size` yielded a `path` pointer before its fix. `0` is then
handed to `darwin_resolve_link_tool`, fails `file_exists`, and takes the
unresolved branch whose error payload renders nil.

**This is the same family as the receipt-size defect but NOT the same defect, and
the fix that cleared that one does not clear this one** — run 14 carries the seed
fix and still fails here. The receipt-size chain was a NAME lost at
`static_call_return_type_name` for a `-> T?` static constructor; `find_linker_path`
returns `Result<text, text>` from a free function, so it loses its payload type by
a different route. What the two share is the shape: a payload behind a wrapper,
read at an offset chosen without the receiver.

Next step, and it is now cheap: replay the Stage 2 `native-build` from its own
`stage2-command.transcript` with `SIMPLE_TRACE_FIELD_GET=1` (the bootstrap script
sanitises the stage env, so the trace only survives the direct replay — see the
sibling record) and read the `[PB]` payload-bind lines for `mold.spl` /
`native_linking.spl`. The `[PB] Result.Ok slot0 expected_ty=... field_ty=...`
channel already prints for every Result bind in the closure and is the direct
analogue of the `[FIELD-TRACE]` line that settled the sibling defect in one read.

## ROOT CAUSE, 2026-09-13 — the LLVM backend routes `.unwrap()` to `rt_enum_payload`

Reproduced in a **1-unit, single-file module** with the Rust seed
(`SIMPLE_NATIVE_BUILD_RUST=1 ... native-build --backend llvm --mode one-binary`),
~2 s per iteration. No bootstrap, no transcript replay, no trace flags were
needed; the closure-size dependence that made the sibling receipt-size defect
hard to corner is absent here.

```
fn opt_call() -> text?:
    val p: text? = "/from/call"
    p
fn plain_ok() -> Result<text, text>:
    Ok("/usr/bin/plain")
fn main():
    val a: text? = "/local/lit"
    print "1 flat-optional unwrap: [{a.unwrap()}]"
    print "2 cross-fn optional unwrap: [{opt_call().unwrap()}]"
    print "3 boxed Ok unwrap: [{plain_ok().unwrap()}]"
```

Before (seed at `origin/main` 7dd8b7f509e):

```
1 flat-optional unwrap: []
2 cross-fn optional unwrap: []
3 boxed Ok unwrap: [/usr/bin/plain]
```

Row 3 is the discriminator, and it **exonerates `Result`**. `Ok("...")`
constructs a genuine boxed heap enum and unwraps correctly. What is broken is
`.unwrap()` on an **Optional**, and specifically on the FLAT representation — a
`text?` holding a bare text pointer rather than a boxed `Some`. So the task's
framing (a `Result<T,E>` payload-slot or `case Ok(p)` pattern-binding defect) is
wrong: the real site never pattern-matches, and `Result` is fine.

### The mechanism, named

`src/compiler_rust/compiler/src/codegen/llvm/` mapped `.unwrap()` to
`rt_enum_payload` in four redirect tables and two direct-call sites:

- `emitter.rs:368` (table) and `:601` (direct call)
- `functions.rs:2933` (table)
- `functions/calls.rs:2108`, `:2291` (tables) and `:2408` (direct call)

`rt_enum_payload` (`runtime/src/value/objects.rs:519`) is:

```rust
get_typed_ptr::<RuntimeEnum>(value, HeapObjectType::Enum)
    .map_or(RuntimeValue::NIL, |p| unsafe { (*p).payload })
```

— it returns **NIL for every receiver that is not a boxed heap Enum**. A flat
nullable is not one. `rt_is_some`/`rt_is_none` in the same file already accept
the flat form as present (that is why `if p.?:` took the true branch all along),
so the two halves of the same representation disagreed.

The correct helper already existed and was already documented:
`rt_unwrap_or_trap` (`objects.rs:388`) opens with *"Not a boxed enum —
bare/flat-nullable payload convention: return the raw value unchanged"*, then
traps only on a genuine `None`/`Err`. The Cranelift/JIT backend has routed
`.unwrap()` there since 2026-08-11
(`codegen/instr/closures_structs.rs:2055`, pinned by
`codegen_bare_unwrap_calls_rt_unwrap_or_self_not_rt_enum_payload`), and the
tree-walk interpreter returns the receiver itself for a non-enum
(`interpreter_helpers/method_dispatch.rs:909`). **`native_unwrap_returns_enum_wrapper_instead_of_payload_2026-08-11.md`
fixed ONE backend. LLVM was never brought along, and no LLVM-side assertion
existed to notice.** This is a backend-parity defect, not a lowering or
slot-index defect.

### Why it surfaced exactly here

`src/compiler/70.backend/linker/mold.spl:704` `find_linker_path()`:

```
val mold_path = find_mold_path()        # -> text?   (FLAT)
if mold_path.?:
    return Ok(mold_path.unwrap())       # <-- unwrap yields NIL; Ok(nil) is built
```

`native_linking.spl:294` then unwraps a perfectly good `Ok` enum and gets that
NIL payload back. `darwin_resolve_link_tool(nil)` fails `file_exists`, takes the
unresolved branch, and the link dies as `Linking failed: no error payload`.
Run 14's bare print of the value rendered as `0`, which is consistent with NIL
(the special sentinel `3`) read back through an integer decode (`3 >> 3 == 0`) —
offered as a consistency check, not as independently proven.

This also means PR #717's source-level change (tuple -> `Result<text,text>`) was
never going to help: the nil is produced one line EARLIER, by the inner
`mold_path.unwrap()`, and both spellings carry it equally.

### Fix

Route the LLVM `unwrap` family to the flat-nullable-aware helpers, at all six
sites:

- `unwrap` -> `rt_unwrap_or_trap`
- `unwrap_or` -> `rt_unwrap_or_value` (the previous mapping sent this
  two-argument method to a one-argument helper, silently **dropping the
  default**; same table, same defect class)
- `unwrap_err` -> **keeps** `rt_enum_payload`: no err-trap twin is exported, and
  the Ok-trap helper would abort on the very `Err` receiver `unwrap_err` exists
  to read.

After (same fixture, rebuilt seed):

```
1 flat-optional unwrap: [/local/lit]
2 cross-fn optional unwrap: [/from/call]
3 boxed Ok unwrap: [/usr/bin/plain]
4 Ok(flat.unwrap()) unwrap: [/usr/bin/ld] is_err=false
5 unwrap_or present: [/local/lit]
```

Regression tests, both in `codegen/llvm/emitter.rs`'s test module:
`llvm_unwrap_family_routes_to_the_flat_nullable_aware_helpers` (asserts the
callable table, each live mapping paired with the dead one being absent so
deleting an arm cannot satisfy it) and
`no_llvm_redirect_table_still_sends_unwrap_to_rt_enum_payload` (a source-level
invariant over all three files, because three of the four tables are inline
`match` closures no unit test can call — and a partial fix would leave the live
one broken, which is precisely how this survived; it also asserts a minimum live
mapping count so a rename cannot pass vacuously).

### Semantics change to expect downstream

`rt_enum_payload` on a genuine `None`/`Err` silently returned nil; the new
helpers abort with `called unwrap on None` / `called unwrap on Err`. Any
`.unwrap()` on an actually-absent value that the Stage 2 compiler executes was
previously MASKED and will now crash. Cranelift already had these semantics, so
such a crash is a latent bug surfacing, not a regression introduced here — read
any new verdict carrying those messages in that light.

### Adjacent gaps found and NOT fixed here

- `rt_unwrap_or_value` / `rt_unwrap_or_trap` treat a **flat nil** as a present
  value (not a boxed None), so `val n: text? = nil; n.unwrap_or("/fallback")`
  returns empty rather than the fallback. Pre-existing in the shared helpers and
  identical on the Cranelift path AND the tree-walk interpreter (measured); out
  of scope here. Filed as
  `doc/08_tracking/bug/unwrap_family_treats_flat_nil_as_present_2026-09-13.md`.
- `val a: text? = "..."` then `a.expect("msg")` is refused at the semantic layer
  as ``cannot resolve method call `str.expect`: receiver is a builtin type`` —
  the declared `?` is dropped from the local's type. `.unwrap()` compiles only
  because it has a bare-name redirect (`expect` appears in none of the three
  LLVM redirect tables — verified by grep). Filed as
  `doc/08_tracking/bug/declared_optional_local_loses_question_mark_expect_refused_2026-09-13.md`.

## CORRECTION, run 15 (2026-09-13): the LLVM unwrap fix is REAL but is NOT this blocker

The section immediately above claims the LLVM `.unwrap()` -> `rt_enum_payload`
routing was this blocker's root cause. **That claim is wrong and is retracted
here.** The routing defect is real, verified, and fixed — but run 15 carried the
fix and this site failed **byte-for-byte identically**.

Run 15: `--stop-after-stage2 --full-bootstrap --mode=dynload --jobs=half`,
virgin evidence root `.simple/storage/build/bootstrap-run15`, stock
Homebrew-first PATH (no `/usr/bin` workaround). Stage 1 admitted; Stage 2 built
clean; sanity FAILED. Verdict verbatim:

```
error: sanity FAIL - frontend smoke exited 1 (bootstrap-mode pass: 0)
bootstrap-sanity-error: version_status=0 version_output=simple-bootstrap 1.0.1-beta.1 unsupported_status=1 frontend_status=1 candidate_unchanged=true
candidate_frontend_smoke: hello-world-positional-build failed (raw rc=1)
[linker-wrapper] darwin-link-tool-unresolved -- command, trail and PATH follow
error: in-process native-build: LLVM native linking failed: Linking failed: no error payload from link_to_native (rendered nil); see the unconditional [linker-wrapper] prints for the failing site
error: Stage 2 bootstrap compiler sanity failed
```

Rejected candidate:
`.simple/storage/build/bootstrap-run15/stage2/aarch64-apple-darwin/simple.rejected`
(139326920 bytes). The seed the script itself built was verified to carry the
unwrap fix before the verdict landed, by running the 1-unit repro against
`.../bootstrap-run15/rust-authority-*/target/aarch64-apple-darwin/bootstrap/simple`:
it prints `[/local/lit]`, so this is not a stale-seed or cargo-profile artifact.

### What run 15 actually establishes — and it narrows the search sharply

Direct replay on the rejected candidate (~40 s, no bootstrap lane), trace tail:

```
[LINKER] calling find_linker...
[LINKER] find_linker returned, is_err=false
[LINKER] linker_info unwrapped
0                                   <-- bare print of linker_path
[linker-wrapper] darwin-link-tool-unresolved -- command, trail and PATH follow
0
                                    <-- trail: empty
```

**`0` is the INTEGER ZERO, not a nil.** This is the measurement that overturns
the previous reading. On this same native lane a nil prints as a BLANK LINE
(measured directly: a flat-optional `unwrap` returning nil printed an empty
line, and an interpolation carrying nil collapses entirely). A bare `0` is
therefore a live integer value, not an absent one. The earlier "NIL's sentinel
3 read through an int decode gives `3 >> 3 == 0`" consistency check was an
invention and is withdrawn.

Follow the value back with that:

1. Before the fix, the print came from `rt_enum_payload(linker_result)`. That
   helper returns NIL — a blank line — for any receiver that is not a boxed
   heap Enum. It printed `0`, so `linker_result` **was** a well-formed boxed
   enum whose payload is the integer 0.
2. After the fix, `rt_unwrap_or_trap` takes the `Ok` arm and returns that same
   payload: `0`. Identical output, for the correct reason. The fix changed
   nothing here because there was never anything wrong with the unwrap at this
   site.
3. So `Ok(x)` was CONSTRUCTED with `x = 0` inside `find_linker_path`, i.e. one
   of `find_mold_path` / `find_lld_path` / `find_ld_path` returned integer 0,
   and `Some(0)` / `.?` / `.unwrap()` all carried it faithfully:
   `rt_is_none(0)` is FALSE (integer 0 boxes to bit pattern `0x0`, which is not
   the nil sentinel `3` — see the long comment at `objects.rs:528`), so `p.?`
   took the true branch on a zero.

**`is_err=false` never proved the Result was well formed.** `is_ok`/`is_err`
compile to `rt_enum_check_discriminant`, which answers false for a non-`Err`
receiver of any shape. Three runs read that line as evidence that
`find_linker_path` succeeded; it is not, and future readings of this trace
should not treat it as such.

### Where the next session should look

The defect is in `find_mold_path` / `find_lld_path` / `find_ld_path`
(`src/compiler/70.backend/linker/mold.spl:29,75,87`) returning integer 0 at
877 units. All three have the same shape:

```
val which_result = shell_output("which <tool> 2>/dev/null")
if which_result.len() > 0:
    Some(which_result)
else:
    nil
```

Integer 0 is also a process EXIT STATUS, which makes the leading hypothesis that
`which_result` is bound to the wrong member of whatever `shell_output` produces
once the receiver's type is lost at closure scale — the same **family** as the
receipt-size defect F54 fixed (`static_call_return_type_name` /
`get_field_info(TypeId::ANY, ...)`'s LOCAL-BEST smallest-index scan), reached by
a route that function does not cover, since `shell_output(...)` is a free-function
call and not a `Type.method(...)` static. **Not proven** — it needs the
instruction-level or `[FIELD-TRACE]` evidence that settled the sibling.

Two probes that did NOT settle it, recorded so they are not repeated:
- A 1-unit and a 2-unit (cross-module) reproduction of the exact
  `shell_output` -> `.len()` -> `Some` -> `Ok` -> `unwrap` chain **cannot model
  this**: in a small binary `shell_output` is an UNBACKED extern and returns nil
  (`raw len: -1`), so the chain correctly yields `Err`. The defect needs the
  full closure.
- Re-running the rejected candidate with `SIMPLE_LINKER=/usr/bin/ld` to bypass
  `find_*_path` does not isolate it either: it fails EARLIER, with
  `backend object-path status 1`, i.e. into
  `stage2_sanity_bootstrap1_backend_object_path_status_1_2026-09-13.md`.

Recommended next step, unchanged in kind from the sibling's successful one but
now aimed at a named target: replay `stage2-command.transcript` with
`SIMPLE_TRACE_FIELD_GET=1` and read `[FIELD-TRACE]` for `mold.spl`.

### Caveat on the leading hypothesis above — it does not yet close

The § CORRECTION section offers "`which_result` is bound to a process EXIT
STATUS" as the leading explanation for the integer 0. That hypothesis has an
internal tension which must be resolved before anyone acts on it:

`Some(which_result)` is only reached when `which_result.len() > 0` was **true**.
`rt_len` of a plain integer 0 is not > 0 — measured on this lane, `.len()` of a
nil is `-1`, and an integer receiver is not a length-bearing value either. So a
bare exit status would have taken the `else: nil` branch and produced
`Err("No linker found.")`, which is NOT what the trace shows.

Three shapes survive, and they need different evidence:

1. **Mistyped receiver.** `which_result` is bound to something whose `.len()`
   answers a garbage value > 0 while its integer projection is 0 — the
   `get_field_info(TypeId::ANY, ...)` LOCAL-BEST class F54 fixed for a different
   route. `SIMPLE_TRACE_FIELD_GET=1` on the transcript replay discriminates this
   one, and it is the only one the recommended next step covers.
2. **`Some(x)` payload slot.** The Optional is constructed with the payload read
   from the wrong slot at closure scale, so a correct `which_result` becomes a 0
   inside the box. This is the task's original "payload slot" hypothesis
   reappearing one wrapper further out, and a FIELD-TRACE will NOT show it —
   it needs the instruction-level read.
3. **Tail-position `if/else` value.** The function's result is the value of a
   tail `if/else` expression; the wrong branch value being yielded would produce
   exactly this. Also invisible to FIELD-TRACE.

So: run the FIELD-TRACE replay first because it is cheap and rules out (1), but
do not read a clean FIELD-TRACE as exoneration — (2) and (3) are still live and
need the same instruction-level method that settled the receipt-size defect.

## ROOT CAUSE, 2026-09-13 (runs 16-17) — a WRONG CALLEE, and the 2-unit reproducer that was always available

Not a payload slot, not a pattern binding, not a tail `if/else`, not the `unwrap`
lowering, and not a bad load of any kind. `find_linker_path` calls the wrong
FUNCTION.

Disassembly of the rejected run-15 candidate (sha256 `2be26905a8e3…`), at the
block every `if <opt>.?:` arm of `find_linker_path` branches to:

```
100558408: aa1303e0  mov  x0, x19
10055840c: 9402c01b  bl   0x100608478 <_lib__nogc_async_mut__async__poll__Poll.unwrap>
100558414: aa0003e2  mov  x2, x0          <-- the Ok(...) payload
100558428: 141c241f  b    0x100c614a4 <_rt_enum_new>
```

`mold_path.unwrap()` on a `text?` was bound to `Poll.unwrap`, an unrelated
type's method, which returns 0 for a text receiver. `Ok(0)` is then a genuinely
well-formed boxed enum — which is why `is_err=false` and why the payload printed
as `0` rather than the blank line a nil produces — `darwin_resolve_link_tool(0)`
fails `file_exists`, and the link dies with the nil-payload error.

### The seed defect

`src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs`, inside
`mangle_mir`: two bare `.method` scans (one for `MirInst::Call`, one for
`MethodCallStatic`) take a BARE `unwrap` target and bind it to the first
import-map entry whose key ends in `.unwrap`.

`resolve_call_target` and `resolve_method_call_static` already refuse exactly
this — their guards cite the `FailSafeResult.unwrap` RV64 leak — but **they run
only when the earlier scans left the name unresolved.** Once a scan rebinds,
`known_mangled` holds the new name and the guarded resolver is skipped entirely.
The guard was in the resolvers and not in the scans that run before them.

The Cranelift twin (`codegen/instr/closures_structs.rs`) had the identical
split: its bare `import_map` fallback carried the guard, its two qualified scans
did not.

### The reproducer that was always available — 2 units, 2.6 s

Every earlier reproducer failed to reproduce because it was missing one
ingredient: a COMPETING user method named `unwrap`.

```
rival.spl:  struct Rival<T>: value: T    /  impl Rival<T>: fn unwrap() -> T: self.value
main.spl:   fn find_it() -> text?  ...   /  if p.?: return Ok(p.unwrap())
```

The minimal pair is the entire story — the only difference is whether one user
`unwrap` exists in the closure:

| | LLVM | Cranelift |
|---|---|---|
| without the rival `unwrap` | `[/usr/bin/ld]` | `[/usr/bin/ld]` |
| with it, before the fix | `[<value:0x4>]` | `[<value:0x4>]` |
| with it, after the fix | `[/usr/bin/ld]` | `[/usr/bin/ld]` |
| genuine `rv.unwrap()` after the fix | `[/real/rival]` | — |

**So the closure-size dependence belongs to the REBIND, not the payload.** A
1- or 2-unit binary has no competing `unwrap` to bind to, so the call correctly
stays bare. That is why F55's two probes "could not model this" and why the
877-unit closure was thought to be required.

### Every other suspect was read at instruction level and exonerated

- `find_mold_path` (`0x100557728`): the `for` loop's `file_exists` truthiness
  test and its `Some(candidate)` return are correct; so is the tail
  `shell_output` -> `str_len` -> `Some`/`nil`. **Hypothesis 3 (tail `if/else`)
  is dead.**
- `find_lld_path`, `find_ld_path`: correct; `x2` is the `shell_output` result in
  every `Some` return.
- `shell_output` (`0x10060dd80`): the 3-tuple destructure is correct —
  `rt_tuple_get(0)` is stdout, `rt_tuple_get(2)` -> `rt_value_unbox_int` is the
  code, `cbz` takes the trim path. **The "bound to the process exit status"
  hypothesis is dead**, and with it the `.len() > 0` tension: `.?` and `.len()`
  both ran on the correct text. Only the `unwrap` CALL SITE was wrong.

### Blast radius

**270 call sites across 143 functions** besides `Poll.unwrap` itself called it
in the rejected binary, including
`MirToLlvm.translate_module_with_entry_policy`, `InterpreterBackendImpl.eval_expr`
and the Cranelift adapter. Zero legitimate external `Poll.unwrap` callers exist.
The linker was simply the first one whose wrong value was fatal.

### Method notes, for the next session

1. **The `SIMPLE_TRACE_FIELD_GET=1` transcript replay recommended by run 15 was
   never needed and could not have found this** — a FIELD-TRACE reports loads,
   and no load was wrong. Minutes of `llvm-objdump -d --start-address/--stop-address`
   over the already-named symbols settled it with no execution at all. Reach for
   the disassembler earlier when the suspect functions are named.
2. **Run 16 proves you must check the artifact before spending 30 minutes.** It
   carried a fix aimed at `resolve_method_call_static` and failed byte-for-byte
   identically; disassembling the freshly built Stage 2 candidate showed the
   `bl Poll.unwrap` still there, and instrumenting that function produced ZERO
   hits. Verify the instruction, then start the bootstrap.
3. **When a defect needs "the full closure", ask what the closure CONTAINS that
   a small one does not.** Here it was one competing symbol, and naming it
   turned a 26-minute lane into a 2.6-second loop.
4. The 40 s direct-witness replay on a rejected candidate could not be
   reproduced from a different worktree — it fails earlier at `backend
   object-path status 1` even after matching the sanity PATH, `SIMPLE_LLVM_BIN`
   and a private cache scope. The sanity child's full env is in
   `<evidence-root>/stage3/<triple>/stage2-sanity.env`; diff against it rather
   than guessing knobs.

### Fix

One `is_enum_helper_method` predicate (`unwrap`, `unwrap_or`, `unwrap_err`,
`is_some`, `is_none`, `is_ok`, `is_err`), applied to both LLVM-side bare scans
and all three Cranelift-side lookups. Leaving the name bare routes it through
codegen's `bare_rt_redirect`, the correct lowering for every receiver
representation; a genuine `Rival.unwrap()` on a real receiver still resolves.

Also hardened as a sibling, NOT as the root cause:
`resolve_method_call_static`'s str/text/string single-candidate UFCS arm (added
2026-09-07 for `str.split_whitespace`) would rebind a `text.unwrap` the same way.
Its test is proven discriminating. That arm was not the path this blocker took.

Tests (`mangle.rs` test module):
`text_qualified_enum_helpers_never_rebind_to_a_lone_user_method` and
`bare_enum_helper_scans_are_guarded_in_mangle_mir` (a source-level invariant,
because the scans are inline in a function that takes a whole `MirModule` —
and a source-level invariant is exactly what would have caught the partial fix).

### Status, run 17 (2026-09-13): this record's defect is RESOLVED; Stage 2 is blocked by a NEW one

Run 17 carried the fix. The site is clean at instruction level — the same range
that used to read `bl <Poll.unwrap>` now reads:

```
100558294: 941c2c67  bl  0x100c63430 <_rt_unwrap_or_trap>
```

and the nil-payload error is GONE from the verdict. It is replaced by a real
link error with a real message, which is exactly what "make the payload
non-nil" was supposed to achieve:

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

The link now resolves a tool, runs `cc`, and fails for a stated reason. The
successor blocker is `-lc` on darwin — a Linux-ism: macOS has no `libc` to link,
`libSystem` provides it. It is pushed by **pure-Simple** source
(`src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl:401,432,438,
1151,1193` and `mold.spl:651`), NOT by the Rust seed, so it is a different lane
and a different owner from this record's fix. Filed separately as
`doc/08_tracking/bug/stage2_sanity_darwin_link_passes_lc_2026-09-13.md`.
