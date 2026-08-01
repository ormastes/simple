# Self-hosted CLI binary segfaults in spl_array_pop during `lex` (and native-build/compile)

**Date:** 2026-07-29
**Severity:** high — blocks the WM gate, smoke matrix, and guard-channel work; the
freshest pure-Simple self-hosted binary is unusable for any subcommand that does
real work
**Status:** MITIGATED (2026-07-29) — `pop`/`push`/`append` added to
`is_bare_builtin_collection_method`; validated byte-identical-archive on an
unaffected fixture (PROVED). Full-CLI tier (b) **not achieved** across five
attempts (monitoring error, a real json-import bug fixed upstream same day
as `ab1ea6fc1a6`, the worker's 7200s timeout, a separate out-of-scope
relative-import gap in non-closure `--source` mode, the same timeout still
insufficient at 3x/21600s — see below for full detail). A sixth attempt used
a fast (~7s), minimal, **executed** narrow entry that reaches the exact
crash line directly (`self.indent_stack.pop()`,
`lexer_struct.spl:1071`) — **decisive negative result, reported honestly**:
both the patched and unpatched seed produce **sha256-identical** executables
and identical exit-0 runtime behavior for this fixture; `pop()` resolves to
`rt_array_pop` in both, byte-for-byte, no theft in either. This corroborates
the earlier tier-c finding that narrow/synthetic closures do not contain
whatever competing symbol the real (large) CLI closure links in — the crash
genuinely requires the full closure to reproduce, so no reproduction attempt
made in this doc (three total) has verified the fix against the real defect.
A seventh attempt deliberately imported real `pop()`-defining competing
types (`Stack`, `Mailbox`) alongside the lexer, single then combined, with
`SIMPLE_DEBUG_ERASED_RECEIVER_BIND=1` — again **zero erased-receiver binds
detected, zero theft, for either candidate alone or combined.** Across all
seven attempts in this doc, `self.indent_stack.pop()` has never once been
observed to bind to anything but `rt_array_pop`. An eighth attempt tested a
second, unrelated candidate mechanism from sibling lanes the same day (the
default-engine LIST MISCOMPILE family — `.push()`-triggered reallocation
leaving a stale backing pointer read by a later call), adapted from "local
across loop iterations" to "struct field across separate method calls" to
match `indent_stack`'s real usage shape, tested at up to 444 pushes across 12
alternating push/pop bursts, with a struct layout mirroring `CoreLexer`'s 15
fields — **also negative, both seeds, byte-identical output, no
corruption.** A ninth attempt then went straight at the actual crashed
artifact with **static disassembly, no build required**: `objdump -d` on
`CoreLexer_dot_scan_token` inside the real crashed binary shows its single
`rt_array_pop` call site loads and calls the **real, correct**
`rt_array_pop` address — **not** a competing symbol — and is
**instruction-for-instruction structurally identical** to the same call site
in a clean, exit-0 narrow-entry binary from retry 6. Frame #2's address from
the original gdb backtrace (`0x3325530`) was also confirmed (via `readelf
-l`) to fall **outside every `LOAD` segment** in the binary, i.e. not a valid
static code address the call could have branched to. **This DISPROVES the
theft/wrong-call-target hypothesis for the actual crashed artifact** (not
merely "unreproduced" — the call site is provably correct) and **favors the
data-corruption family instead: something corrupts the `indent_stack`
receiver's runtime data before this identical, correct call executes.**
**Practical conclusion for deployment: this session's `pop`/`push` allowlist
fix should not be presented as the fix for the `lex` segfault** — it remains
a real, separate, evidence-backed fix for the documented `push` theft victim,
but the original crash needs its own root-cause work, now aimed specifically
at data corruption rather than symbol resolution. See "2026-07-29
follow-up" below for full detail on each attempt and recommended
next steps.
**Component:** `src/compiler/10.frontend/core/lexer_struct.spl` (`CoreLexer.scan_token`),
runtime `rt_array_pop` / `spl_array_pop`,
`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs`
(`is_bare_builtin_collection_method`)

## Symptom

`/home/ormastes/dev/pub/simple_wt_secfix/release/x86_64-unknown-linux-gnu/simple`
(sha256 `04a38e21d6fbd86149d46d3ee2d761349f8ad29b02c5037a8eb589b6a1b9e4e0`, built
2026-07-28 21:37:16 UTC, byte-identical to copies in `simple-redeploy-wt`,
`simple-stage4-wt`, `simple_wt_fable`) is genuinely pure-Simple lineage (0 Rust
`_ZN` symbols, 0 `cargo/registry` strings, 20192 unmangled module-qualified
symbols such as `cli__*`/`backend__*`) but segfaults on every subcommand that
does real work:

- `native-build` (both `--backend cranelift` and `--backend llvm`) on a
  trivial `fn main(): print("hi")` — segfault, exit 139, before any output.
- `compile` — fails with "compile bridge exited early before reporting
  diagnostics".
- `lex <file.spl>` — prints all tokens correctly, THEN segfaults (exit 139)
  right after the last token.
- bare `simple <file.spl>` invocation — returns `missing command` instead of
  running the file, indicating the CLI dispatch table itself differs from a
  normal full build.

## Reproduction (PROVED)

```
BIN=/home/ormastes/dev/pub/simple_wt_secfix/release/x86_64-unknown-linux-gnu/simple
"$BIN" lex some_file.spl > out.txt 2>&1; echo exit=$?
# -> prints correct token list, then: Segmentation fault (core dumped), exit=139
```

## Stack trace (PROVED, via `gdb -batch -ex run -ex bt -ex "bt full" --args`)

```
Program received signal SIGSEGV, Segmentation fault.
0x0000000002af57e9 in spl_array_pop ()
#0  spl_array_pop ()
#1  rt_array_pop ()
#2  0x0000000003325530 in ?? ()      <- no symbol; not inside any mapped code
                                         range per `nm` (highest symbol < this
                                         address) — most likely a stale/garbage
                                         stack slot picked up by gdb's
                                         frame-pointer-less unwinder, not a
                                         real call frame
#3  frontend__core__lexer_struct__CoreLexer_dot_scan_token ()
#4  frontend.core.lexer_struct.core_lexer_next_token ()
#5  io___CliCommands__run_commands__cli_run_lex ()
#6  cli___CliMain__args_and_os_commands__run_lex_command ()
#7  cli___CliMain__main_and_help__main ()
#8  spl_main ()
#9  main ()
```

Registers at fault: `rax=0x3325530`, `rbx=0x3325531` (differ by exactly 1 —
looks like the fault address itself, or something derived from it, ended up in
two registers one bit apart), `rdi=0x33254b1`, `rsi=0x3325531`, `r15=0x3325531`
— all clustered in the same ~0x3325xxx region, consistent with a corrupted or
misinterpreted array/heap pointer being handed to `spl_array_pop` rather than a
valid `Array<i64>` object.

**This is NOT a shutdown/atexit crash.** The fault is mid-command, inside the
`lex` subcommand's own token loop (frame #4/#5/#6 walk straight up through
`cli_run_lex` → CLI `main` → `spl_main` → `main`, no destructor/exit-handler
frames). The "prints everything then crashes" signature is explained by the
call site: `CoreLexer.scan_token()` prints/emits each real token as it scans,
and only calls `self.indent_stack.pop()` (to close out remaining indentation)
on the **final** call, once `self.at_end()` is true
(`src/compiler/10.frontend/core/lexer_struct.spl:1067-1076`, guarded by
`if slen > 1: self.indent_stack.pop()`).

## Source-state check (PROVED — not a stale-snapshot artifact)

```
cd simple_wt_secfix && git status --porcelain      # -> empty, clean
git log --oneline -5
  7d2c7fd1cff 2026-07-28 23:08:42  chore: preserve stale Claude worktree simple_wt_secfix
  36fc2ce69f9 2026-07-28 21:36:19  docs(llm-caret): land agent-teams and embedded-tmux docs plus 2 system specs
  4dc44e1a110 2026-07-28 21:32:07  feat(codegen): default-off diagnostic for receiver-type-blind bare-method binds
  9fa3141e97b 2026-07-28 21:31:15  feat(linker): fabricated-stub ratchet at the Rust emission site
  69b91e581   2026-07-28 21:30:17  fix(web-renderer): make hand-rolled scanners byte-indexed, not character-indexed
```

The binary (finished building 21:37:16) was built from commit `36fc2ce69f9`
(21:36:19, ~1 minute before the build completed — consistent with link+copy
time), which was HEAD at the time. The tree was clean; there is no
uncommitted/mid-edit state to blame. The later `7d2c7fd1cff` (23:08:42) landed
**after** the build and only swept in unrelated `.cargo-target-secfix/**` and
`tauri-shell/**/gradlew.bat` artifacts — it did not touch source and is not
causally related.

`4dc44e1a110` ("default-off diagnostic for receiver-type-blind bare-method
binds", landed 21:32:07, 4 minutes before build completion) was checked and
ruled out: it only adds an opt-in `eprintln!` diagnostic
(`SIMPLE_DEBUG_ERASED_RECEIVER_BIND`) behind an env-var gate in
`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs`, and its own
commit message documents a proof that patched-on/patched-off/control builds
produce byte-identical archives for a fixture — i.e. it is a report-only change
with proven zero behavior impact.

Commit `8d1d0a4476c` (the fix this session was originally verifying) is
confirmed an ancestor of `36fc2ce69f9` (`git merge-base --is-ancestor` exit 0).

## Verdict: (c) — miscompilation, most likely a sibling instance of the already-tracked, open codegen defect

This is not (a) a stale-snapshot artifact (tree was clean, commit identified,
nothing suspicious in the interval) and not (b) a shutdown-path bug (crash is
mid-command, not at exit).

The strongest lead is `doc/08_tracking/bug/codegen_bare_method_receiver_type_blind_candidate_selection_2026-07-28.md`
(OPEN, filed the same day): bare method calls on a receiver whose static type
is erased at the call site get bound to whatever `Type_dot_<method>` symbol
happens to be linked into the entry closure, by name-suffix alone, with no
receiver-type check. That doc explicitly documents `push` (a sibling `Array`
mutator) as a confirmed "THEFT" victim (`RingWindow.push`, found via reloc
census over the `gui_entry_desktop` closure) and states in its own words: "the
set is neither small nor closed... each additional closure keeps adding new
tuples." **`pop` is not yet in that doc's known-victims table.**

I checked `is_bare_builtin_collection_method` in
`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:113-166` —
the allowlist that routes known-hazardous bare method names to safe
tag-dispatching `rt_*` builtins before name-suffix resolution runs. Its exact
member set is: `get`(1), `has`/`contains`/`contains_key`/`has_key`(1),
`remove`(1), `find`(1), `starts_with`/`ends_with`(1), `slice`(1|2|3),
`len`/`length`/`keys`/`values`/`is_empty`(0). **`pop` is absent from this
list.** Separately, `"pop" => "rt_array_pop"` exists in the codegen's
normal/typed builtin-method table (line ~1260) — the path used when the
receiver's type IS known — so a **statically-typed** `Array<i64>.pop()` call
(such as `self.indent_stack.pop()`, a struct field of declared type
`Array<i64>`) should route there directly and correctly, matching what frame
#0/#1 of the backtrace show (`spl_array_pop`/`rt_array_pop` were in fact
reached).

**What I could not fully prove (INFERRED, not verified at the object-code
level for this exact binary):** whether the crash is (i) `spl_array_pop`
correctly invoked but operating on an `indent_stack` array object whose memory
was already corrupted earlier in the same process by an *unrelated* bare-method
mis-bind elsewhere in the linked closure (the open bug's own numbers — 97
erased-receiver binds, 22 distinct method names, in one SimpleOS closure alone
— make this plausible: `push`, `to_i64`, `unwrap` and others are confirmed
thieves in-tree, and `self.indent_stack.push(...)` /
`self.force_indent_bracket_depths.push(...)` are both called earlier in the
same lexer), or (ii) a genuine, independent bug inside `spl_array_pop`'s own
runtime implementation (bounds/length handling) that is unrelated to the
erased-receiver class. I attempted to settle this by rebuilding
`src/app/cli/main.spl` with `SIMPLE_DEBUG_ERASED_RECEIVER_BIND=1` and
`--entry-closure` to get a direct census, but the full CLI closure fails to
parse at discovery time (`src/os/compositor/host_compositor_core.spl:699:50`,
unrelated syntax error, pre-existing in that closure) before it reaches
codegen, so no direct confirmation was obtained in the time available.

## Recommended next step (not applied — validation cost is non-trivial)

Given the sibling defect (`push`) is a confirmed victim of the same class,
the cheapest next diagnostic step is exactly the one the existing bug doc's
"Suggested next steps" already prescribes: extend the
`SIMPLE_DEBUG_ERASED_RECEIVER_BIND` census (already landed, default-off, proven
zero-behavior-impact) to a closure that actually parses cleanly and includes
`src/compiler/10.frontend/core/lexer_struct.spl`, and check whether `pop` shows
up as an erased-receiver bind anywhere in it. If it does, the fix is the same
one-line shape as `8d1d0a4476c`/`bea738bdb0b`: add `pop` (and by extension
`push`, already known-vulnerable) to `is_bare_builtin_collection_method`,
verified with the same byte-identical-archive proof protocol, then a full
bootstrap. That is a real Rust-seed change requiring full-bootstrap validation
before landing — not attempted here per the "fix only if trivially small"
guidance, since validation cost is not trivial even though the code delta
likely is.

## Impact

Blocks: WM gate, smoke matrix, and the three guard-channel checks queued
behind a working pure-Simple binary. **Do not deploy this artifact** (or its
byte-identical copies in `simple-redeploy-wt`, `simple-stage4-wt`,
`simple_wt_fable`) as the production `bin/simple`.

## Related

- `doc/08_tracking/bug/codegen_bare_method_receiver_type_blind_candidate_selection_2026-07-28.md` — the open, broader defect class this is most likely a sibling instance of.
- `8d1d0a4476c` — narrow fix for `starts_with`/`ends_with` (verified present in the currently-deployed Rust seed via `objdump -r` reloc check).
- `4dc44e1a110` — landed the `SIMPLE_DEBUG_ERASED_RECEIVER_BIND` diagnostic; checked and ruled out as the cause of this crash (proven zero-behavior-impact by its own commit).

## 2026-07-29 follow-up: fix implemented, validation tiers reached

Added `("pop", 0)` and `("push" | "append", 1)` to
`is_bare_builtin_collection_method` in
`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs`, following
the exact allowlist shape used for `len`/`is_empty`/etc., with a comment citing
this doc and the sibling `push` THEFT entry from the 2026-07-28 doc. `clear`
was deliberately NOT added: that doc's own census classified `clear` binds as
legitimate erased-field dispatch, not theft. `insert` and `sort` were not
added either — no evidence for either in the 2026-07-28 doc's enumeration, and
the task's own instruction was to add only what the doc's data justifies, not
blanket-add sibling mutator names.

Work done in an isolated worktree (`/home/ormastes/dev/pub/wt_scratch/simple_arraypop_fix`,
detached at the-then origin/main tip), not the shared working copy.

**Tier (a) — byte-identical-archive check on an unaffected fixture: PROVED.**
Same fixture as `4dc44e1a110`'s proof pattern (the `ByteSpan`/`starts_with`
repro from `8d1d0a4476c`'s own verification, unrelated to `pop`/`push`),
built with the OLD (`bin/release/x86_64-unknown-linux-gnu/simple`, currently
deployed) and NEW (patched) seeds via
`native-build --entry-closure --emit-archive --target x86_64-unknown-none --backend cranelift`:
both archives are byte-identical, sha256
`a6994edb73067fdd16041e1e41db89e156f4a84029c9658e3a1a01b9a0aca202`. No
collateral codegen change from this patch on a fixture the patch shouldn't
touch.

**Cargo build: PROVED clean.** `cargo build --release` on the patched tree
finished with the same 16 pre-existing warnings as an unmodified build of the
same commit (`rt_*` "redeclared with a different signature" plus one
`last_value` unused-assignment warning, both in unrelated files) — zero new
warnings, and `rustfmt --check` on the touched file passes with no diff.

**Tier (c) — targeted synthetic repro: ATTEMPTED, DID NOT REPRODUCE (informative negative result).**
Two synthetic fixtures were tried against the OLD (unpatched) seed to try to
reproduce the theft directly, both compiled with
`native-build --entry-closure --backend cranelift --target x86_64-unknown-none`:

1. `src/compiler/10.frontend/core/lexer_struct.spl` alone as entry (the real
   crash-site file). Its 5-module closure does not transitively pull in
   `std.core.list` or any other type exporting a `_dot_pop` symbol, so there
   is no competing candidate to steal the bind — `self.indent_stack.pop()`
   compiled to a clean `rt_array_pop` relocation, no theft observed.
2. A wrapper entry that imports `lexer_struct` AND explicitly calls
   `.pop()` on a `List<i64>` in the same closure (to force `List_dot_pop`
   to be linked, mirroring how the 2026-07-28 doc's fixtures forced
   `common.bytes.span` into the closure for the `starts_with`/`slice`
   repros). This also resolved cleanly to `rt_array_pop` for both the typed
   `List<i64>.pop()` call and the lexer's `self.indent_stack.pop()` — no
   theft observed, because in this fixture `self.indent_stack.pop()`'s
   receiver type is apparently still not erased in the sense the codegen
   name-suffix path requires.

**Conclusion from tier (c): the real erasure condition is narrower than
"a bare `.pop()` call plus a stealable `_dot_pop` symbol somewhere in the same
closure."** The `starts_with`/`slice` victims were erased specifically because
they were called on the *return value of another builtin* (`.lower()`,
`.substring()`) whose result type isn't threaded through this particular
codegen path as concretely `text`. `self.indent_stack.pop()` is a direct
struct-field method call, and my synthetic reproductions of that shape did not
erase. The actual crash site involves `CoreLexer.scan_token()` calling itself
through `scan_token_rescan()` (a trampoline the file's own comments say exists
because "the Rust seed interpreter cannot dispatch a self-recursive `me`
call") — the erasure, if that is indeed the mechanism, is most plausibly tied
to *that* indirection, not to `.pop()` calls in general. **This means the fix
in this doc is evidence-based (matches the confirmed `push` victim in the
2026-07-28 doc) and cheap/safe to land (proved zero collateral impact), but is
NOT confirmed via reproduction of the original miscompile at the object-code
level. Future work on this bug class should validate against the real crash
site (a rebuilt self-hosted CLI binary), not rely on synthetic fixtures alone
— synthetic fixtures can give false negatives for this class.**

**Tier (b) — full self-hosted CLI rebuild + `lex`/`compile`/`native-build` smoke: NOT ACHIEVED. Two distinct real findings below; the first correction supersedes an earlier, WRONG claim in this doc's initial 2026-07-29 push.**

**CORRECTION (same day, later pass): the "hang" reported in the first version
of this section was a measurement error, not a real hang — flagged here by
name so the next agent doesn't repeat it.** `native-build` on a big entry
forks a `native_build_worker.spl` **child** process (visible as
`simple run src/app/cli/native_build_worker.spl ...` under a `timeout`
wrapper) and the **parent** process blocks on it via IPC/pipe, so the parent
legitimately shows ~0% CPU and `futex_wait_queue`/`do_wait` the entire time —
that is normal blocking-on-child behavior, not evidence of a stall. The
original observation only checked the parent's threads (`ps -T -p <parent>`);
checking the worker child (`pgrep -af native_build_worker`, or its
`/proc/<child>/stat` utime across two samples) showed it steadily consuming
99.8-99.9% CPU the entire time. The processes reported as "hung" and killed
after 13-23 minutes were doing real, CPU-bound work, not stuck — killing them
destroyed real progress rather than terminating a dead build. **Measurement
rule for this build tool going forward: always watch the
`native_build_worker` child's CPU/utime, never the top-level `native-build`
process's — the parent's own CPU is not a signal of build health.**

Re-run with correct monitoring (worker child CPU tracked) surfaced the real
outcome: after several more minutes of genuine work, the worker **failed with
a real compile error**, not a hang and not a segfault:

    error: unresolved import 'lib.json.types' (used in src/std/common/json/validation.spl): no source file found ...
    error: unresolved import 'lib.json.object_ops' (used in src/std/common/json/validation.spl): no source file found ...
    error: unresolved import 'lib.json.path_ops' (used in src/lib/common/json/utilities.spl): no source file found ...
    error: unresolved import 'lib.json.validation' (used in src/lib/common/json/utilities.spl): no source file found ...
    error: native-build worker exited with code 1.

Checked directly (PROVED, static read, no build needed):
`src/lib/common/json/validation.spl:9-10` and
`src/lib/common/json/utilities.spl:9-12` both `use lib.json.<name>...`, but
the real files live at `src/lib/common/json/<name>.spl` (i.e. the import
should be `lib.common.json.<name>` or equivalent) — a genuine, pre-existing
broken-import defect in those two files, unrelated to `pop`/`push`/arrays and
unmodified by this session. It blocks any `native-build --entry
src/app/cli/main.spl` closure that transitively reaches these two files,
**regardless of seed** — confirmed present at the same origin/main tip this
session's fix was built from, so it predates this change.

The json import bug was fixed upstream same-day as commit `ab1ea6fc1a6`
(repairs `use lib.json.*` spellings plus defunct `mod json.<name>` lines in
`path_ops`/`array_ops`/`object_ops`/`parser` that imported nothing — all 11
modules in `src/lib/common/json` now compile individually under the seed).

**Retry 3 (fresh worktree at the tip including `ab1ea6fc1a6`, correct
worker-child monitoring throughout): NOT ACHIEVED, third distinct real
blocker found, PROVED via the tool's own diagnostic — a worker timeout
budget, not a hang and not a source bug.**

Re-ran `native-build --entry src/app/cli/main.spl --entry-closure --threads 8`
with the patched seed against a fresh checkout at the tip containing both
fixes. Monitored correctly this time: sampled the `native_build_worker` child
PID's `/proc/<pid>/stat` field 14 (utime) twice, 55s apart, in bounded
polling loops. Utime grew steadily by ~2600-3000 ticks (~26-30 CPU-seconds)
per 55s sample for the entire run — genuine, sustained ~98% single-core work,
not a stall — for **7200 seconds**, at which point the worker was killed by
the tool's own internal timeout and printed:

    [TIMEOUT: Process killed after 7200s]
    error: native-build worker timed out after 7200s before producing a binary.
      The interpreted worker loads the whole compiler + LLVM import graph before any
      codegen; a large --source set (e.g. src/os + src/lib) exceeds the budget. Raise
      --timeout, shrink --source, or use the in-process backend for cross-target builds.

Confirmed (PROVED, `native-build --help`): `--timeout <secs>` exists,
**default 7200** — this run hit exactly that default, not an arbitrary hang.
This is a **real, pre-existing infrastructure limit**: the interpreted
`native_build_worker.spl` path takes longer than 2 CPU-hours just to load the
full compiler+LLVM import graph for the whole CLI entry closure, before any
codegen starts. It is unrelated to the array-pop/push fix (the bottleneck is
described by the tool itself as import-graph loading, not codegen) and
unrelated to the json-import bug (that was already fixed and did not
resurface in this run's log). Per instruction, this is reported precisely and
this pass **stops here** rather than raising `--timeout` and re-running for
potentially several more hours, or silently shrinking `--source` in a way
that could mask the real CLI closure. Reported for whoever picks this up
next: the tool's own suggested remedies are `--timeout <bigger>`, a narrower
`--source`, or the in-process (non-worker-subprocess) backend for
cross-target builds.

**Because of this, the old-seed negative control for the full-CLI rebuild was
not run** — it would deterministically hit the same 7200s wall (the timeout
is a property of closure size versus the interpreted worker's fixed budget,
not of which seed compiles it), so spending another ~2 CPU-hours to
reconfirm that was judged not worth it this pass. This is stated as the
remaining gap rather than silently skipped.

**Retry 4 (explicit ask to raise the budget via the tool's own documented
remedy, `--timeout`): two more attempts, one real NEW finding, one confirms
the timeout wall is not close to 6 hours either.**

Rebased the worktree to the then-current tip (`12788f84d10`, past
`ab1ea6fc1a6`) and re-ran with a 3x budget (`--timeout 21600`, 6 CPU-hours),
worker child correctly monitored throughout via `/proc/<pid>/stat` utime
sampling (PROVED — every sample showed steady ~2800-3000 utime-tick growth
per 55s, i.e. genuine ~98-100% single-core work, no stall at any point in
either sub-attempt):

1. `native-build --source src/compiler --source src/app --source src/lib --entry src/app/cli/main.spl --threads 16 --timeout 21600` (the literal recipe requested, matching the non-entry-closure convention `simple_stage2` was built with) — **FAILED with 51 real, distinct `unresolved import`/`empty or excluded` errors** (PROVED, full list captured) across many files that are NOT reached by `src/app/cli/main.spl`'s actual transitive closure: e.g. `src/compiler/35.semantics/semantics/type_coercion.spl` (`semantics.truthiness`), `src/compiler/70.backend/backend/vhdl/vhdl_sim_runner.spl` (`lib.io.vhdl_ffi`), `src/compiler/70.backend/linker/object_provider_adapter.spl` (resolves to an empty/excluded file), `src/compiler/85.mdsoc/weaving/weaving_result.spl`, `src/compiler/90.tools/fix/rules/impl/lint_public_doc.spl`, `src/compiler/90.tools/header_gen/__init__.spl` (3 errors), `src/compiler/90.tools/verify/checker.spl` and `main.spl`, `src/compiler/99.loader/loader/module_loader.spl` and `smf_cache.spl` (4 errors, all relative imports like `..linker.smf_reader`, `...monomorphize.note_sdn`), `src/app/check_dbs/main.spl` (5 errors). **Root cause (INFERRED, not fixed): this is very likely a systemic gap in how the non-closure `--source` bulk-directory-scan mode resolves relative imports (`..x`, `...x`, `super.super.x`), not 51 independent file-level bugs** — the identical entry point (`src/app/cli/main.spl`) compiled with `--entry-closure` hit ZERO of these errors in every other attempt this pass, meaning none of these 51 files are actually in the CLI's real transitive closure; `--source` mode indiscriminately tries to compile every `.spl` file under the three directories regardless of reachability, including orphaned/dead files with their own pre-existing broken relative imports that nothing currently exercises. Per the "report and stop" pattern, this was not chased further or fixed — it is reported here precisely for whoever owns that mode next.
2. Retried the working recipe instead — `native-build --entry src/app/cli/main.spl --entry-closure --threads 16 --timeout 21600` — ran clean (zero import/parse errors, matching every prior `--entry-closure` attempt) for the **full 21600s (6 CPU-hours)**, utime growing linearly and steadily the entire time with no deceleration near the end (no signal of being "almost done"), then hit the raised timeout and exited with the same diagnostic as the 7200s run, scaled: `[TIMEOUT: Process killed after 21600s]`.

**This means: tier (b) is still NOT ACHIEVED**, and the specific remedy asked
for (3x the timeout) was tried and was insufficient — the interpreted
`native_build_worker`'s import-graph-loading phase for the full CLI closure
does not complete within 6 CPU-hours, with a perfectly linear utime curve
giving no evidence of proximity to completion. **Stopping the timeout-raising
approach here** rather than guessing at a further multiplier with no signal
of how much is actually needed — consistent with the pattern of reporting
precisely and stopping rather than improvising around a real, unresolved
blocker. Four real, precisely-diagnosed blockers were found and reported in
sequence this pass: (1) a monitoring error on my part (corrected same day),
(2) a real pre-existing json-import bug (fixed upstream same day, commit
`ab1ea6fc1a6`), (3) the worker-timeout budget at its 7200s default, (4) the
same timeout budget still insufficient at 3x (21600s), plus a newly-found,
separate, out-of-scope defect in the non-closure `--source` mode's relative
import resolution.

**Recommended path forward for whoever picks up tier (b) next** (not
attempted this pass, each is a real option per the tool's own diagnostic
message): (a) a much larger timeout multiplier (10x+) with no guarantee of
success given the observed linear-with-no-deceleration curve; (b) the
suggested "in-process backend" for cross-target builds instead of the
interpreted-worker-subprocess path, which per the tool's message is built
for exactly this case; (c) add progress instrumentation to
`native_build_worker.spl`'s import-graph-loading phase so a retry has a
completion-percentage signal instead of a blind linear utime curve; (d) a
deliberately narrower entry point that still reaches
`CoreLexer.scan_token`/`self.indent_stack.pop()` without pulling in the
entire CLI's LLVM-linked import graph, trading full end-to-end confidence for
a much faster signal.

**Retry 6 (option (d) above — narrow entry that reaches the real crash site
directly, executed rather than only compiled): tried, DECISIVE NEGATIVE
RESULT, reported honestly per instruction — the narrow closure does not
reproduce the crash on either seed, so it neither proves nor disproves
causation.**

Wrote a minimal, self-contained entry
(`use frontend.core.lexer_struct.{make_core_lexer, core_lexer_next_token}`,
`fn main()`) that drives the lexer directly over an in-memory source string
with two levels of indentation (forcing `self.indent_stack` to `[0, 4, 8]`
mid-file, then a dedent to `[0, 4]` at `print(2)`, then the EOF-time
`self.indent_stack.pop()` at the real crash line —
`src/compiler/10.frontend/core/lexer_struct.spl:1071` — with `slen=2 > 1`,
identical shape to both the original `simple_test.spl` repro and the earlier
tier-c fixtures), looping over `core_lexer_next_token` and printing each
returned kind plus a final count.

First native-build attempt without an explicit `--target`/`--backend` failed
outright (`unresolved import 'frontend.core.lexer_struct'`) regardless of
`--source` flags — PROVED workaround: passing `--target
x86_64-unknown-linux-gnu --backend cranelift` explicitly (instead of relying
on the default) fixed discovery and produced a real, runnable, linked host
executable in **~7 seconds** (6 modules compiled, 0.2-0.3s compile + 6.6-6.9s
link) — confirming the narrow-entry strategy is exactly as fast as hoped,
in sharp contrast to the multi-hour full-CLI closure.

Ran the built executable directly (not just compiled/inspected) with **both**
seeds, same recipe, same cache-dir pattern:

- **Patched seed**: exit 0, no crash. Output includes kind `1456` (=
  `182 << 3`, the DEDENT token, tag-boxed — a separate, already-known,
  unrelated tag-boxing quirk documented in project memory, harmless here)
  followed by many repeats of `1520` (= `190 << 3`, EOF, tag-boxed) because
  my own outer-loop comparison (`if kind == 190`) never matches the
  boxed value and so the loop runs to its `0..40` bound rather than
  breaking early — a bug in **my test driver**, not in the lexer or the fix;
  it does not affect whether the crash site itself was exercised, since the
  EOF-dedent-pop line executes regardless of what my loop does with the
  returned kind afterward.
- **Unpatched (currently-deployed) seed, same recipe**: **exit 0, identical
  output, byte-for-byte** — same 6-module compile, same runtime behavior,
  same printed kind sequence.
- **PROVED at the object-code level (not just behaviorally):** the two
  built executables are **sha256-identical**
  (`d79135977e9499b7a177b2dc76c3633adae610610d28b0ea496f9da4ad6f8dba`, both
  builds). `objdump -r` on each build's cache objects shows the exact same 4
  `rt_array_pop` relocations in the exact same object, byte-identical
  offsets, in both the patched and unpatched build — `self.indent_stack.pop()`
  resolves cleanly to the real builtin in **both** compilers here. No theft,
  no crash, no difference of any kind between old and new seed for this
  fixture.

**This is exactly the "both artifacts behave identically" case flagged as
possible up front, and it is reported honestly rather than reframed as a
pass:** the allowlist fix does not govern this narrow closure's compiled
output at all — `pop()` was never miscompiled here in the first place, in
either seed. This **corroborates, rather than contradicts, the tier (c)
synthetic-repro finding from earlier in this doc**: a closure containing only
the lexer module (plus its handful of direct dependencies) does not contain
whatever competing `_dot_pop`-suffixed symbol the real crash's much larger
CLI closure links in, so the erased-receiver name-suffix collision this fix
targets never triggers here. **The real crash's preconditions appear to
require the actual, large, LLVM/multi-thousand-module CLI closure — no
minimal or narrow reproduction attempted in this doc (three so far: two
tier-c synthetic fixtures, and this executed narrow-entry test) has
reproduced it.** This is a meaningful, generalizable finding for this bug
class: **synthetic and narrow-closure reproductions are structurally
insufficient for verifying fixes to erased-receiver name-collision bugs**,
because the defect's trigger condition is a property of the *whole linked
closure's* symbol set, not of the call site in isolation. Confirming this fix
against the real crash therefore still requires either completing a full CLI
build (blocked, see above) or finding the *specific* competing symbol that
the real CLI closure links in for `.pop` and constructing a closure that
includes exactly that symbol (not attempted this pass — would require
locating it via a working, completed CLI build first, which is the same
blocker).

Net effect: **the original `lex`-segfault repro was not reproduced,
confirmed-fixed, or confirmed-unfixed against a real closure this pass** —
blocked in turn by a monitoring error, a real import bug, a real
worker-timeout budget that held even after a 3x raise, one more real
(separate, out-of-scope) defect found along the way, and finally a decisive
but negative result from the fastest, most targeted reproduction attempt
available. The causal link between "adding `pop`/`push` to the allowlist"
and "the observed `spl_array_pop` segfault disappearing" remains
**INFERRED** (from the tier (a) proof of no collateral damage, the
doc-confirmed `push` victim status, and the code-level absence of
`pop`/`push` from the pre-fix allowlist) but **not PROVED** by any
before/after run attempted this pass, narrow or full. This fix is landed as
a well-evidenced, zero-collateral-risk mitigation consistent with the
established pattern for this bug class, not as a fully closed-loop verified
fix. Whoever next has a completed full-CLI build should re-run the original
`lex` repro against it directly — that remains the cheapest real
confirmation once tier (b)'s infrastructure blockers are cleared.

**Retry 7 (competing-symbol census — deliberately import a real `pop()`-defining
type alongside the lexer, single then combined, to force the theft directly
instead of building the whole CLI): tried, DECISIVE NEGATIVE RESULT again,
reported per instruction 4 ("if no single candidate triggers it, try
two-at-once... report the negative with the bind census — still decisive
data").**

A census of `pop()`-defining structs in owned source (18 files) was narrowed
to candidates plausibly in the real CLI closure by real-usage count (grep for
importers, excluding `src/compiler_rust/lib/std` — seed-stdlib, a different
lane): `tooling.ds_utils.Stack` (0 real importers — dead code, kept anyway as
the requested starting candidate), `nogc_async_mut.actors.actor.Mailbox` (9
importers), `nogc_async_mut.async_host.scheduler.WorkStealingQueue` (62
importers), `common.js.engine.vm.Vm` (37 importers, needs a `Logger` to
construct — not attempted, extra setup cost), `app.interpreter.collections.persistent_vec.PersistentVec`
(12 importers, `fn pop() -> PersistentVec<T>` is a free/functional-style pop
returning a new vec, not `me pop() -> T?` — structurally different call
convention, not attempted), `nogc_async_mut.concurrent` (35 importers, two
`fn pop() -> Any` — same functional-style caveat, not attempted).

1. **Single candidate, `Stack<i64>.pop()` alongside the lexer** (both called
   with a statically-typed, non-erased receiver — `s: Stack<i64>` param,
   `self.indent_stack` a typed struct field), built with the **unpatched**
   seed, `SIMPLE_DEBUG_ERASED_RECEIVER_BIND=1`: **zero
   `[CODEGEN-ERASED-RECEIVER-BIND]` lines** (PROVED — the diagnostic did not
   fire for either call), and `objdump -r` shows `self.indent_stack.pop()`
   still resolves to 4 clean `rt_array_pop` relocations, while
   `touch_stack_pop`'s `s.pop()` correctly resolves to `Stack_dot_pop` — no
   collision, both correct, ran to exit 0.
2. **`WorkStealingQueue` (the highest real-usage candidate, 62 importers)
   pulled in a separate, unrelated, pre-existing compile failure**
   (`mir enum identity: enum construction: missing runtime identity for
   'Poll'`/`'TaskState'`, from its transitive `async_host/future.spl`
   dependency) when compiled in this narrow closure — reported, not chased
   further or fixed (out of scope), and dropped from the fixture.
3. **Two candidates at once, `Stack<i64>` + `Mailbox`, unpatched seed,
   `SIMPLE_DEBUG_ERASED_RECEIVER_BIND=1`:** same result — zero erased-bind
   diagnostics, `self.indent_stack.pop()` still 4 clean `rt_array_pop`
   relocations, `Stack.pop()` → `Stack_dot_pop`, `Mailbox.pop()` →
   `Mailbox_dot_pop`, no cross-contamination, exit 0.

**Across all attempts to reproduce this class of miscompile in this doc
(three tier-c/narrow-entry attempts plus this two-part census — six real
build+run experiments total), none has ever caused
`self.indent_stack.pop()` to bind to anything other than `rt_array_pop`, and
`SIMPLE_DEBUG_ERASED_RECEIVER_BIND` has never once reported an erased-receiver
bind for any `.pop()` call site attempted, single or combined competing
symbols.** This is stronger and more specific than "narrow closures don't
reproduce it" (the earlier framing): it suggests the erasure precondition for
`.pop()` — unlike the *confirmed* `starts_with`/`ends_with`/`slice` victims,
which reliably erase from a `.lower()`/`.upper()`/`.substring()` builtin
result in even a small fixture — may depend on conditions not reproduced by
directly constructing a competing type and calling `.pop()` on it in a small
program. Two honest possibilities, neither settled by this pass: (a) the real
CLI closure has some structural property (huge `use_map`/`import_map`, a
specific resolution-order artifact, or literally thousands of distinct
candidates) that these hand-built fixtures cannot approximate at small scale;
or (b) `self.indent_stack.pop()`'s original segfault is not actually an
instance of the erased-receiver-bind class at all, and this session's fix,
while a real, evidence-backed, zero-collateral-risk hardening of the
allowlist (and directly closes the *documented* `push` theft victim), may not
be the actual fix for the original crash. **This doc does not claim either
possibility as settled — causation remains INFERRED, not PROVED, and is now
explicitly flagged as uncertain at the mechanism level, not just
unconfirmed for lack of a build.** The only way to settle it that has not
been tried is running the original `lex` repro against an actually-completed
full CLI build (still blocked, see tier (b) above) or obtaining a debug build
capable of reporting exactly which symbol `self.indent_stack.pop()` binds to
inside that real closure at the moment of the crash (e.g. via
`SIMPLE_DEBUG_ERASED_RECEIVER_BIND` on a completed, not just attempted, full
build).

**Retry 8 (alternative candidate mechanism from sibling lanes — default-engine
LIST MISCOMPILE family, `reference_native_list_rebind_and_spill_miscompiles`,
`base58_decode_reversed_polarity_rootcause_2026-07-29.md` /
`sha256_bytes_engine_divergence_rootcause_2026-07-29.md`: `.push()`-triggered
reallocation in one call leaving a stale/garbage backing pointer read by a
LATER call, adapted here from "local across loop iterations" to "struct field
across separate method calls"): tried three ways, DECISIVE NEGATIVE RESULT
again, reported per the same "report the negative" instruction.**

`lexer_struct.spl`'s `indent_stack: [i64]` field is born non-empty (`[0]`,
line 172 in `make_core_lexer`, ruling out the sibling bugs' "born `[]` then
rebound" trigger), but is `.push()`-grown across many separate `scan_token`
calls (indent increases, line 1041) and read/popped across many *later*,
separate calls (dedents and the EOF pop at lines 1048-1054 / 1067-1072) —
structurally the right shape for a stale-backing-pointer-after-realloc bug if
one exists at the struct-field level rather than the local-variable level the
sibling lanes found.

Built a `struct Ring` with an `[i64]` field, threaded through separate calls
via the exact copy-and-reassign pattern `core_lexer_next_token` itself uses
(`var next = r; next.method(); return next` / `(next, v)`), with a
push-method and a separate pop-method, driven from `fn main()` with enough
volume and alternation to force multiple reallocations:

1. **Basic**: single struct field (`stack: [i64]`), one push burst of 20,
   then 25 separate pop calls. Patched seed, real linked executable
   (`--target x86_64-unknown-linux-gnu --backend cranelift`, no `--source`
   needed once the target was explicit — same workaround as retry 6):
   clean run, exit 0, all values correct (20 down to 1, then `-1` for the
   depleted stack — no corruption).
2. **Aggressive alternation**: 12 bursts of 37 pushes interleaved with 5 pops
   each (444 total pushes, crossing many likely growth-doubling boundaries:
   4/8/16/32/64/128/256/512), then 500 more pops past empty (mirrors
   `scan_token`'s repeated at-EOF pop-until-`len()<=1` pattern exactly).
   Patched seed: clean, exit 0, all 562 output lines correct. **Unpatched
   seed, identical recipe: byte-identical output** (diff empty apart from my
   own appended exit-code label) — no divergence between seeds either.
   `objdump -r` confirmed the fixture's push/pop calls really do route
   through `rt_array_push`/`rt_array_pop` (not inlined/optimized away), so
   this is a faithful exercise of the real runtime path.
3. **Structurally closer to `CoreLexer`**: rebuilt the struct with 11 sibling
   fields in the same relative order as the real struct (two other array
   fields before `indent_stack`, scalar/text fields around it, one more array
   field after — `CoreLexer` has 15 total fields; a single-field struct
   can't expose an offset-computation bug the real struct's layout might),
   with the pop-method also mutating sibling fields on the same call
   (`pending_dedents`, `line`) matching `scan_token`'s real EOF-pop branch
   shape. Same 444-push/alternating-pop drive. **Both seeds again produced
   byte-identical output, exit 0, no corruption.**

**Combined with retry 7's census, this is now ten real build-and-run
reproduction experiments across two structurally distinct candidate root
causes (erased-receiver-bind theft, and struct-field realloc-then-stale-read),
none of which has reproduced the original crash.** Neither mechanism has been
observed to affect `.pop()`/`.push()` on a struct-field array threaded across
separate method calls in the way the real `CoreLexer`/`scan_token` code is
structured, at the scales and shapes tested (up to 444 pushes across 12
alternating bursts, up to 500 trailing pops, 1-12 sibling struct fields, both
seeds). This does not clear either hypothesis for the real, much larger CLI
closure — only for these specific adapted fixtures.

**Per instruction, the crash-mechanism hunt now needs the debug-instrumented
full-closure run — documented here as the only remaining path that hasn't
been tried and that these ten negative experiments have not been able to
substitute for.** Concretely: either (a) get a completed full-CLI build (the
tier (b) infrastructure blockers above must be cleared first) and re-run the
original `lex` repro directly, ideally under `gdb`/`SIMPLE_DEBUG_ERASED_RECEIVER_BIND`
simultaneously to catch whichever mechanism is live at the actual crash
moment, or (b) instrument `rt_array_pop`/`spl_array_pop` themselves (or the
allocator) to log receiver-pointer provenance and reallocation events, then
run that instrumented build specifically against the real closure. Both
require tier (b) to be unblocked first; neither was attempted this pass.

**Retry 9 (static disassembly of the actual crashed artifact — no build
required, settles causation DIRECTION without tier (b)): DECISIVE — theft
disproven, data-corruption family favored.**

Re-verified (PROVED) the original crashed binary is unchanged:
`/home/ormastes/dev/pub/simple_wt_secfix/release/x86_64-unknown-linux-gnu/simple`,
42477824 bytes, mtime 2026-07-28 21:37:16, sha256
`04a38e21d6fbd86149d46d3ee2d761349f8ad29b02c5037a8eb589b6a1b9e4e0` — exact
match to the artifact diagnosed at the start of this doc.

1. **Located and disassembled the crash-path symbol** —
   `nm` found `frontend__core__lexer_struct__CoreLexer_dot_scan_token`
   (0xc8dc57). `objdump -d --disassemble=<symbol>` found **exactly one**
   `rt_array_pop` reference in the whole function (source has two
   `self.indent_stack.pop()` call sites, lines 1037 and 1071 — codegen
   apparently shares/reuses one call site for both, or only one materializes
   a distinct symbol reference; not investigated further). The call site
   (PROVED, at binary offset `c94a70`):
   ```
   c94a60: mov    $0x2b,%esi
   c94a65: lea    ...,%rcx        # 2af2897 <rt_eprintln_str>
   c94a6c: call   *%rcx
   c94a6e: ud2
   c94a70: lea    0x1e5ec13(%rip),%r8   # 2af368a <rt_array_pop>
   c94a77: call   *%r8
   c94a7a: mov    0x9b8(%rsp),%rdi
   c94a82: mov    %rdi,%r8
   c94a85: and    $0xfffffffffffffff8,%r8
   c94a89: test   %r8,%r8
   c94a8c: jne    c94c8d <...+0x7036>
   ```
   The call is an **indirect call through a register** (`call *%r8`), but the
   register is loaded via a **RIP-relative `lea` whose disassembler-resolved
   comment is `<rt_array_pop>`** — i.e. the loaded, called address IS the
   real `rt_array_pop` symbol's address (0x2af368a, matching `nm`'s table
   exactly), **not** any `_dot_pop`-suffixed competing symbol. **No theft is
   visible at this call site, in the actual crashed binary.** The indirect
   dispatch itself (rather than a direct `call rt_array_pop`) is simply this
   codegen's normal calling convention for runtime helpers via `lea`+`call
   *reg` — not evidence of a vtable/function-pointer mechanism gone wrong.
2. **Frame #2's address (`0x3325530` from the original gdb backtrace) is
   OUTSIDE every `LOAD` segment in the ELF** (PROVED via `readelf -l`): the
   binary's `RW`/bss segment spans `VirtAddr 0x2afd468` through
   `0x2afd468 + MemSiz 0x8180a0 = 0x3315508` — `0x3325530` is **~64 KB (0x10028
   bytes) past that upper bound**, and no other `LOAD` segment comes close.
   It is not a valid static code or rodata address in this binary's own
   image. This is consistent with either a legitimately dynamic
   (heap/allocator-managed, mapped at runtime beyond the static image) data
   address being misread by gdb's non-DWARF, frame-pointer-less backtrace
   heuristic as a return address (most likely, given point 1 shows no
   register-indirect call ever targets an unresolved/wrong location), or with
   genuinely corrupted stack content — **either reading favors "frame #2 is
   not a real call frame / not a call-target problem" over "the call went to
   a different symbol via that address."**
3. **Cross-compared against a known-good binary**: same symbol (mangled as
   `compiler__frontend__core__lexer_struct__CoreLexer_dot_scan_token` — this
   build's module-prefix scheme differs cosmetically) in the clean,
   exit-0 `narrow_patched/narrow_repro` artifact from retry 6 shows the
   **structurally identical** instruction sequence at its own single
   `rt_array_pop` call site: `mov $0x2b,%esi` → `lea`+`call *reg` to
   `rt_eprintln_str` → `ud2` → `lea`+`call *reg` to `rt_array_pop` → load
   from `(%rsp)` → `and $0xfffffffffffffff8` → `test`/`jne`. Same immediate
   constants (`0x2b`, `0xfffffffffffffff8`), same instruction shapes, only
   register allocation (`%rcx` vs `%r8`) and the stack-slot offset (`(%rsp)`
   vs `0x9b8(%rsp)`, expected — different closure size means a different
   frame layout) differ. **Binary-level proof: the call site is not a
   call-target problem in either binary — the crashed binary's `scan_token`
   compiles the pop call identically to a binary that runs it successfully.**

**Verdict: theft/mis-linked-call-target is DISPROVEN, not merely
unreproduced, for the actual crashed artifact.** The call site that crashes
is object-code-identical to the call site that works. This settles causation
*direction* without needing tier (b): whatever corrupts the call, it is not a
wrong symbol being called — it must be the **receiver's runtime data**
(the `indent_stack` array's backing pointer/length/capacity, or the stack
memory feeding the call) that differs between the crashing and non-crashing
runs, which **favors the data-corruption family (the sibling lanes'
default-engine LIST MISCOMPILE root causes, or something adjacent to them)
over the erased-receiver-bind theft family this session's fix targets.**

**What this means for the fix and the deployment decision:** the `pop`/`push`
allowlist fix landed this session (`fbb00ce4...`) is real, evidence-backed,
and zero-collateral-risk for the *documented* `push` erased-receiver theft
victim — but this static evidence indicates it is very likely **not** the
fix for the original `lex` segfault. **Recommendation: do not present this
fix as resolving the `spl_array_pop` crash when making the redeploy
decision.** It should be kept (it closes a real, separate, already-documented
defect) but the `lex` crash itself should be tracked as still-open, now
pointed specifically at the data-corruption family. The ten negative
synthetic experiments in retries 7-8 did not reproduce that family's known
triggers either, so the *specific* trigger present in the real, large CLI
closure remains unidentified — the debug-instrumented full-closure run (or
an allocator/`rt_array_pop`-provenance instrumentation pass) is still the
only remaining path to find it, as stated above, but the *kind* of thing it
needs to find has now narrowed from "which symbol got linked" to "what
corrupted this receiver's data before this call."
