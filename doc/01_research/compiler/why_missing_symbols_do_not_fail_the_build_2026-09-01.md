# Why missing symbols do not fail the build — mechanism, Linux asymmetry, and prevention (2026-09-01)

**Scope.** Across the 2026-08-31/09-01 Windows bootstrap work, a series of defects
shared one shape: a definition or a lowering was missing, and no build error said
so until a Windows link — or nothing said so at all on Linux. This document answers
three questions with file/line evidence: (Q1) why the missing thing produced no
build error, (Q2) why the Linux build cannot find it, (Q3) what prevents the class.

Analysis checkout: `C:\Users\ormas\dev\simple` (Windows working tree). All paths
relative to repo root; all cited code verified in this tree on 2026-09-01.

---

## 0. Instance status first (so this document does not go stale on arrival)

| Instance | Class | Status in this tree |
|---|---|---|
| `mem_snapshot_record_promotion` undefined | A | **FIXED** by `d122c1a4b78` — now defined at `src/compiler/80.driver/driver_mem_snapshot.spl:107`, exported `:133` |
| `rt_set_args` weak, never resolves on PE/COFF | A | **FIXED** by `1d05b6695ab`, scoped Windows-only by `c4074eb8dcf`; still `__attribute__((weak))` on Unix (`src/runtime/runtime_native.c:5511`) by design |
| `read_file` → `fmt_read_file` stale importers | A | **FIXED** in the `d550b0c10d4` PR ("resolve stale read_file import") |
| `rt_print` codegen-only registration | A | **FIXED** by `8426e39b3eb` / `d550b0c10d4`; adjacent gaps (`rt_println`, `rt_stdout_write`, …) recorded as still open in that commit message |
| `runtime_core_host_services.c` dropped from `tools.rs` list | B | **FIXED** by `d122c1a4b78` (18 symbols restored) |
| `runtime_terminal.c` absent from pure-Simple list | B | **FIXED** — now in both lists: `tools.rs:396` and `src/compiler/70.backend/backend/runtime_compiler.spl:400` |
| `rt_unwrap_or_trap` NULL GOT slot | C | fixed 2026-08 per its bug record; the **mechanism** (tolerant link) is still live |
| MCP 120 MIR lowering errors | D | open; cascade root documented in-code at `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:3388-3392` (note: `50.mir`, not `60.mir` as sometimes cited) |

The instances are mostly fixed. The **class** is not — every mechanism below is
still in the tree.

---

## Q1 — Why did the missing thing not cause a build error?

### 1.1 The link is configured to tolerate undefined symbols — on every non-MSVC lane

Per-platform final-link flags, `src/compiler_rust/common/src/platform/link_config.rs`:

- **Linux** (`:83`) and **FreeBSD** (`:146`):
  `unresolved_symbol_flags: vec!["-Wl,--allow-multiple-definition", "-Wl,--unresolved-symbols=ignore-all"]`
- **Windows-GNU** (`:229-232`):
  `"-Wl,--allow-multiple-definition", "-Wl,--warn-unresolved-symbols", "-Wl,--no-fatal-warnings"` — warn-only, still never fatal.
- **macOS**: `-undefined dynamic_lookup` on the lenient pass.

The native-binary linker's two-pass design,
`src/compiler_rust/compiler/src/linker/native_binary/linker.rs` (`run_link_pass`,
`allow_unresolved` parameter, `:213-224`): pass 1 deliberately links with
`/FORCE:UNRESOLVED` (MSVC) / `--unresolved-symbols=ignore-all` (GNU) /
`-undefined dynamic_lookup` (macOS) / `--allow-undefined` (wasm) **to discover the
undefined set**, from which `build_pass1_stubs` (stubs.rs) fabricates definitions.
The freestanding SimpleOS path (`pipeline/native_project/linker.rs:2425-2438`) adds
`--unresolved-symbols=ignore-all` only under `SIMPLE_ALLOW_FREESTANDING_STUBS=1`,
plus unconditional `-z muldefs`.

So an undefined symbol is not an error because the toolchain is **explicitly told
not to make it one**. The pass-1 tolerance is load-bearing (it is the discovery
step of the bootstrap auto-stub mechanism); the tolerance on the **final** artifact
is the accidental part — see Q3.

Consequence: an undefined `rt_terminal_*`/`rt_unwrap_or_trap` becomes a NULL
GOT/IAT slot and a SIGSEGV at first call (documented precedent:
`doc/08_tracking/bug/stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`,
where the link even printed "Unresolved symbol preview" and proceeded).

### 1.2 The safety nets that DO exist fail open exactly where they were needed

Task #97 added post-hoc guards in `linker/native_binary/`:

- `verify_no_undefined_rt_symbols` (`linker.rs:21-60`): parses the **linked
  artifact** and errors on undefined `rt_*` — but
  `Err(_) => return Ok(())  // not an object/executable we can parse (e.g. PE quirks) — skip`.
  It fails open on the very format where the class bit hardest.
- `check_no_fake_rt_stubs` / fabricated-weak-stub check (`stubs.rs:540-615`):
  refuses to let the auto-stub generator paper over a genuine `rt_*` — but skips
  entirely for MSVC (`is_msvc_compiler(...) { return Ok(()) }`, "skip rather than
  misparse") and returns `Ok(())` whenever `nm` output can't be read
  ("fail open rather than block uninspectable targets").
- Both are bypassable via `SIMPLE_ALLOW_UNRESOLVED_RT=1`.
- All are scoped to the `rt_` prefix; a missing **Simple-level** function that
  codegen emitted as a plain symbol is invisible to them.

### 1.3 An unbacked `extern fn` is not a compile-time error by design of two lenient paths

`doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md` (verified
against source): two syntaxes, two fall-throughs —

- `@extern fn` parses as an ordinary **bodyless function**
  (`parser_impl/functions.rs:132-152`); the decorator is dropped as "a codegen
  directive" (`interpreter_eval.rs:656-670`); a call executes zero statements and
  yields nil (or SIGILL under JIT). Nothing checks that a bodyless function is
  backed by anything.
- `extern fn rt_x()` misses the registry with a **logged** error, then returns 0
  and exits 0 (warn-only default; `SIMPLE_STRICT_EXTERN=1` makes it fatal — not
  the default).
- The project has ratcheted rather than fixed this: ~1,466 known unbacked externs
  frozen in `scripts/check/unbacked_extern_baseline.txt`
  (`check-unbacked-extern-ratchet.shs`). A baseline that large is itself the
  answer to "why no error": **an error here would fire 1,466 times on day one**,
  so the semantic stays lenient and only *new* debt is blocked — and the ratchet
  needs a deployed `bin/simple`, so it ERRORs (does not run) on hosts without one.

### 1.4 A whole-program property is checked by nobody before the link

`mem_snapshot_record_promotion` (before `d122c1a4b78`) was imported and called
with no definition anywhere. Import resolution checks that the **module path**
resolves; there is a `check-use-target-resolves.shs` gate ("every use module path
and named member resolves statically") but it sits in the **bootstrap tier** of
`config/check/must_check_gates.sdn` with `push_blocking=false` — it does not run
on push, so a stale import can land. Interpreter execution only fails **if the
call executes**; codegen emits a call to an undefined symbol; the link tolerates
it (1.1). Every stage individually behaves "reasonably"; no stage owns the
invariant "every called function has a definition in the closure."

### 1.5 MIR lowering gaps report only at build because nothing earlier runs MIR

The 120 MCP lowering errors surfaced only at `native-build` because lint and
`check` exercise the frontend (parse/HIR/semantic) — MIR lowering runs only when
someone actually lowers, i.e. at native build or JIT. Moreover the lowering's
`Unresolved` arm is a **cascade sink**: the in-code note at
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:3384-3392`
establishes empirically that Stage-3 "loses its RECEIVER TYPES upstream and drops
everything into this Unresolved arm" — 120 reported errors, one upstream type-loss
root (for-in split: I64 ×23, Tuple ×10, Dict ×0). So the late report is doubly
misleading: late, and mostly a multiplier of one defect.

---

## Q2 — Why can the Linux build not find it?

The framing inverts under evidence: **Linux is not failing to find these defects;
Linux is configured not to look.** The Windows MSVC LNK1120 that started this
investigation was the fleet's **first strict link**. Specific asymmetries:

| # | Asymmetry | Genuine platform difference or tooling accident? |
|---|---|---|
| 1 | ELF final link passes `--unresolved-symbols=ignore-all` (link_config.rs:83); MSVC's default link is strict (LNK1120) and only gets `/FORCE:UNRESOLVED` on the lenient pass-1 | **Accident** — a per-lane flag choice, not a platform necessity. Windows-GNU is also lenient (warn-only), so "Windows caught it" really means "MSVC caught it". |
| 2 | PE/COFF weak-external **functions** never resolve cross-TU — not from an archive (the `ar` index does not list a COFF weak-external), not linked directly, not via `-Wl,-u`, not via `--whole-archive`. Verified against MSYS2 GCC 15.2.0 / binutils 2.42 in commit `1d05b6695ab`. ELF lazily extracts weak archive members fine. | **Genuine** ABI/toolchain semantics difference. `rt_set_args` was silent on Linux and fatal on Windows purely because of this. |
| 3 | Interpreter unknown-extern fallback `try_call_dynamic` resolves via dlopen/dlsym on Linux/macOS (the process's own exported symbols), but on Windows there is **no `simple_runtime.dll`** — only a static `.lib` — so the fallback has nothing to open. Documented in `8426e39b3eb`'s message: "Linux/macOS previously fell through to a *working* try_call_dynamic". | **Genuine** difference in artifact shape (ELF default-exports; PE needs an explicit DLL), but the *reliance* on it as the registration mechanism is an accident: the dispatch table was allowed to be incomplete because the fallback silently compensated on ELF. |
| 4 | Task-#97 artifact guards skip on PE parse failure and skip MSVC `nm` entirely (Q1.2) | **Accident** — ELF-shaped tooling; the guards fail open on exactly the platform that needed them. |
| 5 | `check-no-unresolved-runtime-symbols.shs` measured GREEN on Linux 2026-08-23 while Windows had 68 unresolved. Three stacked reasons: (i) it is **artifact-scoped** — it judges only artifacts present on the host; the Windows artifacts never existed on the Linux box, and with 0 tracked stage binaries it reports `binaries=none(...)` and judges only the archive (script header `:39-48`); (ii) the default archive path `build/simple-core/libsimple_runtime.a` is **overwritten by two lanes** with different symbol sets (core-C capsule, 1,165 symbols, PASS vs `mod_N.o` emit-archive, 414 symbols, FAIL — flipped within one hour, `.claude/rules/vcs.md` 2026-08-24 note); (iii) the runtime symbol set is **per-platform** — `tools.rs:423-429` extends the source list per-OS (`hosted_win32.c`, `runtime_https_openssl_core.c`, …) and TUs are `#ifdef`-gated — so even an honest Linux PASS is not transferable to the Windows link set. | (i),(ii) **accidents**; (iii) **genuine**, and it means a single-platform guard can never certify the fleet. |
| 6 | Two independent runtime source lists — Rust seed `native_project/tools.rs:344-429` and pure-Simple `70.backend/backend/runtime_compiler.spl:400` — with no cross-check. A merge dropped one line from one list while the `.c` file stayed in the tree (`d122c1a4b78`: "the file survived, so nothing looked missing"), and `runtime_terminal.c` was in one and not the other. | **Accident** — duplicated configuration with no parity check. Not platform-specific in principle, but the lists diverge along the lane that each platform exercises. |

---

## Q3 — Prevention (ranked by value/cost)

### #1 (highest value): make the FINAL link fail closed on every platform

The two-pass structure already isolates the load-bearing tolerance: pass 1
(`allow_unresolved=true`) + `build_pass1_stubs` is the bootstrap discovery
mechanism and must stay lenient. What is accidental is that the **final**
artifact is also linked lenient (`link_config.rs:83/146/229-231`) and that the
post-link verifier fails open on PE. Concretely:

1. Drop `--unresolved-symbols=ignore-all` / `--no-fatal-warnings` from the final
   pass on Linux/FreeBSD/Windows-GNU; keep them only where `allow_unresolved` is
   explicitly requested.
2. Extend `verify_no_undefined_rt_symbols` from the `rt_` prefix to **all**
   undefined non-libc symbols, and **fix the PE/MSVC skips** (the `object` crate
   parses PE; the "PE quirks — skip" branch and the MSVC `nm` skip are the
   fail-opens to close). An unparsable artifact must be ERROR, not PASS.
3. Route the known-optional set (weak hooks like `rt_text_slice_audit_level`,
   `rt_cli_get_args` fallbacks, platform-gated families) through the existing
   `RT_KEEP` allowlist rather than through global leniency.

Would have caught: **A** (`rt_set_args`, stale importers, `rt_print`-as-native),
**B** (both dropped registrations — the 18 and the 7 symbols become link errors at
the first build on ANY platform), **C** (`rt_unwrap_or_trap` — the exact incident
its bug record asks for). Cost: near-zero runtime (the linker already does the
work; strictness is free); the real cost is a one-time triage of what currently
only links because of leniency — which is precisely the latent-defect inventory
this document is about. Risk to bootstrap: none if scoped to the final pass;
`SIMPLE_ALLOW_UNRESOLVED_RT=1` remains the escape hatch. Not in
`must_check_gates.sdn` because it is not a push gate at all — it is a compiler
behavior change, which is why it protects every lane including local builds that
never run push gates.

### #2 (cheapest, catches all of B): source-list parity check

A text-level guard: every owned `*.c` under `src/runtime/` (Owned-Code Scope
exclusions applied) must appear in the required source list(s) — the seed's
`tools.rs` roster and the pure-Simple `runtime_compiler.spl` roster — and the two
rosters must agree modulo an explicit, commented per-lane allowlist. Fails on: a
`.c` in the tree that no list compiles (the `runtime_terminal.c` case) and a list
entry with no file (stale roster). This directly detects the merge-drop mechanism
(`d122c1a4b78`) that no diff review can see, because the file survives and only a
line in a list disappears. Cost: seconds, pure text, no compiler or artifact
needed — trivially wireable as a `push` row in `must_check_gates.sdn` today (the
reason similar guards are unwired — needing `bin/simple` or a built artifact —
does not apply). Would have caught: both **B** cases, at push time, on any OS.

### #3: codegen-emitted runtime names as a checked set vs the runtime archive

Already half-exists: `check-no-unresolved-runtime-symbols.shs` compares
codegen-emitted entry names against `libsimple_runtime.a` before any link. Make it
trustworthy and mandatory: (a) give each lane its **own archive path** (the
verdict currently flips when two lanes overwrite `build/simple-core/libsimple_runtime.a`
— the `archive= kind=` status line exists because of this); (b) run it **per
platform** in each lane's bootstrap, since the symbol set is `#ifdef`- and
roster-dependent (Q2 #5(iii)) — a Linux PASS certifies only Linux; (c) promote to
blocking once (a) removes the flip-flop. Would have caught: **C**, and the
undefined halves of **B**. Cost: seconds; currently advisory because the stage
binaries are untracked/stripped and the archive path is contested — (a) fixes the
second, and the archive half needs no binary at all.

### #4: whole-closure "called but defined nowhere" check (the `mem_snapshot_record_promotion` class)

Promote `check-use-target-resolves.shs` (exists; bootstrap tier,
non-blocking) to a push-blocking row, and extend it from "named member resolves"
to "every direct call in the closure resolves to a definition" so a renamed
function's stale importers fail at push. With #1 in place this class also fails
at first native link — but #4 fails it at **push**, before anyone builds, and
covers interpreter-only code that never links. Cost: it already runs in the
bootstrap tier, so the budget question is its wall time on push; if too slow,
scope it to files changed in the outgoing range plus their importers.

### #5: strict-extern by default, ratchet the baseline down

Flip `SIMPLE_STRICT_EXTERN` semantics: unknown-extern is fatal unless the symbol
is in the frozen baseline (reuse `unbacked_extern_baseline.txt`); `@extern`
bodyless declarations get the same treatment (today they are not even registered
— Q1.3). This converts "silent nil / exit 0" into a loud error for every NEW
unbacked extern at **run** time in the interpreter, complementing #1's link-time
gate. Cost: low; the baseline machinery exists. The wired
`push-interpreter-extern-registry-gap` row already blocks NEW compiler-declared
externs missing from the seed registry — this recommendation extends the same
philosophy to call time and to the `@extern` path the registry gate cannot see.

### #6: run MIR lowering (errors-only) under `check`

For **D**: add a `check --lower` mode (or fold into lint's slow lane) that runs
MIR lowering over the target's closure and reports the error set without emitting
code, so "120 lowering errors" appears when the code is written, not when someone
first builds MCP natively. Additionally, make the `Unresolved` sink attribute its
cascade: the in-code analysis (method_calls_literals.spl:3384) shows most errors
share one upstream receiver-type-loss root; an error that says "receiver type
lost upstream (N sibling errors share this root)" turns 120 reports into 1
actionable one. Cost: moderate (lowering time per closure); highest
implementation effort of the six, which is why it ranks last despite being the
only one that touches D.

### Load-bearing vs accidental tolerance — the honest ledger

**Load-bearing (do not remove):** pass-1 `allow_unresolved` + auto-stub discovery
(bootstrap chicken-and-egg); ELF weak definitions for genuinely optional hooks
(`runtime.c:505-517`, `rt_cli_*` fallbacks) — but each belongs on the `RT_KEEP`
allowlist, named, not covered by blanket leniency; `--allow-multiple-definition`
where dual-capsule links legitimately overlap (`c4074eb8dcf`'s Stage-4 analysis).

**Accidental (remove):** leniency on the final link; PE/MSVC fail-open branches in
the task-#97 guards; the dlopen-self fallback acting as a de-facto extern
registry on ELF; two uncrosschecked source lists; a shared archive path written
by two lanes; single-platform guard verdicts cited as fleet-wide.

**Manifest note.** This checkout's `config/check/must_check_gates.sdn` carries 8
push-tier rows; `.claude/rules/vcs.md` documents 13 as measured 2026-08-23 on the
Linux tree — the manifest itself has drifted between lanes, which is the same
duplicated-configuration failure mode as the source lists and worth folding into
recommendation #2's parity philosophy.
