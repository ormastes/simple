# Theme hard stops — unlanded-fix verification (2026-07-27)

Follow-up to `doc/09_report/open_bug_doc_staleness_audit_2026-07-27.md`, which
flagged three theme-related fail-closed hard stops whose cited commits are not
ancestors of `HEAD`. This report verifies each claim against
`origin/main` = `5a8ccabef5238797bc3341cfc15c1755cbdb6aec` (fetched
2026-07-27), recovers what it can of the missing content, and states plainly
whether each hard stop still fires today.

## Headline correction to the briefing premise

The briefing framed these as *"docs that read as resolved but whose fixes never
landed"*. **That framing is refuted.** All three docs already carry accurate
`Status: open` lines and already state in their own body text that the cited
commits were rejected and never integrated. There was no false "resolved"
status to correct. The upstream audit rows were also correct — it classified
all three `STILL-OPEN`.

The cited shas are **rejected candidates, not fixes**. Reading them as "the fix
commit" inverts their meaning: they are the record of *what was tried and
refused*, deliberately preserved so a fresh lane does not repeat the same
shape.

There is, however, a real and separate documentation defect, which this report
does fix: **every rejected-candidate sha is unrecoverable.** The commits were
made in isolated worktrees, never pushed, and no longer resolve in either the
git object store (`git rev-parse` fails) or the jj store (`Revision doesn't
exist`). A doc citing a bare sha invites the next investigator to
`git show` it and waste a cycle discovering it is gone — which is the same
class of harm the briefing was worried about, arriving by a different route.

## Per-doc table

| Doc | Cited sha | Exists? | Ancestor of origin/main? | Still live? | Disposition |
|---|---|---|---|---|---|
| `theme_ipc_k2_review_hard_stop` | `235ef0250b` | **no** | n/a | — | unrecoverable candidate |
| " | `41eedf1bf5` | **no** | n/a | — | unrecoverable candidate |
| " | `d9554f91af` | **no** | n/a | — | unrecoverable candidate |
| " | *(doc overall)* | — | — | **YES** | status annotated; no code re-landed (large) |
| `theme_snapshot_catalog_review_hard_stop` | `9f9a921689` | **no** | n/a | — | unrecoverable candidate |
| " | `d404042bc4` | **no** | n/a | — | unrecoverable candidate |
| " | `7ed0ae0a1a` | **no** | n/a | — | unrecoverable candidate |
| " | *(doc overall)* | — | — | **YES** (both P1 gaps) | status annotated; no code re-landed (see below) |
| `theme_package_transaction_sync_owner_blocker` | `4f84131c55` | **no** | n/a | — | unrecoverable candidate |
| " | `b1d0b3e27ff8` (codec) | yes | **YES** | n/a | doc claim confirmed accurate |

The single sha in all three docs that is described as *landed* —
`b1d0b3e27ff8e9c751ee8cbb7ec8f5e41bd4aaeb`, "feat(theme): add canonical package
wire codec" — **is** an ancestor of `origin/main`, and its artifact is on disk
at `src/lib/common/ui/theme_package_wire.spl:12`
(`THEME_PACKAGE_INSTALL_WIRE_V1_MAGIC`). Every landed-claim in these docs
checks out; only the rejected-claims are unrecoverable, which is consistent.

## Why the content could not be recovered

Not a rebase-away, and **not** the documented jjconflict-tree incident
(`.claude/rules/vcs.md`), which affected pushed commits on `main`. These
commits were never pushed at all — each doc says so explicitly ("None of the K2
commits was integrated or pushed", "None was integrated or pushed", "cycle 3
stopped and fully reverted without a commit"). The isolated worktrees they
lived in have since been cleaned up, taking the only copy of the objects with
them. `git show` and `jj log` both fail on all seven shas.

Consequently step 2's "check whether the current code already implements the
fix by other means" had to be done by *reading current code against each doc's
prose description* of the rejected work, rather than by diffing. That was done
and is reported below.

## 1. `theme_ipc_k2_review_hard_stop_2026-07-27.md` — STILL LIVE

K1 is confirmed landed and is confirmed to *not* claim what K2 would have
added. `src/os/kernel/ipc/ipc.spl` carries bounded copied payloads
(`:22-23` `MAX_OWNED_PAYLOAD_BYTES=4096`, `MAX_OWNED_QUEUE_BYTES=65536`) and
typed receive states (`OwnedIpcReceiveStatus.{Delivered,MetadataOnly,Empty,
MissingPort,Unauthorized}`, `:307-347`). It self-documents the missing half at
`:301-303` — *"K1 has no dispatcher-authenticated sender identity; record zero
until K2 supplies the actual current task"*. Versioned v0/v1 IDs, reservations,
and dispatcher-bound source identity are all **absent**.

Status of the five P1 rejection gaps against current code:

| # | Gap | Verdict on main |
|---|---|---|
| 1 | x86 compat IDs 220/221 unregistered | **moot** — 220/221 exist nowhere on main; they were a K2 invention. Installed dispatcher registers only 20–24 (`examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c:5625-5644`, `default: return -38` at `:5663`) |
| 2 | glue threads state only for IDs 20..23 | **PRESENT** — `src/os/kernel/arch/x86_64/interrupt.spl:243` `if args.id >= 20 and args.id <= 23:`; only inside that branch are `g_trap_scheduler`/`g_trap_ipc` written back (`:244-247`). Any IPC ID outside the range silently discards mutated state |
| 3 | kernel-internal helpers bypass LSTAR/SFMASK | **PRESENT** — `baremetal_stubs.c:114-119` `rt_x86_syscall` calls `rt_syscall_dispatch` directly, so the SFMASK write at `:83` never clears IF. This is the sole x86_64 userlib syscall impl (`src/os/userlib/syscall_raw.spl:9-12`) |
| 4 | C userlib outside `src/**` accepts raw 20/21 five-register | **PRESENT** — `examples/09_embedded/simpleos_remote_gui/remote_window_runtime.c:5-6` (5-arg `simpleos_syscall`), `:48-51` (raw ID defines), `:104-117` (hand-decoded 32-byte header) |
| 5 | RV32 `syscall6` returns ENOSYS | **moot as written, real as constraint** — no `syscall0..6` family exists; RV32 has exactly one 5-arg wrapper (`src/os/userlib/syscall_raw.spl:66-92`). The ENOSYS stub is not on main, but the underlying "RV32 is five-register only" constraint that produced gap 5 is real |

Three of five gaps are present verbatim; the other two are moot only because
the K2 candidate's own constructs never existed on main. The hard stop's
conclusion — **"Only after K2 lands may `ThemeChangedV1` receive a production
OS transport"** — therefore still binds.

**Disposition: no code re-landed.** Re-landing means a cross-architecture ABI
table for x86_64/ARM64/RV64/RV32, dispatcher registration in C, Simple *and*
Rust paths, a real six-register RV32 path or a decision to stay on five, and a
shared interrupt/preemption/address-space stability owner. That is a large,
multi-arch, product-decision-bearing change under an explicit
independent-review-before-integration requirement. Not a forward delta.

## 2. `theme_snapshot_catalog_review_hard_stop_2026-07-27.md` — STILL LIVE

`src/lib/common/ui/generated/aetheric_dark_theme_snapshot.spl` exists and
initially looked like the rejected work had landed by other means. It has not.
That directory holds exactly one file exposing exactly one nullary function
(`:5 fn aetheric_dark_theme_render_snapshot()`). There is **no catalog**: no
multi-theme table, no lookup-by-key, no `theme_snapshot_catalog` symbol in
`src/**`. The generator is per-theme, not per-catalog —
`src/app/cli/theme_sync.spl:320 fn cmd_compile_to_spl(theme_id, out_path)`
emits one function per invocation (`:334`).

Both P1 authority gaps **still fire today**:

- **Gap 1 — confirmed.** `src/os/compositor/host_wm_theme_bootstrap.spl:19-26`
  early-returns any pre-existing active snapshot after checking only
  *presence* (`:22 if active_wm_theme_snapshot_present():`). It never compares
  `snapshot.id` or `source_manifest_sha256` against `default_theme_id()` or the
  registry. A stale or arbitrary active snapshot is re-applied and returned as
  "the default", exactly as the doc describes.
- **Gap 2 — confirmed, and broader than documented.** Registration at
  `src/os/compositor/host_compositor_core.spl:644-648
  me require_external_web_frame` stores no theme key *at all*. Acceptance at
  `:650-670 me set_external_web_frame` validates window id, origin kind,
  dimensions, checksum, parent/offset and provenance, but never reads the
  active snapshot. The provenance helper
  `src/lib/common/ui/window_scene.spl:338-359` only asserts
  `frame.theme_id != ""` (`:358`) and hex-shape. So the mismatch applies to
  **every** external Web frame, not merely to frames registered before a theme
  change. For contrast, the in-process UI-session path *does* recompare
  (`src/lib/nogc_sync_mut/ui/session.spl:41-48`); it is only the external Web
  frame path that is unguarded.

Two findings not in the original doc:

- The freestanding closure requirement (resume-contract item 4) is currently
  **satisfied**: `simpleos_wm_theme_bootstrap.spl:7-9` imports only
  `common.ui.*`, transitively reaching `std.common.crypto.sha256` and nothing
  else — no `std.fs`, env, process, or `theme_package`. The hosted path pulls
  `nogc_sync_mut.ui.theme_package` (`host_wm_theme_bootstrap.spl:6`) as
  intended.
- **`install_generated_simpleos_wm_theme` has zero production callers.** Only
  its definition at `simpleos_wm_theme_bootstrap.spl:11` exists; nothing
  invokes it. This contradicts its own comment at `:3-5` ("Both canonical
  desktop entries install the exact generated snapshot"). Worth a separate
  bug — it means the generated-snapshot boot path is currently dead code.

**Disposition: no code re-landed.** Gap 1 in isolation looks like a small
edit, and it was tempting. It is not safe to apply unilaterally, for three
reasons. (a) The remedy is a product decision, not a mechanical fix: on a
mismatch, does bootstrap fail closed, or silently reinstall the default? And
is identity `id`, `source_manifest_sha256`, or the full tuple? The doc's
resume contract deliberately leaves this open. (b) The doc's own contract
says *"Start from current `origin/main`, not a piecemeal cherry-pick"* and
requires independent highest-capability review before integration — a
piecemeal repair is precisely the shape that was rejected three times.
(c) Gaps 1 and 2 share an identity-comparison design; fixing one half invents
an identity rule the other half would then have to match. Half-applying would
manufacture the appearance of progress against a fail-closed gate. Written up
instead.

## 3. `theme_package_transaction_sync_owner_blocker_2026-07-27.md` — STILL LIVE

`ThemePackageTransactionStore` **does not exist anywhere in `src/**`** — grep
for the type name and for `theme_package_transaction` returns nothing. None of
the five architectural prerequisites has landed. `install_default_host_wm_theme`
(`src/os/compositor/host_wm_theme_bootstrap.spl:19`) still returns only a
snapshot, handing no persistent transaction store or session to later refresh
consumers — prerequisite 1 verbatim, still unmet.

The doc's one landed-claim is accurate: the canonical
`theme-package-install-wire-v1` codec is present at
`src/lib/common/ui/theme_package_wire.spl:12` and `b1d0b3e27ff8` is an
ancestor of `origin/main`. Its native-ABI probe (prerequisite 2) remains
unadmitted, so the doc's instruction to keep transaction candidates and
publication as canonical text still stands.

**Disposition: no code re-landed.** This doc is explicitly a *prerequisite*
blocker, not a defect with a patch. It blocks on interfaces that do not exist
(persistent hosted session handoff, scalar/wire transaction reads for WM/GUI/
Web, native codec ABI evidence) plus unresolved language-level primitives the
doc names: lazy module-global `Mutex?` initialization races, eager
module-global mutex construction being unsafe in seed/freestanding/native
entry-closure paths, and current atomic integer APIs being single-threaded
stubs rather than CAS/Once. No forward delta is possible until those land.

## What these hard stops actually block

- **`ThemeChangedV1` production OS transport** is gated on K2 (doc 1). The
  notification wire exists but cannot cross a real syscall boundary with
  authenticated sender identity.
- **Hosted/SimpleOS theme parity** is gated on doc 2. Today a stale active
  snapshot can pass as the default, and any external Web frame is accepted
  regardless of the current theme.
- **Atomic theme package installation** is gated on doc 3, which is in turn
  gated on runtime primitives (real mutex/CAS) that are themselves unbuilt.

The three are ordered: doc 3 blocks on runtime primitives, doc 2 blocks on an
identity-authority decision, doc 1 blocks on multi-arch ABI work. None is
close to a one-line repair, and all three docs already say so accurately.

## Actions taken

- Verified all 8 cited shas against `origin/main` (fetched); 7 unrecoverable,
  1 (`b1d0b3e27ff8`) confirmed landed as claimed.
- Verified all 9 documented P1 gaps against current source; 7 present, 2 moot
  on main for stated reasons.
- Annotated all three bug-doc Status lines with the re-verification date, the
  still-live verdict, and an explicit **unrecoverable — do not `git show` or
  cherry-pick** warning on the candidate shas.
- No `src/**` changes. Doc-only commit.

## Recommended follow-ups

1. File the `install_generated_simpleos_wm_theme` dead-code finding as its own
   bug — the generated SimpleOS theme boot path has no callers.
2. Consider a convention that rejected-candidate shas in bug docs are either
   pushed to a `rejected/` ref namespace before the worktree is dropped, or
   recorded as a diff excerpt in the doc. Seven unrecoverable shas across three
   docs is a repeating pattern, not a one-off.
