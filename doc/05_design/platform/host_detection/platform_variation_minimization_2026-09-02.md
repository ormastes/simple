# Platform Variation Review — .shs / .spl / .sdn

Date: 2026-09-02. Host: Windows 11 (`bin/simple` = Rust bootstrap seed).
Status: **review + decision doc.** No source changes landed — see §7 for why.

**POSIX was not tested.** Every measurement below is from a Windows host.
Claims about Unix behaviour are read from source, not executed.

## 1. Corrected census

Scope: `src/`, `scripts/`, `test/` (working tree, detached HEAD `ca5619dab1e`).

| ext | total files | files w/ platform conditional |
|---|---|---|
| `.spl` | 41,546 | **198** |
| `.shs` | 2,246 | **138** |
| `.sdn` | 438 | **0** |

`.sdn` is genuinely clean — data files carry no platform branching. This is a
real positive result and should stay that way.

Scope note: the `.sdn` total differs from the task's 1,096 because this scan
covers `src/`, `scripts/`, `test/` only; the wider figure includes `doc/` and
vendored trees. The count that matters — conditionals — is 0 under both scopes.

### 1.1 Two figures in the task brief are false positives

- **`$TMP` 1808 / `${TMPDIR` 541 is not a temp-dir cluster.** In `.shs`,
  `$TMP` is overwhelmingly a **local shell variable assigned from `mktemp -d`**:
  45 files contain `TMP=`, 44 files use `$TMP`. It is not `%TMP%`. The real
  environment reads are **36 sites across 15 `.spl` files**
  (`TMPDIR` 17, `TEMP` 10, `TMP` 9).
- **`uname` 175 in `.spl` overstates host detection.** Of the 51 `.spl` files
  invoking `uname`, **19 run it on a remote or guest system** (telnet, SSH,
  QEMU). Those are irreducible by construction — no host primitive can answer
  for another machine. Only **32** are host detection.

  Caveat: this 19/32 split is a **file-level keyword heuristic** (does the file
  mention telnet/ssh/qemu/guest/remote/serial), not a per-call-site
  classification. It is the one number here measured loosely; a file mixing both
  kinds is counted remote. Treat it as an order-of-magnitude correction to the
  175 figure, not an exact tally.

## 2. Classification

### (i) Collapses onto an existing helper — the bulk of the debt

| cluster | count | existing replacement |
|---|---|---|
| `is_windows`-family predicate **definitions** | **24** | one resolver (§3) |
| host `uname` shell-outs in `.spl` | 32 files | `platform_name_raw()` (§3) |
| shell-tuple builder duplicated | 2 | `process_ops._shell_command_args()` vs `backend/io_compat.backend_shell_tuple()` — same logic, two copies |
| `dir_sep` / `path_separator` / `normalize_path` | 2 / 3 / 3 | `src/lib/nogc_sync_mut/fs/host_path.spl` |

The 24 definitions are the headline. Each re-derives "am I on Windows" from a
different mix of `env_get("OS")`, `OSTYPE`, `COMSPEC`, `MSYSTEM` and `uname`,
so they do not agree under `env -i`, under MSYS, or in a cross-compile.

### (ii) Collapses onto a NEW system variable

**None. Zero new variables are recommended.** See §5.

### (iii) Irreducible — keep, but check the layer

| cluster | why irreducible | layered correctly? |
|---|---|---|
| remote `uname` over telnet/SSH/QEMU | queries another machine | yes |
| `cmd.exe /c` vs `/bin/sh -c` | genuine argv difference | **no** — duplicated in 2 places |
| `/d/foo` -> `d:\foo` drive mapping | genuine path difference | yes — `host_path.spl` |
| BSD discrimination (`freebsd`/`openbsd`/`netbsd`) | runtime primitive cannot answer (§3) | yes |

## 3. `rt_host_os_name` — do NOT add it. The chain already exists, unused.

The task proposed a new `rt_host_os_name()` primitive because
`rt_get_host_target_code` is arch-only. That premise is correct but the
conclusion is not: **the primitive already exists under another name.**

```
rt_platform_name()   src/compiler_rust/runtime/src/value/sffi/env_process.rs:1425
                     -> "windows" | "macos" | "linux" | "unix"
```

It is fully backed, not a paper extern — registered in `runtime_symbols.rs:866`,
`codegen/runtime_sffi.rs:1958`, and `interpreter_extern/mod.rs:1794`.

**Verified by execution on this host** (the repo's known failure mode is an
unbacked extern silently returning nil, so this was run, not assumed):

```
$ bin/simple run probe.spl        # extern fn rt_platform_name() -> text
platform=windows
rc=0                              # status read into a variable, not via a pipe
```

A sanctioned Simple wrapper also already exists, in an **allowlisted provider
directory**:

```
src/lib/nogc_sync_mut/sffi/platform.spl:181   fn platform_name_raw() -> text
src/lib/nogc_sync_mut/sffi/__init__.spl:120   pub use std.sffi.platform*
```

**`platform_name_raw()` has zero call sites.** Meanwhile both
`src/lib/nogc_sync_mut/env/platform.spl` and `.../nogc_async_mut/env/platform.spl`
contain **zero** references to it and instead guess from `env_get("OS")` /
`OSTYPE` and shell out to `uname -s`.

This is the exact anti-pattern this repo has repeatedly found — `resolve_methods`
never called, `attach_inferred_type` zero call sites, `is_dir` shelling out while
`rt_dir_exists` sat six lines away.

**Recommendation: add no primitive and no variable. Wire the existing chain.**

**Important limit — the shell-out does not fully disappear.** `rt_platform_name`
collapses everything not windows/macos/linux to `"unix"`, but `detect_os()`
documents `freebsd`/`openbsd`/`netbsd`, and this repo has a live FreeBSD
bootstrap lane. So the correct shape is a short-circuit, not a replacement:

```
platform_name_raw() -> if "windows"/"macos"/"linux": return it
                    -> else ("unix" or nil): fall through to existing
                                             env + `uname -s` logic, unchanged
```

That keeps every Unix path byte-identical, which matters because POSIX cannot be
tested from this host.

## 4. Temp directory

There is no missing temp resolver and **no new variable is warranted.**

- `.shs` already uses the portable primitive: **`mktemp -d`, ~240 sites.**
  `$TMPDIR` respects the POSIX default and works under MSYS.
- `.spl` has only 36 env reads in 15 files, but **~20 separate `*_temp_dir()`
  helpers** (`_dt_get_temp_dir`, `_tp_get_temp_dir`, `_get_temp_dir` x2, …).

The debt here is **duplication, not a missing variable** — same shape as the 24
`is_windows` definitions, and it collapses onto one existing helper the same way.

## 5. Minimal new-variable set: **none**

Argued per candidate, since "add nothing" needs evidence, not assertion:

| candidate | verdict | why |
|---|---|---|
| `SIMPLE_HOST_OS` | **reject** | `rt_platform_name()` already answers, in-process, with no env dependency and no spoofing surface. An env var would be *less* reliable. |
| `SIMPLE_TMPDIR` | **reject** | `mktemp -d` + `$TMPDIR` already portable; the cluster that motivated it was a false positive (§1.1). |
| `SIMPLE_SHELL` / `SIMPLE_SHELL_ARG` | **reject** | The choice is `cmd.exe /c` vs `/bin/sh -c` — a genuine argv difference that belongs in the boundary function, not in a variable a caller can set wrong. Fix by de-duplicating the two copies. |
| `SIMPLE_PATH_SEP` | **reject** | `host_path.spl` is the boundary and already correct. A variable would let callers bypass it. |

Adding a variable moves a decision from a tested boundary function into ambient
environment state that can be unset, stale, or wrong. Every candidate here is
better served by *calling the code that already exists*.

## 6. Overlap with live agents (read-only, not touched)

`src/app/io/`, `src/lib/nogc_sync_mut/io/`, `nogc_async_mut/**`,
`gc_async_mut/**` are owned by other sessions. That covers `process_ops.spl`
(both trees) and the async `env/platform.spl` and its `get_temp_dir`.
**All reported only.** The shell-tuple de-duplication in §2 touches
`src/app/io/process_ops.spl` and must be coordinated with that owner.

That session landed `6a8f487438f` ("drop /bin/sh from nogc_async_mut /
gc_async_mut hot paths") **during** this review, inside the very directories §3
makes zero-claims about. All three load-bearing claims were therefore
re-verified against the post-landing tree and still hold: `platform_name_raw`
callers outside `sffi/platform.spl` = **0**; `rt_platform_name` references in
both `env/platform.spl` trees = **0**; `backend_shell_tuple` still defined at
`src/compiler/70.backend/backend/io_compat.spl:4`.

## 7. Why nothing was landed

The obvious class-(i) fix — have `nogc_sync_mut/env/platform.spl` call
`platform_name_raw()` — is **not blocked by the `rt_*` ratchet.** A
`platform_name_raw()` call site contains no `rt_` token, so it cannot move the
forbidden count that `check-no-direct-rt.shs` gates on; calling the allowlisted
wrapper rather than `rt_platform_name()` directly is precisely the shape that
sidesteps it. (Calling the extern *directly* from that file **would** trip the
ratchet — it is not allowlisted and already carries 4 counted call sites — which
is why the wrapper is the recommended route, not a workaround.)

The single real blocker is behavioural: step 1 changes a **decision procedure**
(`detect_os`), and its Unix paths — including the BSD fall-through in §3 and the
live FreeBSD bootstrap lane — cannot be executed from this Windows host. Per the
standing constraint *never break Unix while fixing Windows*, an untestable change
to how the OS is determined is left as a reviewed recommendation rather than a
blind edit.

The remaining class-(i) items (24 predicates, ~20 temp helpers, 8 path helpers)
are consolidations across files owned by three live sessions. They are
mechanical but not *safe* to do blind, and are sequenced in §8.

## 8. Recommended sequence

1. Wire `platform_name_raw()` into `nogc_sync_mut/env/platform.spl` with the
   BSD fall-through (§3). Verify on Linux **and** the FreeBSD QEMU lane.
2. Re-point the 24 `is_windows` definitions at that one resolver, deleting each
   local copy. Largest single reduction; do it in per-directory batches.
3. De-duplicate `backend_shell_tuple()` into `_shell_command_args()`
   — coordinate with the `src/app/io/` owner.
4. Collapse the ~20 `*_temp_dir()` helpers onto one.
5. Collapse `dir_sep`/`path_separator`/`normalize_path` into `host_path.spl`.

Steps 2-5 remove code without changing behaviour, and each is independently
verifiable. Step 1 is the only one that changes a decision procedure.
