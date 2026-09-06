# macOS bootstrap blocked at origin/main: seed compile break + Linux-only Stage-3 authority lib (2026-09-06)

**Status:** partially FIXED (3 fixes in this change); the remaining `/proc` coupling is documented below.
**Host:** aarch64-apple-darwin, macOS 25.5.0. **Base:** `1bd13da6125`.

## Symptom

`sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2`
failed three times in a row on macOS, each time at a different Linux-only
assumption, before any Simple code was compiled.

## Defects found, in the order they fired

### 1. Rust seed does not compile on macOS (E0609, blocking)

`src/compiler_rust/runtime/src/cache_host_authority_v1.rs:166`, the
`#[cfg(any(target_os = "macos", target_os = "ios"))]` arm of `stat_nsec_equal`,
read `a.st_mtimespec.tv_nsec` / `a.st_ctimespec.tv_nsec`. Against the pinned
`libc`, Apple's `libc::stat` exposes `st_mtime_nsec` / `st_ctime_nsec` (plain
integers), so the macOS arm — the only arm macOS compiles — never built:

```
error[E0609]: no field `st_mtimespec` on type `&libc::stat`
error: could not compile `simple-runtime` (lib) due to 4 previous errors
```

The Linux, Android and FreeBSD arms directly above already use the correct
field names; only the macOS arm diverged. Fixed by making it match them.

Landed in `72b11296929` / `2cf4bb13366` / `478f4b1b093` (cache daemon authority
receipts); those changes were never compiled on a macOS host.

### 2. `stat -Lc` is GNU-only (`scripts/check/lib/bootstrap-stage3/authority.shs:1659`)

```
stat: illegal option -- c
authority.shs: line 1660: $1: unbound variable
```

BSD `stat(1)` has no `-c`. The repo idiom elsewhere
(`scripts/bootstrap/bootstrap-phase-verification.shs:66`) is
`stat -c ... || stat -f ...`; this site did not use it. `%d` and `%i` are the
same letters in both dialects, so the fallback is a literal one-liner. Fixed.

### 3. `/proc/self/stat` read unconditionally (`authority.shs:1188`)

```
authority.shs: line 1188: /proc/self/stat: No such file or directory
error: could not prepare immutable Rust authority generation
```

`bootstrap_stage3_directory_snapshot` read its own pid from procfs in order to
pin the trusted `/proc/<pid>/fd/N` magic-link arm of the `case` below it. macOS
has no procfs, so the read aborted the function before the plain-directory arm
— which is fully portable — could be selected.

Fixed by making the procfs read conditional and leaving the pid empty when
there is no procfs. This is still fail-closed: without a pid the magic-link arm
cannot match, and the existing `/proc/*) return 1` arm continues to reject
every other `/proc` path.

## Provenance: this is a regression, not a long-standing gap

The whole `scripts/check/lib/bootstrap-stage3/` tree arrived in the range
`e8cfd13ef6d..1bd13da6125` with `848f626638b` ("surgical extraction of PR #235 —
secure stage3 bootstrap + backend transport"). `/proc/self/stat` does not appear
in `manifest-verify.shs` at `e8cfd13ef6d`. That is consistent with
`bootstrap_stage2_admission_refused_by_concurrent_source_edits_2026-09-05.md`,
where this same mac reached Stage-2 admission on the older script version.

## Still OPEN: Stage 3/4 manifest verification is Linux-only

`scripts/check/lib/bootstrap-stage3/manifest-verify.shs` is not portable in the
same shallow way. It uses `/proc/<pid>/fd/8` as a *readable path* to prove that
the manifest it hashed is the manifest it holds open (`:136`, `:150`, `:171`,
`:174`), reads `/proc/self/stat` at the top of
`bootstrap_stage3_verify_manifest_impl`, writes phase status to
`/proc/self/fd/159`, and hard-codes GNU `stat -Lc '%f'` raw-mode output
(`[ "$3" = 8100 ]`). 19 `/proc` references in that file alone; 50 across the
directory.

Descriptor-pinned re-open is a deliberate security property, not an accident, so
the macOS equivalent (`/dev/fd/N`, whose fdesc semantics differ) needs a design
decision rather than a substitution. Until that is made, any bootstrap lane that
reaches Stage 3 or Stage 4 manifest verification — which includes every
`--deploy` route — fails closed on macOS.

## What to do

- The three fixes above unblock Rust authority publication and Stage 2 on macOS.
- Stage 3/4 on macOS needs the descriptor-pinning port. File as its own task;
  do not paper over it by hand-copying a seed into `bin/release/**`
  (`.claude/rules/bootstrap.md` documents why that recurs).

## 4. The C runtime does not compile on macOS either (blocking every push)

`sh scripts/check/check-c-runtime-compiles-push.shs` — a BLOCKING push-tier gate
— is red on `origin/main` from any macOS host, so no push from this platform can
pass its own pre-push hook:

```
FAIL — 2 file(s) failed to compile: src/runtime/runtime_cache_host_authority_v1.c
       src/runtime/test/rt_cache_host_authority_v1_selfcheck.c
```

Same root as defect 1, in C this time.

- `runtime_cache_host_authority_v1.c:121` compared `a.st_mtim.tv_nsec` /
  `a.st_ctim.tv_nsec`. Those are the POSIX-2008 spellings; Apple's `struct stat`
  spells them `st_mtimespec` / `st_ctimespec`. Fixed with `SPL_STAT_MTIM_NSEC` /
  `SPL_STAT_CTIM_NSEC` next to the includes. Note the site sits *above* the
  file's own `#if defined(__linux__)` daemon guard at `:176`, which is why the
  guard did not cover it.
- `rt_cache_host_authority_v1_selfcheck.c` used `SOCK_CLOEXEC`, `struct ucred`
  and `SO_PEERCRED` unguarded. Those exercise the provider's daemon lane, which
  is already `#if defined(__linux__)` only, so the two daemon check groups and
  the four helpers that serve them are now compiled only there.

  The non-Linux `main` deliberately prints what it did **not** run —
  `3 check group(s) passed; 2 daemon group(s) NOT exercised on this host` —
  rather than printing the old `5 check group(s) passed`. A count that silently
  drops two groups reads as a full pass on a host that never exercised them.

Verified on macOS: `cc -std=gnu11 -Wall -Wextra` compiles both files with no
warnings, and the linked selfcheck runs and exits 0 with the honest count.

## Step-over record: `push-sffi-v2-authority` is red on unmodified origin/main

With defect 4 fixed the C-runtime gate passes and the next BLOCKING push-tier
gate fails instead:

```
sffi-v2-authority: FAIL — 3 of 46 guard(s) failed
push-must-check: BLOCKING gate push-sffi-v2-authority failed (exit 1)
```

Pre-existing offenders, recorded here as vcs.md requires before any step-over:

| audit | file it reads | verdict |
|---|---|---|
| `bootstrap-probe-args-sffi-authority.shs` | `src/app/cli/bootstrap_probe_args.spl` | `@unsafe(reason, capabilities: [ffi])` expected 1, actual 0; `rt_get_args` unsafe-wrap expected 1, actual 0 |
| `interpreter-eval-ast-sffi-authority.shs` | `src/app/interpreter/ffi/ast_ffi.spl` | `unsafe_tagged_declarations` expected 29, got **0** |
| `test-codegen-quick-sffi-authority.shs` | `src/app/compile/test_codegen_quick.spl` | `local_raw_extern_declarations` expected 0 got 1; result-lift import/call and error arm each expected 1, got 0 |

This is **not** platform-specific and **not** caused by this change: none of the
five files in this commit is read by any of the three audits, and
`src/app/interpreter/ffi/ast_ffi.spl` at `1bd13da6125` contains bare
`extern fn rt_ast_*` declarations with zero `@unsafe(` tags — the audit expects
a migration that is not in the tree. "expected 29, got 0" is a whole missing
migration, not a drifted count.

This matches the caveat already in `.claude/rules/vcs.md` ("on unmodified
`origin/main` the hook already ends BLOCKING gate ... failed ... pushes are
therefore routinely made with `--no-verify`, which nullifies every guard").
This branch was pushed with `--no-verify` for exactly that reason, after
confirming the two gates this change is actually accountable for —
`push-c-runtime-compiles` (red before this change, green after) and the
workspace root guard — pass.

## Where the lane actually stops on macOS: Stage 2 sanity (two independent blockers)

With defects 1-3 fixed, Rust authority publication succeeds and **Stage 2 builds
a real binary**:

```
Build complete: 834 compiled, 0 cached, 0 failed
  Binary: build/bootstrap/stage2/aarch64-apple-darwin/simple (136387 KB)
  Time: 815.6s compile + 11.0s link = 826.6s total
```

It is then rejected by the shared bootstrap compiler sanity:

```
error: Stage 2 bootstrap compiler sanity failed
  rejected Stage 2 binary preserved: build/bootstrap/stage2/aarch64-apple-darwin/simple.rejected
FAIL — 1 check(s), stage stage2 failed (exit 2) with NO diagnostic text
```

`stage2-sanity.env` isolates it: `version_status=0`, `version_match_status=0`,
`unsupported_status=1` (the bootstrap CLI correctly refuses `run`),
`sha_stable_status=0` — and `frontend_smoke_status=1`, with
`frontend_smoke_bootstrap0_log_sha256=-` (the log was never written).

### Blocker A — the smoke driver hands the child procfs paths

`scripts/bootstrap/bootstrap-from-scratch.sh:1553-1556`:

```sh
frontend_owner_pid=$(perl -e 'print getppid') || return 1
exec 6<"${frontend_bootstrap0_log%/*}" 7<".../run-process-group-bounded-log.pl" 8<"$(command -v perl)"
BOOTSTRAP_STAGE3_PERL_DESCRIPTOR=/proc/$frontend_owner_pid/fd/8
BOOTSTRAP_STAGE3_BOUNDED_LOG_DESCRIPTOR=/proc/$frontend_owner_pid/fd/7
frontend_log_authority=/proc/$frontend_owner_pid/fd/6/${frontend_log##*/}
```

These are the same descriptor-pinned magic links as the Stage-3 lib, so the
coupling is **not confined to Stage 3** as this document's earlier section
assumed — it reaches Stage-2 admission. On a host with no procfs the child
cannot open any of the three, so it writes no log and reports raw status 1,
which is exactly the recorded evidence.

Note the shape of the port, since it is smaller than it looks: fds 6/7/8 are
**inherited** by the child, so the macOS spelling is plain `/dev/fd/N` rather
than a per-pid path. It is still a change to a deliberate security mechanism and
belongs in its own reviewed change, not this one.

### Blocker B — the Stage-2 binary SEGVs in `serialize_mir_function`

Independent of the harness, and the more serious of the two. Running the
preserved binary by hand on the sanity fixture:

```
$ build/bootstrap/stage2/aarch64-apple-darwin/simple.rejected native-build \
    --backend llvm -o /tmp/p2add_out \
    scripts/check/cert/redeploy_gate/fixtures/p2_add.spl
[build] native_cache 0/1 step 5/6 +1719ms dt=1006ms pending
build_rc=139
```

macOS crash report (`simple.rejected-2026-09-07-010218.ips`):

```
EXC_BAD_ACCESS (SIGSEGV), KERN_INVALID_ADDRESS at 0x0000000000000000
  simple.rejected 0x3dd390 compiler__mir__mir_json__serialize_mir_function
```

A null dereference reaching `src/compiler/50.mir/mir_json.spl:624`
(`serialize_mir_function`) during the `native_cache` step, on a 25-line fixture.
`--version` answers cleanly, which is the same shape as
`stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md` and exactly
why `check-stage-binaries-runnable.shs` refuses to treat `--version` as a pass.

This is a compiler defect, fixable in pure Simple, and it is what actually
blocks a macOS Stage-2 admission — fixing blocker A alone would only move the
failure one step later.

## Net position

- Rust seed, Rust authority publication, and the full 834-unit Stage-2 native
  build now work on macOS (defects 1-3 fixed here).
- Stage-2 **admission** does not: blockers A and B above.
- Therefore Stage 3, Stage 4 and every `--deploy` route remain unreachable on
  this host, and `bin/simple` stays pointed at the Rust seed. No binary was
  hand-copied into `bin/release/**`.

## Blocker B, diagnosed to the instruction

The Stage-2 binary **never** completes a `native-build` on macOS, and it fails
two different ways from the *same input*:

```
$ for i in 1 2 3 4; do simple.rejected native-build --backend llvm -o /tmp/zz_r zz_r.spl; done
run1 rc=1   run2 rc=1   run3 rc=139   run4 rc=139
```

Nondeterministic on a byte-identical fixture and a byte-identical binary. The
non-crashing runs are not better: they end

```
ERROR: 1 unit(s)
      reason: (none recorded — BUG in the producer: a non-OK unit must carry a diagnostic)
```

Minimal repro (any of these; the trigger is not input-specific, see below):

```
fn t() -> bool:
    true

fn main():
    print(5)
```

### The fault address resolves inside `serialize_mir_function`, not near it

`nm -n` on the binary brackets the faulting `imageOffset` 0x3dd390:

```
00000001003dce8c _compiler__mir__mir_json__serialize_mir_function   <- encloses
00000001003dd76c _compiler__mir__mir_json__escape_json_string
```

So it is genuinely in that function, +0x504 in — not a nearest-symbol
misattribution.

### What the instruction does

```
00000001003dd384   and  x24, x21, #0xfffffffffffffff8   ; strip the pointer tag
00000001003dd390   ldr  x20, [x24]                      ; <-- SIGSEGV, x24 == 0
```

and `x21` is set once, in the prologue, and never reassigned:

```
00000001003dcea0   mov   x20, x0          ; x20 = the `func` argument
00000001003dcea4   mov   w0, #0xf0
00000001003dcea8   bl    _rt_alloc        ; 240-byte copy of the struct
00000001003dceac   and   x8, x20, #0x7
00000001003dceb4   cmp   x8, #0x1         ; "is this a boxed pointer?"
00000001003dcebc   ands  x9, x20, #0xfffffffffffffff8
00000001003dcec8   csel  x8, x9, x0, ne   ; source = untagged arg, ELSE the fresh alloc
00000001003dcecc   csel  x21, x0, x20, ne ; x21   = the copy,      ELSE the raw argument
00000001003dced0   ldr   x9, [x8]         ; field copy begins
```

Two things follow, and together they explain both failure modes:

1. **When `func` is not a boxed pointer, `x21` becomes the raw argument value.**
   A nil (0) or small unboxed value then makes `x21 & ~7 == 0`, and the
   unguarded `ldr x20, [x24]` at +0x504 dereferences address 0. That is the
   SIGSEGV, and `KERN_INVALID_ADDRESS at 0x0000000000000000` matches exactly.
2. **In that same case the field-copy loop reads from `x0` — the memory
   `rt_alloc` just returned, still uninitialized.** Whether the following 240
   bytes of heap garbage steer the run into the crash or into the silent
   `ERROR: 1 unit(s)` is what makes the outcome vary between runs of the same
   input. The nondeterminism is a symptom of the same defect, not a separate
   race.

So `serialize_mir_function` is reached with a `func` that is not a boxed object.
The call sites are `src/compiler/60.mir_opt/mir_opt/mod.spl:842,852` (pass
before/after cross-check) and the `sha256_text(serialize_mir_function(...))`
sites in `verification_contract_bridge.spl` / `verification_call_manifest_finalizer.spl`.

This is a compiler defect in argument boxing on aarch64-apple-darwin, not a
logic error in `mir_json.spl` — the Simple source dereferences nothing. It is
fixable in pure Simple/codegen, and it is the true gate on a macOS Stage-2
admission: blocker A only decides which error you see first.

Related prior art worth reading before attacking it:
`class_instances_copy_on_bind_and_for_loop_drops_mutation_2026-08-04.md` and
`method_call_on_result_returns_garbage_sentinel_2026-09-06.md`.

## Correction: blocker A is NOT a small port (verified at the mechanism level)

An earlier section of this document guessed that because fds 6/7/8 are
inherited, the macOS spelling would be plain `/dev/fd/N`. That is wrong, and
the consumer shows why. `scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs`
does three things with those values:

- `candidate_frontend_procfd()` (`:35-37`) *requires* the literal shape
  `/proc/<pid>/fd/<n>` and returns 126 otherwise — the admission is defined in
  terms of procfs, not in terms of "some path to a descriptor".
- it **executes** `"$BOOTSTRAP_STAGE3_PERL_DESCRIPTOR" "$BOOTSTRAP_STAGE3_BOUNDED_LOG_DESCRIPTOR"`,
  i.e. runs a binary through its descriptor path and feeds it a script through
  another one.
- it builds log and receipt paths as `$bounded_parent/$bounded_leaf` where
  `bounded_parent` is a **directory** descriptor path (`:47`,
  `candidate_frontend_procfd_leaf` at `:38-40`).

The third one is the wall. `/proc/<pid>/fd/<n>/<leaf>` — resolving a name
*through* a directory descriptor as an ordinary path — has no macOS equivalent.
Apple's `/dev/fd` is fdesc: `/dev/fd/N` re-opens a file, and directory
traversal through it is not supported. There is no spelling of this mechanism
on macOS; it needs a different one (an `openat`-based helper, or dropping
directory pinning), which is a redesign of a deliberate security property.

The same file also uses `sha256sum` (`:33`), which does not exist on macOS
(`shasum -a 256`) — a second, independent macOS gap in the same admission path.

**Consequence.** Stage-2 admission on macOS is blocked for a reason that is
independent of blocker B: even with the compiler defect fixed, the sanity
harness cannot produce admissible frontend evidence on a host without procfs.
Both must be resolved before any macOS `--deploy` is possible, and blocker A is
a design decision rather than a portability fix.
