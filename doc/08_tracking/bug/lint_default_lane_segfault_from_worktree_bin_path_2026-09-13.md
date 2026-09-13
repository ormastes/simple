# `simple lint` segfaults in the default (JIT-attempt) lane when the compiler binary is invoked from a path inside the current working directory's own tree

- Status: OPEN (2026-09-13)

## Summary

`bin/simple lint <any file, including a well-formed, already-clean file>`
consistently segfaults (SIGSEGV, rc 139) when invoked in the default execution
lane, IF the invoked binary's own path lives INSIDE the current working
directory's tree — regardless of which worktree, which copy of the binary
(byte-identical in every case tried), or which target file is linted.
`SIMPLE_EXECUTION_MODE=interpret` avoids the crash entirely and produces the
correct "Lint passed: all files clean" result, so this is specific to the
default lane's native/JIT compile path, not to lint's rule logic.

## Reproduction (worktree `simple-perf-5`, base `f26970e9d93`, 250 commits
ahead of PERF-2's base `99c73a6ac87`)

Binary: sha256 `3d120a6f9ab5704b2225654e4f2773cdbdc787108bd21b67aab657ffe3da72ef`
(identical bytes in every path tried below — `cmp` confirms byte-for-byte
identity).

```
cd /home/yoon/dev/simple-perf-5     # cwd fixed for every line below

# CRASHES (rc 139): exe path is INSIDE cwd's own tree
./bin/simple lint src/lib/common/base_encoding.spl
bin/release/aarch64-unknown-linux-gnu/simple.perf5 lint src/lib/common/base_encoding.spl
cp bin/release/aarch64-unknown-linux-gnu/simple.perf5 bin/simple_pin
./bin/simple_pin lint src/lib/common/base_encoding.spl   # still crashes

# WORKS (rc 0, "Lint passed: all files clean"): exe path is OUTSIDE cwd's tree
/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple lint src/lib/common/base_encoding.spl
cp bin/release/aarch64-unknown-linux-gnu/simple.perf5 /tmp/simple_short
/tmp/simple_short lint src/lib/common/base_encoding.spl

# WORKS (rc 0): same exe path that otherwise crashes, forced to the
# interpreter lane instead of the default JIT-attempt lane
SIMPLE_EXECUTION_MODE=interpret ./bin/simple lint src/lib/common/base_encoding.spl
```

Every crash reproduced consistently; every workaround succeeded every time
tried. `cwd` was `/home/yoon/dev/simple-perf-5` in every invocation above
(never varied) — only the invoked binary's OWN path differs between the
crashing and non-crashing cases.

**Corrected discriminator (this paragraph replaces an earlier, disproved
version of this record):** it is NOT "exe under any worktree's `bin/` tree" —
`/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` IS such a
path and it worked. The pattern consistent with all six data points above is:
**the exe's own path is a descendant of the current working directory**
(both worktree-internal crash cases are `<cwd>/bin/...`; both success cases —
the other clone and `/tmp` — are NOT descendants of this cwd). That is the
default deployment shape (`bin/simple` relative to repo root, run from repo
root), so this is not an edge case.

## Two cheap discriminating probes run before filing

1. **`ulimit -s unlimited` does NOT prevent the crash** (still SIGSEGV, still
   dumps core, `timeout 30 ... ; ulimit -s unlimited` in the same shell).
   This weighs against a plain stack-overflow-from-deep-recursion theory
   (unless the guard page check happens before the raised limit takes effect,
   which cannot be ruled out from outside, but the straightforward reading is
   "not just stack exhaustion").
2. **`git log --oneline 99c73a6ac87..HEAD -- src/compiler_rust
   src/compiler/99.loader src/app/lint src/compiler/90.tools/lint`** shows
   several recent seed/codegen fixes squarely in the area lint's own large
   codebase exercises heavily: `fix(seed): route 4 — LLVM MethodCallStatic
   bound qualified enum helpers by suffix`, `close the Cranelift twin of the
   qualified enum-helper rebind`, `close the second route that rebinds
   qualified .unwrap() to Poll.unwrap`, `bare Optional/Result helpers must not
   suffix-rebind to a user method`, `route the LLVM unwrap family to the
   flat-nullable-aware helpers`, `keep a -> T? constructor's struct name so
   optional-bound field reads use the right offset` — all landed between
   PERF-2's base and this one. PERF-2 measured `simple lint <2-line file>`
   working (rc 0) at the OLDER base. This is a plausible regression window for
   whoever owns JIT/native codegen to start from, not a confirmed root cause.

Not isolated further (out of scope for PERF-5, whose task is `simple test` /
`simple lint` STARTUP OVERHEAD, not JIT correctness): which specific commit in
that range introduced the regression, and why the self-path-under-cwd
condition specifically gates it (candidate: a cache-scope or workspace-root
key derived from `current_exe()`'s relationship to cwd, landing the process on
a different, buggy code path — see `.claude/rules/commands.md` "Fast Path"
section on `compiler_fingerprint`/`object_cache_key`/`SIMPLE_CACHE_SCOPE`).

## Impact on PERF-5

PERF-5's target 2 (`simple lint <2-line file>` startup-cost attribution) was
measured under `SIMPLE_EXECUTION_MODE=interpret` to work around this crash.
The interpret lane is a real, documented execution mode
(`.claude/rules/commands.md`), so opens/timing attribution done under it is
valid, but it means PERF-5's numbers are NOT directly comparable to PERF-2's
default-lane baseline table without also fixing or working around this
crash. Whoever owns JIT/native-lane correctness should treat this as a
blocking regression: `simple lint` is part of the default toolchain
(`.claude/rules/commands.md` "Default tooling" mandate) and currently cannot
run to completion in its default lane from a binary deployed and invoked the
ordinary way (`bin/simple lint <file>`, from repo root, same as every example
in this repo's own docs).
