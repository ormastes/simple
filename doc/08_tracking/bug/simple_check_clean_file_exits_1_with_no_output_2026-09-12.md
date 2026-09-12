# `simple check` on a CLEAN file exits 1 and prints nothing

- Status: OPEN (2026-09-12)
- Found by: BUGFIX-2 fan-out lane, while re-checking
  `simple_check_parse_only_false_green_2026-07-19`
- Severity: high — a false RED with no diagnostic. Any gate or script that reads
  `simple check`'s exit status treats every clean file as a failure, and there is
  no message to explain why.
- Binary: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`
  sha256 `3d120a6f` (Rust bootstrap seed; `--version` says so)

## Repro

```
$ printf 'fn main():\n    val x: i64 = 7\n    print(x)\n' > build/probe/ok.spl
$ SIMPLE_RUST_SEED_WARNING=0 bin/simple check build/probe/ok.spl >out 2>err
$ echo $?
1
$ wc -c out
0 out
$ grep -ci error err
0
```

Zero bytes on stdout, no `error[...]` line anywhere on stderr, exit 1.

## Positive control — the error path DOES work

The same command on a type-invalid file behaves correctly, which is what makes the
clean-file result a defect rather than a general breakage:

```
$ printf 'fn main():\n    val x: i64 = "text"\n    print(x)\n' > d_check.spl
$ SIMPLE_RUST_SEED_WARNING=0 bin/simple check d_check.spl; echo $?
d_check.spl:2:18: error[semantic]: type mismatch: expected HirTypeKind::Str, found HirTypeKind::Int((64, true))
1 error(s) found in 1 of 1 file(s)
1
```

Reproduced on two different clean files, one in a scratch directory and one inside
the worktree, so it is not path-specific.

## Where the success message should come from

`src/app/check/main.spl:335-343` is explicit:

```
    elif errors == 0:
        if syntax_only:
            print "Syntax-only check passed ({checked} file(s)); semantic coverage was not requested"
        else:
            print "Semantic check passed with complete syntax and semantic coverage ({checked} file(s))"
    else:
        print "{errors} error(s) found in {files_with_errors} of {checked} file(s)"

    if errors == 0: 0 else: 1
```

The failing-file output above matches the `else` branch's format byte for byte
(`"{errors} error(s) found in {files_with_errors} of {checked} file(s)"`, no `✗`,
with the word `of` — distinct from the Rust driver's
`src/compiler_rust/driver/src/cli/check.rs:168` `"✗ {} error(s) found in {} file(s)"`),
so the pure-Simple worker IS the one reporting. On the clean file neither the
`errors == 0` message nor the `else` message is printed at all, and the exit code
is 1 rather than the `if errors == 0: 0` this code returns.

So the run is not reaching this reporter on the clean path — it fails earlier and
exits 1 without saying so. That silent-exit path is what needs finding; the
reporter itself looks correct.

## Not investigated here

Whether the early exit is in the CLI dispatch, the file-collection step, or the
semantic pass. Out of scope for the bug-fix shard this was found in.
