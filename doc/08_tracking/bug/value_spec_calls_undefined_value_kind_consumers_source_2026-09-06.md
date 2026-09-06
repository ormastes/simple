# `value_spec.spl` calls a helper that is defined nowhere, so one `it` is permanently RED

- **Filed:** 2026-09-06
- **Status:** OPEN — reported, deliberately NOT "fixed". Left RED per
  `.claude/rules/testing.md`: "A correct spec that fails is a legitimate
  artifact ... leave it RED, file a record with file:line and the unblock
  condition."
- **Severity:** Low-medium — one always-failing example in a unit spec. It is
  filed because it is a standing red that makes the interpreter unit directory
  never green, which trains readers to ignore that directory's verdict.
- **Component:** `test/01_unit/compiler_core/interpreter/value_spec.spl:46`

## Symptom

```
$ SIMPLE_TEST_RUNNER_RUST=1 bin/simple test test/01_unit/compiler_core/interpreter/value_spec.spl
Files: 1
Passed: 3
Failed: 1
```

The failing example is `it "uses the canonical value-kind accessor in type
checking"`, which is:

```simple
    it "uses the canonical value-kind accessor in type checking":
        step("uses the canonical value-kind accessor in type checking")
        val source = value_kind_consumers_source()          # <-- line 46

        expect(source).to_contain("extern fn val_get_kind(value_id: i64) -> i64")
        expect(source.contains("val_kind(")).to_equal(false)
```

`value_kind_consumers_source` has exactly ONE occurrence in the whole tree —
this call site:

```
$ /usr/bin/grep -rn "value_kind_consumers_source" test/ src/
test/01_unit/compiler_core/interpreter/value_spec.spl:46:        val source = value_kind_consumers_source()
```

The spec's other three examples each define their own reader
(`interpreter_value_source`, line 13); this one's was never written.

## Not a regression, and specifically not caused by the env.spl fix

Measured on both sides of
`doc/08_tracking/bug/interp_scope_slot_reuse_stale_bucket_heads_2026-09-06.md`
(`git checkout <sha> -- env.spl`, same tree, same binary
`bin/release/aarch64-unknown-linux-gnu/simple` 50093192 bytes 2026-09-06 09:59):

```
env.spl pre-fix  : Passed: 3   Failed: 1
env.spl fixed    : Passed: 3   Failed: 1
```

Identical, so this is pre-existing. All 20 of the spec's other `to_contain`
strings were also checked by hand against
`src/compiler/10.frontend/core/interpreter/value.spl` and every one is present,
which is what isolates the failure to this example.

## Why it must not be "fixed" by deleting the example

The assertion it makes is real and worth keeping: it pins that consumers of the
value arena declare `extern fn val_get_kind(value_id: i64) -> i64` and that the
older `val_kind(` spelling has no remaining call sites. Deleting the example,
or softening it to a pending, would drop that invariant.

## Unblock condition

Someone who knows which files the example meant by "value-kind consumers" must
write the missing reader. The name suggests concatenating the sources that
declare `extern fn val_get_kind` — but that set is not recorded anywhere, and
guessing it would produce an assertion that passes for the wrong reason, which
is worse than the current honest red. Until then this stays RED and this record
is its explanation.
