# Parser parity: seed accepts an if-expression `else:` indented under the binding; the stage2 candidate rejects it (2026-11-15)

**Status:** OPEN (source workaround landed; parity defect in the candidate parser remains)
**Area:** stage2 candidate parser vs seed parser, if-expression `else:` indentation
**Evidence:** cycle 27 receipt-authorized full run at 96505bb569d (output c27full):
`compiler_cli_build` and `test_runner_build` FAIL (exit 1, 655 s / 473 s) with
`parse error in src/lib/nogc_sync_mut/io/windows_command_owner_v2.spl: 388:13:
unexpected token in expression: : ':'`, introduced by da60e2106d1.

## Symptom

The seed (Rust) parser accepts an if-expression whose `else:` is indented under
the `val` binding:

```
    val evidence = if capture:
        Some(...)
        else: nil        <- accepted by the seed, rejected by the candidate
```

The stage2 (pure Simple) candidate rejects the `else:` token at that position.
The in-tree accepted form aligns `else:` with the binding statement (see
src/lib/nogc_sync_mut/io/process_ops.spl:2925-2935):

```
    val wrapped_cmd = if timeout_ms > 0:
        ...
    else:
        ...
```

The tree was self-inconsistent at 96505bb569d: the stage2 candidate built
from it cannot parse one of its own closure sources (the stage1/2 closure
never parses that file; only the CLI/test-runner rows do).

## Workaround (landed)

windows_command_owner_v2.spl reformats the `else:` to the accepted alignment.
This unblocks the stage2 compiler-tests rows but does NOT fix the parity
defect: any lane committing the indented form will re-break the candidate.

## Proper fix direction

Make the candidate parser accept the indented `else:` form for if-expressions
(or emit a seed-side lint so the form cannot be committed). Until then the
review rule is: if-expression `else:` aligns with the binding statement.
