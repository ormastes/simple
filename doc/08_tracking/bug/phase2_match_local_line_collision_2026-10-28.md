# Phase2 seed resolves a match-bound local as an unrelated method

Status: OPEN; diagnostic source workaround only. Owner: compiler bootstrap
name resolution/HIR lowering. Root-cause repair remains pending.

On 2026-10-28, source revision `597b86aef358da3bd2f4a752dfd06784524a9e9a`
in `D:/dev/simple-phase2-rebuild-20261028` failed Phase2 native compilation.
The retained evidence is
`C:/dev/simple-phase2-rebuild-20261028-output4/logs/x86_64-pc-windows-gnu/stage2-native-build.log`.
It reports 1608 compiled files, zero reused, and one failure.

The failing owner is `src/lib/scv/structural_pack_v1.spl`, function
`_syntax_pack_line_v1`. Its valid local binding is:

```simple
val line = match validated_utf8_bytes_to_text_linear(line_bytes):
    Ok(value): value
    Err(_): return ("", start, "ERROR invalid syntax pack line\n")
(line, end, "")
```

The producer instead attempts a GlobalLoad of imported function `line`, named
`compiler__frontend__core__flat_pool_packed_v1___Walk_dot_line`. Code generation
correctly refuses to build a NULL function value because the value's type is
not a function type. This is evidence of incorrect lexical resolution, not
evidence that the source should return a function. The exact lowering stage
that loses or overrides the local binding has not yet been isolated.

The initial workaround renamed that local and its tuple use to
`syntax_pack_line_text`. UTF-8 validation, error propagation, byte bounds,
tuple contents and return types are unchanged. No stub fallback is enabled.
The original failed output and compatible cache must remain retained; a retry
must have a separate log/attempt identity.

Removal gate: repair the producer's lexical binding handling, compile the
original spelling in the same full entry closure (including `_Walk.line`),
and verify decoded text, newline offset and invalid-UTF-8/truncation errors.
Then remove the workaround and run the original form through a rebuilt chain.
A renamed-local compile pass alone does not close this compiler bug or admit
Phase2, Hello execution, Phase3, or test-runner verification.

Validation at registration: original failure retained; workaround execution
pending the parent bootstrap retry. No runtime PASS claimed.

## Retry evidence: rename did not repair the missing local

The retry ending 2026-10-28 10:54:45 local time reports
`compiled=2 reused=1606 failed=1 scope=scope-f44db1e977686b25`.
Its GlobalLoad error names `syntax_pack_line_text` as an unresolved identifier.
This proves the changed source was compiled and rules out a stale failure
cache. The initial unrelated method resolution was a fallback symptom: the
match-result local itself is missing when lowering the final tuple.
The rename-only workaround failed and must not be reported as validated.

The revised diagnostic workaround returns the complete tuple directly in
each terminal match arm, eliminating the missing result-local boundary.
The successful arm returns `(value, end, "")`; the error arm retains
`("", start, "ERROR invalid syntax pack line\n")`. Truncation checking and
UTF-8 validation remain unchanged. Execution of this revised form is pending.
The original binding form above remains the producer repair/removal regression.

## Revised workaround build result

The revised form passed module compilation in the cached Phase2 rebuild.
The final link failed on duplicate providers and unresolved runtime symbols;
no resulting compiler or runtime execution was verified.
