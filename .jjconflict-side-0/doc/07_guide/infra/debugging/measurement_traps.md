# Measurement Traps in Shell-Based Diagnosis

Two cheap-to-avoid traps that produced false conclusions during a debugging
campaign. Both look correct at a glance; both silently corrupt the signal you
think you're reading.

## Trap 1 — unanchored greps when counting a symbol class

**Symptom:** `grep -c` over a build/HIR log matches substrings inside
unrelated identifiers, inflating or fabricating a count.

- `grep -c 'unresolved name: me'` matched `unresolved name:
  metal_sffi_quarantine_submission` and similar — inventing a phantom "20
  residual errors" when the true count was **0** (the fix was already
  complete).
- `grep -c 'parser_error'` matched the *function name* `parser_error_count`
  inside an HIR trace line, falsely reporting a parse regression in a build
  that had zero parse errors.

**Rule:** anchor the pattern to the field boundary (e.g. `'name: X$'`,
`'^\[parser_error\]'`) whenever counting occurrences of a named class, and
print 2-3 matching lines to sanity-check any surprising count before drawing
a conclusion.

## Trap 2 — `git rev-parse` echoes its argument on failure

**Symptom:** `git rev-parse <ref>` prints the literal ref string back instead
of failing when the ref can't be resolved (e.g. a fetch that silently
failed), so a `[ -n "$VAR" ]` guard passes on garbage.

- `O=$(git rev-parse FETCH_HEAD 2>/dev/null)` set `O` to the literal string
  `FETCH_HEAD` when the fetch had failed. The non-empty guard passed, and
  every downstream `git cat-file -p $O:path` silently read nothing —
  producing a false "already fixed upstream" verdict that nearly skipped a
  real fix. This matters especially when several sessions hit the same repo
  concurrently and fetches fail intermittently.

**Rule:** verify with `git rev-parse --verify -q <ref>^{commit}`, which fails
cleanly (empty output, nonzero exit) instead of echoing the input.
