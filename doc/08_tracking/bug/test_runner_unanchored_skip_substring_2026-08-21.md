# Test discovery excluded 8 passing specs via an unanchored `# @skip` substring match

Status: FIXED (discovery gate) — 2026-08-21; two non-gate copies remain, see below
Found: 2026-08-21
Area: `src/lib/nogc_sync_mut/test_runner/test_runner_files.spl`

## Symptom

Eight spec files were silently absent from default `bin/simple test` discovery.
All of them pass when run explicitly. None of them was ever meant to be skipped.

## Cause

The discovery gate tested the **whole file content** for the marker as a
substring, with no line anchoring:

```
# Skip files with # @skip or # @pending unless running --only-skipped
if not options.only_skipped:
    if content.contains("# @skip") or content.contains("# @pending"):
        continue
```

Any file that so much as *mentions* `# @skip` — in a prose comment, in a
docstring, or inside a string literal — was therefore dropped from the run.

## Blast radius

13 spec files contain the substring. 5 are legitimate
(`test/fixtures/unstable_mode/{pass_a,pass_b,fail,crash,timeout}_spec.spl`,
deliberate fixtures with a real directive). The other 8 were accidental:

| spec | why it matched | executed | failed |
|---|---|---|---|
| `test/01_unit/std/pending_on_spec.spl` (+ `test/unit/` mirror) | comment `use # @pending` | 6 | 0 |
| `test/01_unit/lib/common/pending_on_spec.spl` (+ mirror) | same comment | 6 | 0 |
| `test/01_unit/app/test_runner_new/test_manifest_spec.spl` (+ mirror) | `content.contains("# @pending")` in an assertion | 26 | 0 |
| `test/02_integration/app/check_skip_log_modes_spec.spl` (+ `test/integration/` mirror) | `# @skip` inside a heredoc string literal | 4 | 0 |

**42 passing assertions** were being lost.

Note the self-concealing shape: `check_skip_log_modes_spec` and
`test_manifest_spec` are precisely the specs that cover the skip machinery, and
the skip machinery was excluding them. The feature's own tests could not
report the feature's own bug.

## Fix

Added a line-anchored helper in `test_runner_files.spl` and used it at the
discovery gate:

```
fn has_skip_directive(content: text) -> bool:
    val lines = content.split("\n")
    for line in lines:
        val trimmed = line.trim()
        if trimmed == "# @skip" or trimmed == "# @pending":
            return true
        if trimmed.starts_with("# @skip(") or trimmed.starts_with("# @pending("):
            return true
    false
```

A line now excludes a file only when the line **is** the directive. The
parameterised `# @skip("arm64")` form is preserved.

## Verification

Both directions checked against the real string operations:

| input | expected | got |
|---|---|---|
| `# @skip` as its own line | excluded | excluded |
| `  # @pending` (indented) | excluded | excluded |
| `# @skip("arm64")` | excluded | excluded |
| `# uses # @skip in docs` | **kept** | kept |
| `val c = "# @skip\nbody"` | **kept** | kept |
| `content.contains("# @pending")` | **kept** | kept |

The 5 intentional fixtures stay excluded; the 4 distinct accidental specs run
and pass (`OK`, 0 failed) individually.

Full-suite confirmation of the recovered discovery count is **not** included:
a full suite and a bootstrap were running concurrently on this host and a
directory-level discovery run could not complete within 10 minutes under
load average 24+. That remains to be confirmed on a quiet box.

## Follow-ups (not fixed here)

The same unanchored pattern exists in two other files. Neither is the discovery
gate, so neither drops tests from a run, but both will misclassify for the same
reason:

- `src/lib/nogc_sync_mut/test_runner/test_manifest_scanner.spl`
- `src/app/check_skip/main.spl`

## Related

- `doc/09_report/skipped_flaky_test_census_2026-08-21.md` §2b, §4
