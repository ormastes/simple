# Gate coverage for spec-vacuity families 3 and 4

- **ID:** spec_vacuity_families_3_4_gate_gap_2026-08-10
- **Status:** DETECTION LANDED (census, warning severity, no blocking gate)
- **Scanner:** `scripts/check/census-spec-vacuity.spl`
- **Binary used:** `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`
  (Rust bootstrap seed; it prints the seed banner). The scanner's module drops
  to the interpreter on `rt_file_is_char_device`, so a whole-corpus run is
  slow but correct.

## Why these two needed a new checker

Four distinct spec-vacuity families were found on 2026-08-09/10. Two are
gated: the non-matcher `expect` tail (`47ba20fda2b`) and the needle that
matches only a comment in the product source
(`doc/08_tracking/test/comment_cheat_spec_census_2026-08-09.md`). Both of
those gates are structurally blind to the two below.

### Family 3 — value-type helper mutates a copy (VTM001 / VTM002)

A `struct` in Simple is a VALUE type. A spec helper

```
fn delete_key(tree: BTree, k: text):
    tree.root.keys.remove(k)
```

mutates a COPY; the caller's `var` is never touched, so the call is a silent
no-op. The failure is **asymmetric**: positive/presence assertions sail
through a no-op and stay green, and only NEGATIVE/absence assertions
(`to_equal(false)`, `to_not_equal`, "was removed", "differs") go red. That
asymmetry is exactly why these sat green — in `report_spec` every painter
mutated a copy so all 18 scenes hashed the same blank buffer, and only the
single "different scenes produce different hashes" assertion caught it; the
other 17 blocks were vacuous.

Background and the proven instances: `doc/08_tracking/bug/spec_value_type_helper_mutates_copy_family_2026-08-10.md`.

**Detection approach.** Build a struct-vs-class kind index by scanning every
`struct X:` / `class X:` declaration across `src/` plus the spec roots, then
for each spec-file `fn`, take the parameters whose base type RESOLVES to
`struct`, and walk the function body (indentation-delimited, triple-quoted
blocks skipped) looking for a mutation through that parameter:

- `VTM001` — field or index assignment: `p.f = `, `p.a.b = `, `p.x[i] = `,
  and the compound forms `p.f += ` / `-=` / `*=` / `/=`.
- `VTM002` — a known in-place mutator called through the parameter:
  `push pop insert remove set clear sort reverse extend append truncate
  resize fill push_str add delete put retain drain swap`.

Two exclusions carry the whole precision story and are both covered by the
positive control:

- **`class` receivers are REFERENCES and are never flagged.** The kind is
  resolved from declarations, never guessed from the name. A checker that
  flagged classes would drown in false positives — `CrsCell`,
  `T32JobManager`, `RecordingRenderBackend3D`, `HostCompositor`, `Engine2D`,
  `Game`, `Canvas`, `SbiMock` are all correct class-receiver helpers.
- **A `mut` parameter writes back and is CORRECT**, so it is never flagged.
- A type that appears nowhere in the index, or that is declared BOTH ways
  somewhere in the corpus ("ambiguous"), is never flagged.

### Family 4 — the spec re-implements the code under test (SHADOW / NOSRC)

`lease_grant_spec`, `request_queue_spec` and `busy_contract_spec` each
re-declare their own `struct LeaseManager` / `struct RequestQueue` and
reimplement acquire/release/enqueue/dequeue inside the spec file, so they
never touch `src/lib/nogc_sync_mut/service/*`. `mcp_analysis_tools_spec.spl`
and `mcp_lsp_tools_spec.spl` build the string under test inside the spec and
assert against it. Such a spec can be 100% green while exercising nothing in
`src/`.

**Detection approach — deliberately split by precision.**

- `SHADOW` (reported as a finding): the spec declares a `struct`/`class`/
  `enum` whose name is ALSO declared under `src/`. This is name-precise and
  is the exact shape of the three proven instances.
- `NOSRC` (reported as a bare count, NOT itemised): a spec importing nothing
  at all. This is the "asserts only against values it constructed itself"
  signal, and it is **low precision** — plenty of specs legitimately test
  pure local logic. It is published as a triage number only. A lint with a
  high false-positive rate gets disabled and is worse than nothing, so this
  half is explicitly a REPORT, not a check.

Neither family is wired into any blocking gate. Warning severity only.

## Mandatory positive control

`--selftest` runs before every scan and is FATAL: on control failure the
script prints `ERROR -- positive control did not reproduce; scan not
attempted` and exits 2 rather than reporting a vacuous zero. Same pattern as
`scripts/check/census-return-type-mismatch.spl` (`cfa6414d356`).

The control source is held in memory, not as a checked-in `.spl`, so a
deliberately-broken file can never be picked up by lint or the test runner
and can never drift away from the checker.

- **5 planted violations MUST fire**: field assign, nested `.push` through a
  field chain, index assign, `.remove(...)`, and `+=` on a field.
- **8 correct forms MUST stay silent**: a `class` receiver mutated the same
  way, a `mut` struct parameter, read-only field access, a `==` comparison, a
  non-mutating `.contains()` query, an unindexed/unknown type, a body that
  only reads the parameter, and a body that mutates a DIFFERENT local.
- Bucket assertions: the field assign must land in `VTM001` and the
  `.remove` in `VTM002`, so the two codes cannot silently collapse.
- Family 4 control: `SHADOW` fires on a name colliding with a known src/
  name and stays silent on a spec-only name.

Verified output:

```
control: 5 planted VTM violations detected, 8 correct forms silent
control: SHADOW fires on a colliding name, silent on a spec-only name
REPORT -- positive control reproduced
```

## Both test trees

`test/01_unit` is a byte-duplicate of `test/unit` (likewise `02_integration`
/`integration`, `03_system`/`system`, `04_external`/`external`,
`05_perf`/`perf`) and BOTH execute, so a raw count double-reports every
finding in them. Every number is printed as **deduped / raw**.

## Usage

```bash
bin/simple run scripts/check/census-spec-vacuity.spl --selftest
bin/simple run scripts/check/census-spec-vacuity.spl --list test
```

Verdict line is last on stdout: `REPORT -- ...` (exit 0, it scanned
something) or `ERROR -- nothing was scanned` (exit 2).
