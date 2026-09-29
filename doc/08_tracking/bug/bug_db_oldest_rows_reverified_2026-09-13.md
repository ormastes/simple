# bug_db.sdn oldest `open` rows re-verified — three no longer reproduce

Status: VERIFICATION RECORD (2026-09-13). The three oldest rows still marked
`open` in `doc/08_tracking/bug/bug_db.sdn` `bugs_active` were re-run on this
host and none of them reproduces. **The DB rows themselves were NOT edited —
see "Why the DB was not touched" below.**

## Host and binary identity (measured)

- Windows 11 x86_64, Git Bash.
- `bin/simple` -> Rust bootstrap seed, `Simple Language v1.0.0-rc.1`.
- `src/compiler_rust/target/release/simple.exe`, 39,265,792 bytes, Sep 13 08:23.

## 1. `md_diag_tuple_element_corruption` (created_at 2026-04-14, P1, `open`)

DB claim: "Interpreter corrupts .2/.3 element access on (i64,i64,text,text)
tuple arrays -- text fields return garbage pointers, trim().len() returns -1".

Repro run:

```simple
fn main():
    val rows = [(1, 2, "alpha", "beta"), (3, 4, "gamma", "delta")]
    for item in rows:
        print(item.0)
        print(item.2)
        print(item.3)
        print(item.2.trim().len())
```

`bin/simple run` output — all correct, no garbage pointer, `trim().len()` is 5
not -1:

```text
1
alpha
beta
5
3
gamma
delta
5
```

**Verdict: does not reproduce.** This is the oldest entry in the whole tracking
system. The `MdDiagLinkRef` struct workaround recorded at
`src/lib/editor/services/md_diagnostics.spl:593` is no longer required by this
defect; removing it is a separate, deliberate change and was NOT done here.

## 2. `md_slugify_string_corruption` (created_at 2026-06-12, P1, `open`)

DB claim: "markdown_slugify returns heap-state-dependent corrupted slugs in
interpreter -- same input gave l-h / l-a / a / section across call sites in one
run".

Repro run (same input from three different frames, interleaved with a different
input to perturb heap state):

```simple
use std.common.markdown.utilities

fn probe1() -> text:
    return markdown_slugify("Alpha")

fn probe2() -> text:
    val t = "Alpha"
    return markdown_slugify(t)

fn main():
    print(markdown_slugify("Alpha"))
    print(probe1())
    print(probe2())
    print(markdown_slugify("Alpha Beta Gamma"))
    print(markdown_slugify("Alpha"))
```

Output — stable and correct across all call sites:

```text
alpha
alpha
alpha
alpha-beta-gamma
alpha
```

**Verdict: does not reproduce.**

## 3. `interp_qualified_enum_is_payload_variant` (created_at 2026-06-14, P1, `open`)

DB claim: "`x is MetaOp.Variant` evaluates false even for a freshly constructed
payload-carrying enum variant".

Repro run:

```simple
enum E:
    A(x: i64)
    B

fn main():
    val a = E.A(x: 5)
    print(a is E.A)
    print(a is E.B)
    val b = E.B
    print(b is E.B)
    match a:
        case E.A(x):
            print(x)
        case E.B:
            print("b")
```

Output — `a is E.A` is now `true`, and the negative case is correctly `false`:

```text
true
false
true
5
```

**Verdict: does not reproduce.** Note this row is *already* inconsistent with
its own markdown entry: `interp_qualified_enum_is_payload_variant_2026-06-14.md`
has said `Status: resolved (2026-06-14)` since the day it was filed, while the
`bugs_active` row has stayed `open` ever since. The DB row is the stale side.

## Why the DB was not touched

`doc/08_tracking/bug/bug_db.sdn` is CRC-guarded and the reader is **fail
closed**: `src/lib/nogc_sync_mut/database/core.spl:467-483` recomputes
`crc32_text(body)` and returns `nil` for the entire file on mismatch. A hand
edit to a status field would therefore not produce a stale-but-readable DB — it
would make the whole database unreadable until the `#sdn-crc32:` header is
recomputed.

A second session was working the same DB from the newest end during this run,
so rewriting the file (which requires rewriting the header over the whole body)
risked clobbering concurrent writes. The three rows above should be flipped to
`fixed` through the normal tooling path by whoever holds the DB, citing this
record.
