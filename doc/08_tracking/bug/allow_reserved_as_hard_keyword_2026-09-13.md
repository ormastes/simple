# `allow` and `forbid` cannot be used as identifiers — hard keywords the lexer's own comment says are contextual
## Closed 2026-09-16 — ...pect more sites as the tree grows. ## Fix, and why it is not done here Deleting the `"allo

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

- Status: OPEN (2026-09-13)
- Binary: `/home/yoon/dev/cargo-fulltest/release/simple`, sha256 `4dfdf671742007d30210` (Rust seed built 2026-09-13 16:00)
- Base: `origin/main` `f4cd1c306dd`
- Area: `src/compiler_rust/parser/src/lexer/identifiers.rs`

## Repro — three lines, and a control that isolates the name

```
$ printf 'fn main():\n    val allow = 1\n    print allow\n' > allow.spl
$ bin/simple run allow.spl
error: compile failed: parse: in allow.spl:
       Unexpected token: expected pattern, found Allow

$ printf 'fn main():\n    val alow = 1\n    print alow\n' > alow.spl
$ bin/simple run alow.spl
1
```

The only difference is the spelling of the variable, so this is the name, not
the surrounding code.

## Cause — two arms of one `match`, and the later one wins

`identifiers.rs` says, at line 260, in the middle of the keyword table:

```rust
// Note: "allow" is NOT a keyword - it's parsed contextually in unit definitions
// to avoid conflicts with lint-level attributes.
```

and then at line 334, in the AOP block further down the same `match`:

```rust
// AOP keywords
"on" => TokenKind::On,
"bind" => TokenKind::Bind,
"forbid" => TokenKind::Forbid,
"allow" => TokenKind::Allow,
```

The second arm wins. The comment records a deliberate decision that the AOP
keyword set silently reversed; nothing failed at the time because no code in
the tree used `allow` as a name — until one did.

`forbid`, from the same block, has the identical defect — probed the same way:
`val forbid = 1` gives `expected pattern, found Forbid`.

The scope is exactly those two, which is what makes this a defect rather than a
design choice. Every other name in that keyword table that was probed is
accepted as an ordinary identifier in `val` position — `on`, `bind`, `mock`,
`literal`, `alias`, `bounds`, `repr`, `shared` all run and print `1`. So the
parser already treats this family contextually; `Allow` and `Forbid` are the
two that fall through to a hard reservation.

## Impact measured

`test/01_unit/hardware/rv32i/rv32_sv32_walker_spec.spl:103` is
`val allow = pmp_allow_all()`. That one line makes the WHOLE FILE unparseable,
so none of its examples has ever run — the sweep reports it as a single
`compile failed: parse:` line. See
`doc/08_tracking/bug/unit_specs_that_never_parse_2026-09-13.md` for why that
class is worth more than its red count.

`allow` is an ordinary English word for a permission check; expect more sites
as the tree grows.

## Fix, and why it is not done here

Deleting the `"allow" => TokenKind::Allow` arm restores the documented intent
and is one line — but `TokenKind::Allow` is presumably matched by the AOP
parser, so the change needs the AOP paths re-checked and a spec that pins both
`val allow = 1` and whatever AOP form consumes the keyword. It also needs a
seed rebuild to verify, which the UNIT-P1 lane deliberately did not do (it runs
on a seed built from today's tree and does not deploy one). Recorded rather
than half-applied.

The pure-Simple lexer (`src/compiler/10.frontend/core/`) has no `"allow"`
entry, so this is a seed-side divergence: the two front ends disagree about
whether `allow` is a name.

