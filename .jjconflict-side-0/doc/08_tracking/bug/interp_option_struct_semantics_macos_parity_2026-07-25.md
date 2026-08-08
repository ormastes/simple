# Interpreted-lane semantics defects on macOS — present in BOTH deployed and stage4-candidate binaries

**Date:** 2026-07-25
**Area:** compiler / interpreter lane (aarch64-apple-darwin)
**Severity:** high (silent wrong values in the default tooling lane)

All three reproduce identically on the deployed `bin/release/aarch64-apple-darwin/simple`
(built 2026-07-11) and on the stage4 candidate built 2026-07-25 from current main —
i.e. they are longstanding parity defects of the compiled interpreter on this
platform, NOT regressions of the stage4 lane. The raw Rust seed
(`src/compiler_rust/target/bootstrap/simple run`) evaluates all three correctly.

## 1. struct copy isolation violated (gate check `struct-copy-isolation`)

```
struct Box: v: int
fn bump(mut b: Box): b.v = 999
fn main():
    val b = Box(v: 5)
    bump(b)
    print(b.v)        # expected 5 (value semantics), got 999 (aliased)
```

Structs passed to a `mut` param mutate the caller's copy — reference semantics
where the language defines value semantics. This is the single red check in the
redeploy gate for both binaries.

## 2. `i64? ?? default` yields float 0.0

```
val i: i64? = nil
print(i ?? 42)        # expected 42, got 0.00000000000000000
```

The coalesce result comes out tagged as float zero. Text options
(`text? ?? "d"`) work.

## 3. `!!` on a Some value prints nil

```
fn give() -> text?: Some("fromfn")
val r = give()
if r.?: print(r!!)    # expected fromfn, got nil
```

`r.?` correctly takes the some-branch, but `!!` loses the payload.

## Repro kit

Probe files preserved at session scratchpad `deploytest/` (v3.spl, v5.spl,
struct_copy_isolation.spl fixture in scripts/check/cert/redeploy_gate/fixtures/).

## Non-parity sibling (tracked separately)

The stage4 candidate additionally garbles conditional-Option-return + `??`
(`fn f()->text?: if c: Some(x) else: nil` → `<unknown>`), which the incumbent
handles; conversely the incumbent breaks plain-nil-return + `??` (prints "nil"
instead of the default), which the candidate handles. Root-cause in progress in
the stage4 deploy arc (see memory project_stage4_macos_deploy_ladder_2026-07-25).
