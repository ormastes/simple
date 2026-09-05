# Shared seed rebuilt 2026-08-18 10:12 breaks ALL instance-method dispatch — receiver types as `object`

- **Status:** OPEN — affects every lane using the shared seed binary
- **Date:** 2026-08-18
- **Severity:** **Critical.** A 14-line hello-world class fails. Any spec or
  program that calls an instance method on a class value is broken.
- **Area:** the shared seed binary
  `/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`
  (every lane's `bin/simple` is a symlink to it)
- **Found while:** reconciling a contradiction between two measurements of the
  same spec, on the same source, an hour apart.

## Minimal reproducer

```
use std.spec.{describe, it, assert_equal}

class Greeter:
    name: text

impl Greeter:
    static fn create(n: text) -> Greeter:
        Greeter(name: n)
    fn greet() -> text:
        "hello " + self.name

describe "class method dispatch":
    it "calls a static constructor and an instance method":
        val g = Greeter.create("world")
        assert_equal(g.greet(), "hello world")
```

```
✗ calls a static constructor and an instance method
  semantic: method `greet` not found on type `object` (receiver value: Greeter(name: world))
Results: 1 total, 0 passed, 1 failed
```

Note precisely what the error says: the receiver **value** is correct —
`Greeter(name: world)`, so the static constructor ran and built the right
object — but its **type** is `object`, so instance-method lookup fails. The
class's static method resolves; its instance methods do not.

## Binary identity (the whole point — record it with every measurement)

```
$ readlink -f bin/simple
/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
$ stat -c 'size=%s mtime=%y' "$(readlink -f bin/simple)"
size=59645008 mtime=2026-08-18 10:12:23.164167908 +0000
```

## How it was found — a result that changed under identical source

`test/01_unit/lib/nogc_sync_mut/web_framework/auth_token_strict_base64url_spec.spl`
was measured **twice on byte-identical source**:

| when | binary | result |
|---|---|---|
| before 10:12 | previous build | `Results: 9 total, 9 passed, 0 failed` |
| after 10:12 | build of 10:12:23 | `Results: 9 total, 5 passed, 4 failed` |

The 4 newly-failing examples are exactly the ones that construct a class and
call a method on it:

```
✗ POSITIVE CONTROL: module under test loaded and a VALID token verifies
    semantic: undefined field 'algorithm' on value of type 'object'
✗ POSITIVE CONTROL: a generated token still verifies
    method 'generate_token' not found on type 'object'
✗ REPRODUCING: malformed payload segment is rejected
✗ DEFECT CLASS: residue-1 payload length is rejected
    method 'verify_token' not found on type 'object'
```

The 5 that still pass are pure-function decode-rejection tests that never touch
a class receiver — which is why the failure looked domain-specific at first
rather than universal.

**Isolation performed.** A concurrent change to `base64.spl` /
`auth_middleware.spl` / `password_reset.spl` was the obvious suspect. It was
`git stash`ed away, restoring those three files to exactly their committed
state at `051ccaea260`, and the spec was re-run: **still 5 passed, 4 failed.**
So the regression is not in the Simple sources — the only variable left was the
binary. The hello-world reproducer above then confirmed it directly.

## Consequences

1. **A `main`-committed claim of mine is now unreproducible.** Commit
   `051ccaea260` states this spec is "9 total, 9 passed, 0 failed". That was
   truthfully measured at the time, on the then-current binary, but it does not
   reproduce on the 10:12:23 build. Corrected here rather than left standing.
2. **Every lane's test results are silently non-comparable across a seed swap.**
   CLAUDE.md already warns that the symlink target is replaced mid-session
   ("3 distinct builds seen in one session") and instructs recording binary
   identity alongside any timing. This incident shows the same discipline is
   required for **pass/fail**, not just performance.
3. Any green run recorded today should be re-verified against a known binary
   before being trusted, in this lane and others.

## What is NOT established

Which change in the 10:12:23 build caused it. That build was produced by
another lane; this lane did not build it and must not replace it (it is shared
and in use). The reproducer above is deliberately minimal so whoever owns that
build can bisect it quickly.

Also unestablished: whether the earlier binary was *correct* and the new one
regressed, versus the new one exposing a latent defect. The hello-world case
makes the former overwhelmingly likely — instance-method dispatch on a class is
not an edge case — but it is not proven here.
