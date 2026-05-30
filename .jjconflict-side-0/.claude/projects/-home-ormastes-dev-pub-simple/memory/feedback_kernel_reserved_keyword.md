---
name: kernel is a reserved keyword in spipe matchers
description: Variable names like kernel, trace cause parse errors in auto-generated .spipe_matchers_ files because they are reserved keywords
type: feedback
---

`kernel` (and possibly `trace`, `port`, `machine`, `arch`) are reserved keywords in Simple's parser. In spec files, the test runner transforms `expect(x).to_equal(y)` into `.spipe_matchers_` files with `expect x == y` syntax. If `x` is a reserved keyword like `kernel`, the parser produces "expected identifier, found Eq".

**Why:** Discovered while debugging replay_cli_dispatch_spec.spl — `val kernel = parse_flag(...)` followed by `expect(kernel).to_equal(...)` worked in the spec but the matchers file `expect kernel == "boot.elf"` failed because `kernel` is a keyword.

**How to apply:** In test spec files, use short generic variable names (`v`, `k`, `a`) instead of domain-specific names that might be reserved. The documented reserved list (`gen`, `val`, `def`, `exists`, `actor`, `assert`, `join`, `pass_todo`, `pass_do_nothing`, `pass_dn`) is incomplete — `kernel` is also reserved.
