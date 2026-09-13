# `namespace` is hard-rejected as an identifier

Date: 2026-09-07
Severity: MEDIUM (blocks a Kubernetes-vocabulary field name; workaround is a rename)
Status: OPEN
Binary: `bin/release/aarch64-unknown-linux-gnu/simple` (Rust seed, 50093192 bytes, mtime 2026-09-06 09:59:11)

## Symptom

Declaring a struct field or a local variable named `namespace` is refused by the
compiler's "common mistake" check, at both the declaration and every use site:

```
error: Common mistake detected: See error message for details
  --> src/lib/common/contracts/orchestration/resource_v1.spl:33:5
   |
33 |     namespace: text
   |     ^
Use 'mod' for modules instead of 'namespace'.

C++:     namespace math {}
Simple:  mod math:
```

Reproduced on three shapes in one file: `namespace: text` (struct field, line 33),
`var namespace = "default"` (local, line 427), and `d.meta.namespace` (field read
in a caller).

## Why it matters

`namespace` appears in NEITHER reserved-keyword list: `.claude/rules/language.md`
§ Reserved keywords does not name it, and `/usr/bin/grep -n namespace
doc/07_guide/quick_reference/syntax_quick_reference.md` (the 124-keyword extract) returns
nothing. So
the rejection is undocumented. It is also a first-class name in the domain the
orchestration lane models — Kubernetes `metadata.namespace` — so the workaround
(`ns:` for the field, `namespace` kept only as the SDN key text) makes the typed
model read differently from the wire format it decodes.

This is the same defect class as `pub` / `move` / `examples` / `admit`: a reserved
token rejected at a use site where it is unambiguously an identifier. Those were
made contextual; `namespace` was not.

## Expected

`namespace` is the module keyword only where a module declaration can appear.
In a field declaration, a `var`/`val` binding, a parameter, a named argument, or
after a `.`, it is an ordinary identifier.

## Workaround in place

`src/lib/common/contracts/orchestration/resource_v1.spl:31-37` — field named `ns`
with a comment citing this record. Do not "clean up" that comment without fixing
the compiler.

## Repro

```bash
printf 'struct M:\n    namespace: text\n\nfn main():\n    print("x")\n' > /tmp/ns.spl
bin/simple run /tmp/ns.spl   # -> Common mistake detected
```

## Related

- `doc/08_tracking/bug/pub_reserved_identifier_undocumented_2026-08-10.md`
- `doc/08_tracking/bug/move_identifier_rejected_as_expression_2026-08-15.md`
- `doc/08_tracking/bug/admit_is_a_hard_keyword_unusable_as_identifier_2026-08-21.md`
