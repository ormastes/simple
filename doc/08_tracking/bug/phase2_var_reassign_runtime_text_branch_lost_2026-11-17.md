# Phase 2 compiler: `var` text reassigned in an if/elif branch keeps its old value (final-path texts)

Date: 2026-11-17, evidence updated 2026-11-18. Status: source workaround in place; compiler
mechanism unknown. No `bug_db.sdn` row; this file is the record.

## Symptom
In a native binary built by the frozen Phase 2 compiler (LLVM backend, Windows), this shape
returns its input unchanged for some texts:

```
fn strip_elif(path: text) -> text:
    var plain = path
    if plain.starts_with("//?/UNC/"):
        plain = "//" + plain.substring(8)
    elif plain.starts_with("//?/"):
        plain = plain.substring(4)
    plain
```

Consequence: a Stage 3 compiler built by Phase 2 keeps the `//?/` prefix on the checkout
root, `path_entry_present` returns `PATH_ENTRY_LEAF`, and every build is rejected with
`SCV-E-ADMISSION: directory-alias-inventory-invalid`
(`stage3_alias_inventory_invalid_on_windows_2026-11-17.md`).

## Native evidence (2026-11-18)
One probe binary called four strip shapes on six texts, all equal to `//?/C:/dev/keep/p3`
except the volume identity:

| input | var + if/elif | early return | `val = if/elif/else` (substring) | same (slice) |
|---|---|---|---|---|
| literal | stripped | stripped | stripped | stripped |
| `"//" + "?/C:/..."` | stripped | stripped | stripped | stripped |
| backslash literal `.replace("\\", "/")` | stripped | stripped | stripped | stripped |
| `path_final_existing(root).path` | **unchanged** | stripped | stripped | stripped |
| `path_final_existing(root).identity` | **unchanged** | stripped | stripped | stripped |
| `"" + path_final_existing(root).path` | stripped | stripped | stripped | stripped |

For every input, length, byte length, the first six character codes, and
`starts_with` on `/`, `//`, `//?`, `//?/` were correct, and `substring(0, 4) == "//?/"`
was true. So the predicate is right and the text content is right; the reassignment is
what is lost, and only for the two texts that come out of the
`GetFinalPathNameByHandleW` decode. A concatenated copy of the same text behaves.

The trigger is therefore narrower than "any runtime-built text". What distinguishes
those two texts inside the compiled code is not known.

Not the cause: the `?`-unwrap typing defect (`stage2_try_unwrap_text_typed_as_i64_2026-11-02`).
Replacing `dos?` / `guid?` with typed matches (cc06d5136da) left the probe output at
`FINAL path=//?/C:/dev/keep/p3` on 2026-11-17.

## Workaround
`compile_source_inventory_plain_checkout_v1` (`src/lib/scv/compile_source_inventory_core.spl`)
and the Windows `_path_final_existing` (`src/lib/nogc_sync_mut/io/path_identity.spl`) use
`val x: text = if ...: ... elif ...: ... else: ...`, the form the probe shows working, tagged
`# @workaround bug=phase2_var_reassign_runtime_text_branch_lost_2026-11-17`.

Not proven natively:
- `compile_source_inventory_plain_checkout_v1` still reassigns `var plain` in its trailing-slash
  `while` loop; the probe did not exercise that loop on a final-path text.
- No Stage 3 has been rebuilt with the workaround yet, so the admission failure is not yet
  shown fixed end to end.

`test/01_unit/lib/scv/plain_checkout_runtime_text_spec.spl` pins behaviour in the interpreter
only; the interpreter does not reproduce the defect.

Remove the workaround once a fixed compiler replaces the pinned Phase 2.
