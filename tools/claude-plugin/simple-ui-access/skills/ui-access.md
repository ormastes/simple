# UI Access Skill — Canonical Simple UI Protocol

Use the internal UI access protocol when you need to inspect or manipulate
Simple UI surfaces through one stable semantic model.

## Tools

- `ui_access_snapshot`
- `ui_access_surface`
- `ui_access_find`
- `ui_access_act`
- `ui_access_history`

## Workflow

1. Start with `ui_access_snapshot` to see the active surface set.
2. Narrow to one surface with `ui_access_surface`.
3. Use `ui_access_find` by `surface_id`, `kind`, `text`, or `focused_only`.
4. Invoke `ui_access_act` with `canonical_id` and `action`.
5. Inspect `ui_access_history` after actions or unexpected state changes.

## Canonical Identity

Nodes use `surface_id#widget_id`.

Examples:

- `main#submit_btn`
- `popup#ok_btn`

## Rules

- prefer canonical node IDs over raw widget IDs when writing instructions
- prefer `ui_access_find` over manual tree scanning when the target is not known
- use `ui_access_history` for debugging before guessing why a state changed
- treat this plugin as internal-to-Simple UI v1, not an external desktop
  automation interface
