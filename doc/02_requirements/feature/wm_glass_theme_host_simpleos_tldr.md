# WM Glass Theme Requirements — TLDR

- `aetheric_dark` is the one production theme authority.
- Typed glass semantics must reach WM, Simple GUI, Simple Web, Draw IR, and
  Engine2D without renderer-owned color branches.
- Host and canonical x86_64 SimpleOS use the same theme fingerprint.
- Interaction and accessibility fallbacks remain functional and evidenced.
- Fix gaps at their owning layer; no legacy/private/synthetic shortcut counts.

```text
aetheric_dark package
  -> typed theme -> WM/Simple GUI --------+
                 -> resolved Web CSS -----+-> Draw IR -> Engine2D
                                            -> host + canonical QEMU proof
```
