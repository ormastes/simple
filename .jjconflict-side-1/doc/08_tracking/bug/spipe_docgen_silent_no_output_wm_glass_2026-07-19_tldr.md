# SPipe Docgen Silent No-Output — TLDR

- Docgen exited 0 but created no mirrored WM glass manual.
- It printed unrelated compiler warnings and no focused result.
- Expected: artifact path/stub count or a nonzero focused diagnostic.
- The command was not retried; add a CLI output-existence postcondition.

```text
valid spec -> docgen exit 0 -> missing manual (BUG)
```
