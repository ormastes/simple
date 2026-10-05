# Frozen library imports omitted numbered-directory providers

The source9737/producer776ce2 early Phase4 cohort omitted `src/lib/editor/00.common/{types,keybindings}.spl` and `70.backend/gui_backend.spl` from both its parse and HIR inventories. The files physically exist in the frozen SCV snapshot, but its `src/std` checkout alias does not. Consumers consequently reported missing editor exports and unresolved types.

The entry resolver's generic numbered-directory fallback probed the authored `std/...` path. Its later `std` to `src/lib` rewrite only probed exact directories. The repair applies the existing numbered walker to physical library and family roots after all existing exact probes. It preserves exact precedence and ambiguous sibling rejection; no editor visibility/import workaround is added.

Four added executable cases cover a snapshot without `src/std`, common/backend numbered providers, a numbered family provider, ambiguous siblings, and exact-directory precedence. Runtime validation remains PENDING; live source9737 is immutable and does not contain this repair. No complete Phase4 or bootstrap PASS is claimed.

Evidence: `runtime/windows-restart-20261004/phase34-post-link4/hir-fatal-observation-phase4-full-cli.json`; retained parse queue6708 and HIR queue33000 inventories under `early-phase4-from-phase2/cranelift/full-cli/cache`.
