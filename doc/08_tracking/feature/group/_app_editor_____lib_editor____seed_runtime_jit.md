# `app/editor`_+_`lib/editor`_+_seed_runtime/jit

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-EDITOR_TUI_RENDER_COMPLETION_2026_05_29"></a>EDITOR_TUI_RENDER_COMPLETION_2026_05_29 | Editor TUI render completion + ctrl module consolidation | ## Context The editor-TUI render goal is partly landed. On `main` as of `knrqtpow`: the `_layout_find_group_index_local` SIGSEGV is fixed (`.id.value`→`.id`, was deref'ing an `i64` as a pointer), and the previously-undefined UI-state types | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
