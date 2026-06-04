# `simple_web_html_layout_renderer.spl`_+_`browser_renderer.spl`

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-WEBRENDER-003"></a>FR-WEBRENDER-003 | Chrome-compatible text antialiasing / CSS coverage | The real layout renderer covers block flow, the CSS cascade for color / background / font-size / text-align / padding / margin, and word-wrapped text. It does not implement Chrome-compatible glyph antialiasing, LCD subpixel/gamma compositin | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
