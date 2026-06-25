# `simple_web_html_layout_renderer.spl`

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-WEBRENDER-001"></a>FR-WEBRENDER-001 | Generic-HTML layout render speed under the interpreter | The real layout renderer paints text glyph-by-glyph; a realistic full page (`examples/06_io/ui/sample_page.html`, ~4 KB) renders in ~2m37s under `SIMPLE_EXECUTION_MODE=interpret`. That is correct but far too slow for any interactive or test | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
