# simple_db

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-SIMPLE-DB-0003"></a>FR-SIMPLE-DB-0003 | Add learned cardinality estimation for Simple DB planning | Once Simple DB has a real planner path, add a learned cardinality-estimation experiment that can coexist with BRIN summaries and conventional statistics. - isolated behind a planner experiment flag | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
