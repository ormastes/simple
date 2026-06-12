# Feature: html_ui_toolchain

## Raw Request
use spipe dev skill, make 2 cli app and a guide for llm. ui editor which produce or update html css file pair, css can be more than one. later it can be gui/tui support. tui css can apply but less functional like html. another is binary ui file builder which can used to native in dyn or merged. so there be two form std one lib file which parsed html css, or for dynsmf which should less than 4kb. main file have map to other smf files which element where and primitive ui will be added on main file. if main file can take all ui bin data than one file is enough. the ui lib smf generated backgound during build like other spl file. however llm can call it and verify it is parsable and impl all ui elements properly. with this tool. find theme html and css and make full ui lib and fix and add feature of tool and make guide for make html base ui. research web and make small tasks and evaluate needed model for tasks and assign small model and review by big model, do pherallel.

## Task Type
feature

## Refined Goal
Build an HTML-based UI toolchain: a `ui-edit` CLI that creates/updates HTML + one-or-more CSS files, a `ui-build` CLI that compiles HTML/CSS into binary UI artifacts (std single-lib SMF that parses HTML/CSS, or dynSMF parts each < 4 KB with a main file mapping elements to part SMFs, merged to one file when it fits), wired into the existing background dynSMF build lane, with an LLM-callable verify mode, a themed full UI element library, and an LLM guide for authoring HTML-based UI.

## Acceptance Criteria
- AC-1: `bin/simple run src/app/ui_edit/main.spl -- new <dir>/<name>` creates `<name>.html` + `<name>.css`; `set-css`, `add-element`, `list` subcommands update an existing pair; an HTML file may reference >1 CSS file and all referenced CSS files are managed.
- AC-2: `ui-edit` round-trips: editing an existing HTML/CSS pair preserves unrelated content (verified by spec comparing before/after DOM/rule dumps).
- AC-3: `bin/simple run src/app/ui_build/main.spl -- build <name>.html -o build/dynsmf/ui/` emits either (a) `--form=std` one lib SMF embedding parsed HTML/CSS, or (b) `--form=dyn` a main SMF + part SMFs where each part is < 4096 bytes, and the main file contains an element→part map; when total payload fits in the main file, only one file is produced.
- AC-4: `ui_build --verify <artifact>` exits 0 only when the artifact parses (valid `SMF\0` magic + manifest) and every UI element referenced by the source HTML is implemented in the catalog; nonzero with a per-element report otherwise — callable by an LLM as the parse/coverage oracle.
- AC-5: The UI lib SMF artifacts are produced by the existing background build lane (entry added to dynSMF build plans; `scripts/check/check-low-dependency-dynsmf-build-plans.shs` stays green).
- AC-6: A theme (HTML + CSS) covering the full primitive element set (button, input, select, checkbox, radio, textarea, label, heading, paragraph, list, table, image placeholder, container/panel, nav/menu) exists under `src/lib/common/ui/theme_html/` and `ui_build --verify` passes on it.
- AC-7: An LLM guide exists at `doc/07_guide/ui/html_ui/llm_html_ui_guide.md` documenting: editor workflow, builder forms (std vs dyn vs merged), verify loop, theme usage, and TUI subset notes (which CSS properties degrade on TUI).
- AC-8: SPipe specs exist and pass in interpreter mode for editor (pair create/update, multi-css), builder (std form, dyn form < 4 KB parts, merge decision), and verify (pass + fail cases).
- AC-9: `bin/simple build lint` and `simple check` pass on all new files; no inheritance; statement-form exports.

## Scope Exclusions
- GUI/TUI interactive editing surfaces (later phase; only the CSS-degradation notes in the guide cover TUI now).
- JS/behavior in HTML; only structure + style.
- Rendering-pipeline changes (web_render lane is reused, not modified).

## Phase
dev-done

## Log
- dev: Created state file with 9 acceptance criteria (type: feature)
