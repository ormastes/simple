// JupyterLab extension entry point for the Simple language.
//
// X1 scope: register the generated CodeMirror 6 grammar (./language.ts) as a
// JupyterLab editor language for `.spl` files / `text/x-simple` cells.
// Kernel mapping, LSP wiring, lane picker, and math outputs are follow-on
// tasks (X2/X3) in doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md.
import type { JupyterFrontEnd, JupyterFrontEndPlugin } from "@jupyterlab/application";
import { IEditorLanguageRegistry } from "@jupyterlab/codemirror";
import {
  SIMPLE_FILE_EXTENSIONS,
  SIMPLE_LANGUAGE_NAME,
  SIMPLE_MIME_TYPE,
  simpleLanguage,
} from "./language";

export { simpleLanguage, SIMPLE_LANGUAGE_NAME, SIMPLE_MIME_TYPE, SIMPLE_FILE_EXTENSIONS };

const plugin: JupyterFrontEndPlugin<void> = {
  id: "@simple-lang/jupyterlab-simple:language",
  description: "CodeMirror 6 syntax highlighting for the Simple language (.spl)",
  autoStart: true,
  requires: [IEditorLanguageRegistry],
  activate: (_app: JupyterFrontEnd, languages: IEditorLanguageRegistry): void => {
    languages.addLanguage({
      name: SIMPLE_LANGUAGE_NAME,
      mime: SIMPLE_MIME_TYPE,
      extensions: SIMPLE_FILE_EXTENSIONS,
      support: simpleLanguage(),
    });
  },
};

export default plugin;
