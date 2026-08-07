// JupyterLab extension entry point for the Simple language.
//
// X1 landed the CodeMirror 6 grammar plugin (registers ./language.ts as a
// JupyterLab editor language for `.spl` files / `text/x-simple` cells).
// X2 (this file) adds:
//   - kernel/language mapping (./kernel.ts): stamps `language_info` on any
//     notebook backed by the "simple" kernel, since that kernel's
//     kernel_info_reply doesn't supply it itself.
//   - a status-bar "execution mode/lane" item (./status.ts), a placeholder
//     until X3 wires it to the real lane-picker comm.
//   - LSP wiring: see ../lsp_server_spec.json + install.shs. JupyterLab's
//     bundled `@jupyterlab/lsp` only *consumes* language servers that the
//     `jupyter-lsp` Python server extension spawns from its
//     `LanguageServerManager.language_servers` config; a frontend plugin has
//     no API to register a new server (TLanguageServerId is a closed union
//     over the known community servers), so the spec lives as data
//     (lsp_server_spec.json) installed into the Jupyter config search path
//     rather than as TypeScript here.
// Lane picker UI and math outputs are X3 (deps: X2, P1).
import type { JupyterFrontEnd, JupyterFrontEndPlugin } from "@jupyterlab/application";
import { IEditorLanguageRegistry } from "@jupyterlab/codemirror";
import { INotebookTracker } from "@jupyterlab/notebook";
import { IStatusBar } from "@jupyterlab/statusbar";
import {
  SIMPLE_FILE_EXTENSIONS,
  SIMPLE_LANGUAGE_NAME,
  SIMPLE_MIME_TYPE,
  simpleLanguage,
} from "./language";
import { wireKernelLanguageMapping } from "./kernel";
import { DEFAULT_MODE, ModeStatusWidget, MODE_STATUS_ITEM_ID } from "./status";

export { simpleLanguage, SIMPLE_LANGUAGE_NAME, SIMPLE_MIME_TYPE, SIMPLE_FILE_EXTENSIONS };
export { wireKernelLanguageMapping, languageInfoForKernelLanguage } from "./kernel";
export { ModeStatusWidget, DEFAULT_MODE, MODE_STATUS_ITEM_ID } from "./status";

const languagePlugin: JupyterFrontEndPlugin<void> = {
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

const kernelMappingPlugin: JupyterFrontEndPlugin<void> = {
  id: "@simple-lang/jupyterlab-simple:kernel-mapping",
  description: "Maps the 'simple' kernelspec language to the registered CM6 grammar",
  autoStart: true,
  requires: [INotebookTracker],
  activate: (_app: JupyterFrontEnd, notebooks: INotebookTracker): void => {
    wireKernelLanguageMapping(notebooks);
  },
};

const modeStatusPlugin: JupyterFrontEndPlugin<void> = {
  id: "@simple-lang/jupyterlab-simple:mode-status",
  description: "Status-bar item showing the current notebook's execution mode/lane",
  autoStart: true,
  requires: [IStatusBar],
  optional: [INotebookTracker],
  activate: (
    _app: JupyterFrontEnd,
    statusBar: IStatusBar,
    notebooks: INotebookTracker | null
  ): void => {
    const widget = new ModeStatusWidget(DEFAULT_MODE);
    statusBar.registerStatusItem(MODE_STATUS_ITEM_ID, {
      item: widget,
      align: "left",
      rank: 500,
      isActive: () => (notebooks ? notebooks.currentWidget !== null : true),
    });
  },
};

const plugins: JupyterFrontEndPlugin<void>[] = [
  languagePlugin,
  kernelMappingPlugin,
  modeStatusPlugin,
];

export default plugins;
