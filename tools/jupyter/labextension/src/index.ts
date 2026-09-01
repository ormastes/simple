// JupyterLab extension entry point for the Simple language.
//
// X1 landed the CodeMirror 6 grammar plugin (registers ./language.ts as a
// JupyterLab editor language for `.spl` files / `text/x-simple` cells).
// X2 (this file) adds:
//   - kernel/language mapping (./kernel.ts): stamps `language_info` on any
//     notebook backed by the "simple" kernel, since that kernel's
//     kernel_info_reply doesn't supply it itself.
//   - a status-bar "execution mode/lane" item (./status.ts) fed live data by
//     the lane picker (./lane.ts, X3).
//   - LSP wiring: see ../lsp_server_spec.json + install.shs. JupyterLab's
//     bundled `@jupyterlab/lsp` only *consumes* language servers that the
//     `jupyter-lsp` Python server extension spawns from its
//     `LanguageServerManager.language_servers` config; a frontend plugin has
//     no API to register a new server (TLanguageServerId is a closed union
//     over the known community servers), so the spec lives as data
//     (lsp_server_spec.json) installed into the Jupyter config search path
//     rather than as TypeScript here.
//   - a toolbar lane picker (./lane.ts, X3) bound to the `simple_lane` kernel
//     comm (P1, src/app/jupyter_kernel/main.spl).
//
// Math outputs (X3, design doc §6): `text/latex` `display_data` needs NO
// extension code here. @jupyterlab/rendermime's `defaultRendererFactories`
// already includes a `text/latex` factory (node_modules/@jupyterlab/
// rendermime/lib/factories.js:29-33,86) whose `RenderedLatex` widget calls
// `latexTypesetter.typeset(host)` when the app provides an `ILatexTypesetter`
// (renderers.js:62) -- and every notebook panel uses the app-wide
// `RenderMimeRegistry`, which this extension never overrides or wraps. So any
// `text/latex` output the kernel emits is already routed to MathJax by core
// JupyterLab. What's actually missing is upstream of this package on both
// ends: (1) P1 deliberately does not emit `display_data` for math blocks yet
// (no kernel-side change was made here -- out of X3's scope), and (2) the
// `ILatexTypesetter` token is provided by `@jupyterlab/mathjax-extension`,
// part of the standard `jupyterlab` distribution (`pip install jupyterlab`)
// but not a dependency of this package nor present in this dev sandbox
// (verified: no mathjax-extension anywhere under this checkout) -- without it
// `RenderedLatex` still renders (falls back to raw source, per the `if
// (shouldTypeset && latexTypesetter)` guard) rather than erroring, so a
// deployed JupyterLab without MathJax degrades gracefully but silently.
import type { JupyterFrontEnd, JupyterFrontEndPlugin } from "@jupyterlab/application";
import { ICommandPalette } from "@jupyterlab/apputils";
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
import { EXPORT_SDOCTEST_COMMAND_ID, registerExportSdoctestCommand } from "./export";
import { wireLanePicker } from "./lane";

export { simpleLanguage, SIMPLE_LANGUAGE_NAME, SIMPLE_MIME_TYPE, SIMPLE_FILE_EXTENSIONS };
export { wireKernelLanguageMapping, languageInfoForKernelLanguage } from "./kernel";
export { ModeStatusWidget, DEFAULT_MODE, MODE_STATUS_ITEM_ID } from "./status";
export {
  SIMPLE_EXPORT_COMM_TARGET,
  EXPORT_SDOCTEST_COMMAND_ID,
  deriveSdoctestOutPath,
  requestSdoctestExport,
  registerExportSdoctestCommand,
} from "./export";
export {
  wireLanePicker,
  parseLaneStatus,
  LanePickerWidget,
  LanePickerController,
  SIMPLE_LANE_COMM_TARGET,
} from "./lane";

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

// Shared between modeStatusPlugin (registers it in the status bar) and
// lanePickerPlugin (feeds it live mode updates from the `simple_lane` comm)
// -- there is exactly one status item for whichever notebook is active, so
// both plugins need the same widget instance rather than each owning one.
const modeStatusWidget = new ModeStatusWidget(DEFAULT_MODE);

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
    statusBar.registerStatusItem(MODE_STATUS_ITEM_ID, {
      item: modeStatusWidget,
      align: "left",
      rank: 500,
      isActive: () => (notebooks ? notebooks.currentWidget !== null : true),
    });
  },
};

const lanePickerPlugin: JupyterFrontEndPlugin<void> = {
  id: "@simple-lang/jupyterlab-simple:lane-picker",
  description: "Toolbar lane picker bound to the 'simple_lane' kernel comm",
  autoStart: true,
  requires: [INotebookTracker],
  activate: (_app: JupyterFrontEnd, notebooks: INotebookTracker): void => {
    wireLanePicker(notebooks, modeStatusWidget);
  },
};

const exportSdoctestPlugin: JupyterFrontEndPlugin<void> = {
  id: "@simple-lang/jupyterlab-simple:export-sdoctest",
  description: "Command-palette entry to export the current notebook as an SDoctest markdown file",
  autoStart: true,
  requires: [INotebookTracker],
  optional: [ICommandPalette],
  activate: (
    app: JupyterFrontEnd,
    notebooks: INotebookTracker,
    palette: ICommandPalette | null
  ): void => {
    registerExportSdoctestCommand(app.commands, notebooks);
    if (palette) {
      palette.addItem({ command: EXPORT_SDOCTEST_COMMAND_ID, category: "Simple" });
    }
  },
};

const plugins: JupyterFrontEndPlugin<void>[] = [
  languagePlugin,
  kernelMappingPlugin,
  modeStatusPlugin,
  lanePickerPlugin,
  exportSdoctestPlugin,
];

export default plugins;
