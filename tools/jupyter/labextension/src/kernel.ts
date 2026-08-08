// Kernel <-> language mapping for the Simple JupyterLab extension (X2).
//
// The Simple kernel (tools/jupyter/kernel_wrapper.py, kernelspec name
// "simple", declared in tools/jupyter/kernel.json) speaks the Jupyter wire
// protocol but its kernel_info_reply does not populate `language_info`.
// JupyterLab's notebook widget only recomputes a cell's CodeMirror mimetype
// (`Notebook._updateMimetype`, @jupyterlab/notebook) by reading the
// *notebook model's* `language_info` metadata -- which, absent a kernel that
// reports it, is never set, so cells silently fall back to plain text
// instead of the CM6 grammar registered in language.ts.
//
// We close that gap explicitly here: whenever a notebook's kernel spec
// resolves to the "simple" language (kernel.json's `language` field), we
// stamp the notebook model's `language_info` metadata ourselves. That is the
// same piece of notebook metadata a well-behaved kernel would have supplied,
// so it flows through JupyterLab's existing, unmodified mimetype pipeline
// rather than us reimplementing per-cell mimetype assignment.
import type { INotebookTracker, NotebookPanel } from "@jupyterlab/notebook";
import { SIMPLE_FILE_EXTENSIONS, SIMPLE_LANGUAGE_NAME, SIMPLE_MIME_TYPE } from "./language";

/** kernelspec `language` (as declared in kernel.json) -> the `language_info`
 * block JupyterLab expects a kernel_info_reply to carry for that language. */
export const KERNEL_LANGUAGE_INFO: Record<string, Record<string, unknown>> = {
  [SIMPLE_LANGUAGE_NAME]: {
    name: SIMPLE_LANGUAGE_NAME,
    mimetype: SIMPLE_MIME_TYPE,
    file_extension: SIMPLE_FILE_EXTENSIONS[0],
  },
};

/** Look up the `language_info` block for a given kernelspec language, or
 * `undefined` if this extension has no mapping for it. Exported standalone
 * so the mapping table is unit-testable without a live JupyterFrontEnd. */
export function languageInfoForKernelLanguage(
  kernelLanguage: string | undefined
): Record<string, unknown> | undefined {
  if (!kernelLanguage) {
    return undefined;
  }
  return KERNEL_LANGUAGE_INFO[kernelLanguage];
}

/** Stamp `panel`'s notebook model with the `language_info` metadata implied
 * by its current kernel spec's `language`, if we have a mapping for it. */
export async function applyKernelLanguageMapping(panel: NotebookPanel): Promise<void> {
  const spec = await panel.sessionContext.session?.kernel?.spec;
  const info = languageInfoForKernelLanguage(spec?.language);
  if (info) {
    panel.content.model?.setMetadata("language_info", info);
  }
}

/** Wire a notebook tracker so every notebook backed by a kernel this
 * extension knows about (currently just "simple") gets its `language_info`
 * metadata -- and therefore its cells' CodeMirror mimetype -- set as soon as
 * the kernel connects, and again on every kernel change (e.g. restart with a
 * different kernel). */
export function wireKernelLanguageMapping(notebooks: INotebookTracker): void {
  notebooks.widgetAdded.connect((_sender, panel: NotebookPanel) => {
    // Apply immediately: a restored session may add the panel *after* its
    // kernel already connected, in which case `kernelChanged` never fires.
    void applyKernelLanguageMapping(panel);
    panel.sessionContext.kernelChanged.connect(() => {
      void applyKernelLanguageMapping(panel);
    });
  });
}
