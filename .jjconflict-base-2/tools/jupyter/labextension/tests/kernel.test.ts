import { Signal } from "@lumino/signaling";
import {
  KERNEL_LANGUAGE_INFO,
  applyKernelLanguageMapping,
  languageInfoForKernelLanguage,
  wireKernelLanguageMapping,
} from "../src/kernel";
import { SIMPLE_FILE_EXTENSIONS, SIMPLE_LANGUAGE_NAME, SIMPLE_MIME_TYPE } from "../src/language";

/** Minimal fakes standing in for the JupyterLab objects kernel.ts touches,
 * built with real @lumino/signaling Signals so `.connect` callbacks fire
 * exactly as they would against a live INotebookTracker/NotebookPanel. */
function makeFakePanel(kernelLanguage: string | undefined) {
  const setMetadata = jest.fn();
  const panel: any = {
    content: { model: { setMetadata } },
    sessionContext: {
      kernelChanged: new Signal<any, void>({}),
      session: {
        kernel: {
          spec: Promise.resolve(kernelLanguage ? { language: kernelLanguage } : undefined),
        },
      },
    },
  };
  return { panel, setMetadata };
}

describe("kernel language mapping (X2)", () => {
  it("maps the 'simple' kernelspec language to the registered mimetype/extension", () => {
    expect(KERNEL_LANGUAGE_INFO[SIMPLE_LANGUAGE_NAME]).toEqual({
      name: SIMPLE_LANGUAGE_NAME,
      mimetype: SIMPLE_MIME_TYPE,
      file_extension: SIMPLE_FILE_EXTENSIONS[0],
    });
  });

  it("languageInfoForKernelLanguage resolves 'simple' and rejects unknown/undefined languages", () => {
    expect(languageInfoForKernelLanguage(SIMPLE_LANGUAGE_NAME)).toBeDefined();
    expect(languageInfoForKernelLanguage("python")).toBeUndefined();
    expect(languageInfoForKernelLanguage(undefined)).toBeUndefined();
  });

  it("applyKernelLanguageMapping stamps notebook model metadata for a 'simple' kernel", async () => {
    const { panel, setMetadata } = makeFakePanel(SIMPLE_LANGUAGE_NAME);
    await applyKernelLanguageMapping(panel);
    expect(setMetadata).toHaveBeenCalledWith("language_info", KERNEL_LANGUAGE_INFO[SIMPLE_LANGUAGE_NAME]);
  });

  it("applyKernelLanguageMapping is a no-op for a kernel language we don't map", async () => {
    const { panel, setMetadata } = makeFakePanel("python");
    await applyKernelLanguageMapping(panel);
    expect(setMetadata).not.toHaveBeenCalled();
  });

  it("wireKernelLanguageMapping applies the mapping immediately on widgetAdded (restored-session case, no kernelChanged fires)", async () => {
    const { panel, setMetadata } = makeFakePanel(SIMPLE_LANGUAGE_NAME);
    const widgetAdded = new Signal<any, any>({});
    const notebooks: any = { widgetAdded };

    wireKernelLanguageMapping(notebooks);
    widgetAdded.emit(panel);

    // applyKernelLanguageMapping awaits a microtask (kernel.spec promise).
    await Promise.resolve();
    await Promise.resolve();

    expect(setMetadata).toHaveBeenCalledWith("language_info", KERNEL_LANGUAGE_INFO[SIMPLE_LANGUAGE_NAME]);
  });

  it("wireKernelLanguageMapping also re-applies the mapping on kernelChanged (e.g. kernel restart)", async () => {
    const { panel, setMetadata } = makeFakePanel(SIMPLE_LANGUAGE_NAME);
    const widgetAdded = new Signal<any, any>({});
    const notebooks: any = { widgetAdded };

    wireKernelLanguageMapping(notebooks);
    widgetAdded.emit(panel);
    await Promise.resolve();
    await Promise.resolve();
    setMetadata.mockClear();

    panel.sessionContext.kernelChanged.emit(undefined);
    await Promise.resolve();
    await Promise.resolve();

    expect(setMetadata).toHaveBeenCalledWith("language_info", KERNEL_LANGUAGE_INFO[SIMPLE_LANGUAGE_NAME]);
  });
});
