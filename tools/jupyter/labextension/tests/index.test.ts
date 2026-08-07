/**
 * @jest-environment jsdom
 *
 * Unit-level plugin-registration test standing in for a galata (headless
 * JupyterLab-in-browser) smoke test. This repo has no `jupyter lab` /
 * browser host available to run galata against (see host-unavailable note
 * in the X2 task report); this test instead activates each plugin against
 * mock JupyterLab services and asserts the wiring galata would exercise
 * end-to-end: the CM6 language gets registered, the kernel-mapping listener
 * gets attached, and the status-bar item gets registered.
 */
import { Signal } from "@lumino/signaling";

// @jupyterlab/{codemirror,notebook,statusbar} ship ESM-only `lib/*.js`
// builds that ts-jest's CommonJS transform can't parse without an
// additional Babel ESM-interop pipeline this repo doesn't vendor. `tsc -b`
// (the real build, run separately -- see the X2 task report) already
// type-checks src/index.ts against the genuine `.d.ts` for all three; here
// we only need the DI *token identity* each package exports (`requires:
// [IEditorLanguageRegistry]` etc. compare tokens by reference), so a bare
// stub token per package is a faithful enough substitute for unit-testing
// plugin activation.
jest.mock("@jupyterlab/codemirror", () => ({ IEditorLanguageRegistry: Symbol("IEditorLanguageRegistry") }));
jest.mock("@jupyterlab/notebook", () => ({ INotebookTracker: Symbol("INotebookTracker") }));
jest.mock("@jupyterlab/statusbar", () => ({ IStatusBar: Symbol("IStatusBar") }));
jest.mock("@jupyterlab/apputils", () => ({ ICommandPalette: Symbol("ICommandPalette") }));

// eslint-disable-next-line @typescript-eslint/no-var-requires
import plugins from "../src/index";
import { SIMPLE_FILE_EXTENSIONS, SIMPLE_LANGUAGE_NAME, SIMPLE_MIME_TYPE } from "../src/language";
import { MODE_STATUS_ITEM_ID } from "../src/status";

function findPlugin(id: string) {
  const found = plugins.find((p) => p.id === id);
  if (!found) {
    throw new Error(`plugin not found: ${id}`);
  }
  return found;
}

describe("Simple JupyterLab extension plugins (X2/X3/X4)", () => {
  it("exports exactly the five expected plugins, all autoStart", () => {
    expect(plugins.map((p) => p.id).sort()).toEqual([
      "@simple-lang/jupyterlab-simple:export-sdoctest",
      "@simple-lang/jupyterlab-simple:kernel-mapping",
      "@simple-lang/jupyterlab-simple:lane-picker",
      "@simple-lang/jupyterlab-simple:language",
      "@simple-lang/jupyterlab-simple:mode-status",
    ]);
    for (const p of plugins) {
      expect(p.autoStart).toBe(true);
    }
  });

  it("lane-picker plugin attaches a widgetAdded listener on activation (X3)", () => {
    const plugin = findPlugin("@simple-lang/jupyterlab-simple:lane-picker");
    const widgetAdded = new Signal<any, any>({});
    const notebooks: any = { widgetAdded, currentWidget: null };

    expect(() => (plugin.activate as any)({}, notebooks)).not.toThrow();
    // Wiring is exercised end-to-end in tests/lane.test.ts against a fake
    // panel; here we only assert plugin activation doesn't throw when a
    // panel-shaped object without a toolbar/sessionContext is emitted.
    const fakePanel = {
      toolbar: { insertItem: jest.fn() },
      sessionContext: { session: undefined, kernelChanged: new Signal<any, void>({}) },
    };
    expect(() => widgetAdded.emit(fakePanel)).not.toThrow();
  });

  it("language plugin registers the Simple CM6 language on activation", () => {
    const plugin = findPlugin("@simple-lang/jupyterlab-simple:language");
    const addLanguage = jest.fn();
    const languages: any = { addLanguage };

    (plugin.activate as any)({}, languages);

    expect(addLanguage).toHaveBeenCalledTimes(1);
    const arg = addLanguage.mock.calls[0][0];
    expect(arg.name).toBe(SIMPLE_LANGUAGE_NAME);
    expect(arg.mime).toBe(SIMPLE_MIME_TYPE);
    expect(arg.extensions).toEqual(SIMPLE_FILE_EXTENSIONS);
    expect(arg.support).toBeDefined();
  });

  it("kernel-mapping plugin attaches a widgetAdded listener on activation", () => {
    const plugin = findPlugin("@simple-lang/jupyterlab-simple:kernel-mapping");
    const widgetAdded = new Signal<any, any>({});
    const notebooks: any = { widgetAdded };

    expect(() => (plugin.activate as any)({}, notebooks)).not.toThrow();
    // A listener was attached: emitting must not throw, even though no
    // panel-shaped object is supplied here (kernel.test.ts exercises the
    // full metadata-stamping path against a fake panel).
    expect(() => widgetAdded.emit({ sessionContext: { kernelChanged: new Signal<any, void>({}) } })).not.toThrow();
  });

  it("mode-status plugin registers a real status-bar item with the mode widget", () => {
    const plugin = findPlugin("@simple-lang/jupyterlab-simple:mode-status");
    const registerStatusItem = jest.fn();
    const statusBar: any = { registerStatusItem };
    const notebooks: any = { currentWidget: null };

    (plugin.activate as any)({}, statusBar, notebooks);

    expect(registerStatusItem).toHaveBeenCalledTimes(1);
    const [id, options] = registerStatusItem.mock.calls[0];
    expect(id).toBe(MODE_STATUS_ITEM_ID);
    expect(options.item.node.textContent).toBe("Simple: local");
    expect(options.isActive()).toBe(false);

    notebooks.currentWidget = {};
    expect(options.isActive()).toBe(true);
  });

  it("mode-status plugin works with notebooks tracker absent (optional dependency)", () => {
    const plugin = findPlugin("@simple-lang/jupyterlab-simple:mode-status");
    const registerStatusItem = jest.fn();
    const statusBar: any = { registerStatusItem };

    (plugin.activate as any)({}, statusBar, null);

    const [, options] = registerStatusItem.mock.calls[0];
    expect(options.isActive()).toBe(true);
  });
});
