import {
  EXPORT_SDOCTEST_COMMAND_ID,
  SIMPLE_EXPORT_COMM_TARGET,
  deriveSdoctestOutPath,
  registerExportSdoctestCommand,
  requestSdoctestExport,
} from "../src/export";

/** Minimal fake IComm: captures the opened data and lets the test drive
 * onMsg/onClose the way a real kernel round trip would. */
function makeFakeComm(targetName: string) {
  const comm: any = {
    commId: "comm-1",
    targetName,
    onMsg: undefined,
    onClose: undefined,
    openedWith: undefined,
    disposed: false,
    open: jest.fn((data: unknown) => {
      comm.openedWith = data;
      return { done: Promise.resolve() };
    }),
    dispose: jest.fn(() => {
      comm.disposed = true;
    }),
  };
  return comm;
}

function makeFakeKernel(comm: any) {
  return {
    createComm: jest.fn((_target: string) => comm),
  } as any;
}

describe("deriveSdoctestOutPath", () => {
  it("replaces .ipynb with .sdoctest.md", () => {
    expect(deriveSdoctestOutPath("notebooks/hello.ipynb")).toBe("notebooks/hello.sdoctest.md");
  });

  it("replaces .snb.sdn with .sdoctest.md", () => {
    expect(deriveSdoctestOutPath("notebooks/hello.snb.sdn")).toBe("notebooks/hello.sdoctest.md");
  });

  it("falls back to appending .sdoctest.md for an unknown extension", () => {
    expect(deriveSdoctestOutPath("notebooks/hello.txt")).toBe("notebooks/hello.txt.sdoctest.md");
  });
});

describe("requestSdoctestExport (comm round trip)", () => {
  it("opens a simple_export comm with an export_sdoctest request and resolves on the reply", async () => {
    const comm = makeFakeComm(SIMPLE_EXPORT_COMM_TARGET);
    const kernel = makeFakeKernel(comm);

    const pending = requestSdoctestExport(kernel, "nb/hello.ipynb", "nb/hello.sdoctest.md");

    expect(kernel.createComm).toHaveBeenCalledWith(SIMPLE_EXPORT_COMM_TARGET);
    expect(comm.openedWith).toEqual({
      action: "export_sdoctest",
      in_path: "nb/hello.ipynb",
      out_path: "nb/hello.sdoctest.md",
    });

    comm.onMsg({ content: { data: { status: "ok", out_path: "nb/hello.sdoctest.md" } } } as any);

    await expect(pending).resolves.toEqual({ status: "ok", out_path: "nb/hello.sdoctest.md" });
    expect(comm.disposed).toBe(true);
  });

  it("resolves with an error result when the kernel replies with status:error", async () => {
    const comm = makeFakeComm(SIMPLE_EXPORT_COMM_TARGET);
    const kernel = makeFakeKernel(comm);

    const pending = requestSdoctestExport(kernel, "nb/hello.ipynb", "nb/hello.sdoctest.md");
    comm.onMsg({ content: { data: { status: "error", error: "boom" } } } as any);

    await expect(pending).resolves.toEqual({ status: "error", error: "boom" });
  });

  it("rejects if the comm closes before any reply arrives", async () => {
    const comm = makeFakeComm(SIMPLE_EXPORT_COMM_TARGET);
    const kernel = makeFakeKernel(comm);

    const pending = requestSdoctestExport(kernel, "nb/hello.ipynb", "nb/hello.sdoctest.md");
    comm.onClose({} as any);

    await expect(pending).rejects.toThrow("simple_export comm closed before a reply arrived");
  });
});

describe("registerExportSdoctestCommand", () => {
  function makeCommands() {
    const registered: Record<string, any> = {};
    const commands = {
      addCommand: jest.fn((id: string, options: Record<string, unknown>) => {
        registered[id] = options;
        return { id };
      }),
    };
    return { commands, registered };
  }

  it("registers the export command with the expected id and label", () => {
    const { commands, registered } = makeCommands();
    const notebooks: any = { currentWidget: null };

    registerExportSdoctestCommand(commands, notebooks);

    expect(commands.addCommand).toHaveBeenCalledTimes(1);
    expect(registered[EXPORT_SDOCTEST_COMMAND_ID]).toBeDefined();
    expect(registered[EXPORT_SDOCTEST_COMMAND_ID].label).toBe("Export notebook as SDoctest");
  });

  it("isEnabled reflects whether there is a current notebook", () => {
    const { commands, registered } = makeCommands();
    const notebooks: any = { currentWidget: null };
    registerExportSdoctestCommand(commands, notebooks);

    expect(registered[EXPORT_SDOCTEST_COMMAND_ID].isEnabled()).toBe(false);
    notebooks.currentWidget = {};
    expect(registered[EXPORT_SDOCTEST_COMMAND_ID].isEnabled()).toBe(true);
  });

  it("execute() drives the comm round trip against the current notebook's kernel and path", async () => {
    const { commands, registered } = makeCommands();
    const comm = makeFakeComm(SIMPLE_EXPORT_COMM_TARGET);
    const kernel = makeFakeKernel(comm);
    const panel: any = {
      context: { path: "nb/hello.ipynb" },
      sessionContext: { session: { kernel } },
    };
    const notebooks: any = { currentWidget: panel };

    registerExportSdoctestCommand(commands, notebooks);
    const pending = registered[EXPORT_SDOCTEST_COMMAND_ID].execute();

    expect(comm.openedWith).toEqual({
      action: "export_sdoctest",
      in_path: "nb/hello.ipynb",
      out_path: "nb/hello.sdoctest.md",
    });
    comm.onMsg({ content: { data: { status: "ok", out_path: "nb/hello.sdoctest.md" } } } as any);

    await expect(pending).resolves.toEqual({ status: "ok", out_path: "nb/hello.sdoctest.md" });
  });

  it("execute() returns an error result when there is no active notebook", async () => {
    const { commands, registered } = makeCommands();
    const notebooks: any = { currentWidget: null };
    registerExportSdoctestCommand(commands, notebooks);

    await expect(registered[EXPORT_SDOCTEST_COMMAND_ID].execute()).resolves.toEqual({
      status: "error",
      error: "no active notebook",
    });
  });

  it("execute() returns an error result when the notebook has no running kernel", async () => {
    const { commands, registered } = makeCommands();
    const panel: any = {
      context: { path: "nb/hello.ipynb" },
      sessionContext: { session: { kernel: null } },
    };
    const notebooks: any = { currentWidget: panel };
    registerExportSdoctestCommand(commands, notebooks);

    await expect(registered[EXPORT_SDOCTEST_COMMAND_ID].execute()).resolves.toEqual({
      status: "error",
      error: "notebook has no running kernel",
    });
  });
});
