// SDoctest export command (X4).
//
// Adds a command-palette entry, "Export notebook as SDoctest", that asks the
// running Simple kernel to run the shared L1 exporter
// (`src/app/simple_lab/export_sdoctest.spl`, functions `export_notebook_file`
// / `nb_to_sdoctest_markdown`) over the current notebook file and write
// `<name>.sdoctest.md` next to it (design doc
// doc/05_design/app/tools/notebook_lanes_architecture.md §7.3/§7.4).
//
// The exporter itself only runs kernel-side (it needs to read/parse the
// notebook file and shells out to nothing the browser can do), so this
// module's job is entirely the request/reply round trip over a NEW comm
// target, `simple_export` -- distinct from X3/P1's `simple_lane` comm, which
// only carries lane list/mode traffic. The kernel-side handler for this
// target is `src/app/jupyter_kernel/main.spl` `handle_comm_open` /
// `handle_comm_msg` (branches on `target_name`, same dispatch P1 already
// established for `simple_lane` -- this is just another branch, not a
// replacement).
import type { Kernel, KernelMessage } from "@jupyterlab/services";
import type { NotebookPanel } from "@jupyterlab/notebook";
import type { CommandRegistry } from "@lumino/commands";

export const SIMPLE_EXPORT_COMM_TARGET = "simple_export";
export const EXPORT_SDOCTEST_COMMAND_ID = "simple-lang:export-sdoctest";

export interface ExportSdoctestResult {
  status: "ok" | "error";
  out_path?: string;
  error?: string;
}

/** `foo/bar.ipynb` -> `foo/bar.sdoctest.md` (or `foo/bar.snb.sdn` ->
 * `foo/bar.sdoctest.md`), matching L1's `export_notebook_file` output
 * convention (design §7.3: "saves `<name>.sdoctest.md`"). */
export function deriveSdoctestOutPath(notebookPath: string): string {
  if (notebookPath.endsWith(".ipynb")) {
    return `${notebookPath.slice(0, -".ipynb".length)}.sdoctest.md`;
  }
  if (notebookPath.endsWith(".snb.sdn")) {
    return `${notebookPath.slice(0, -".snb.sdn".length)}.sdoctest.md`;
  }
  return `${notebookPath}.sdoctest.md`;
}

/** Open a `simple_export` comm on `kernel`, send an export request for
 * `inPath` -> `outPath`, and resolve with the kernel's reply. Rejects if the
 * kernel never replies (comm closed without a `comm_msg` reply). */
export function requestSdoctestExport(
  kernel: Kernel.IKernelConnection,
  inPath: string,
  outPath: string
): Promise<ExportSdoctestResult> {
  return new Promise<ExportSdoctestResult>((resolve, reject) => {
    const comm = kernel.createComm(SIMPLE_EXPORT_COMM_TARGET);
    let settled = false;

    comm.onMsg = (msg: KernelMessage.ICommMsgMsg) => {
      if (settled) {
        return;
      }
      settled = true;
      const data = msg.content.data as Record<string, unknown>;
      const status = data.status === "ok" ? "ok" : "error";
      const result: ExportSdoctestResult = { status };
      if (typeof data.out_path === "string") {
        result.out_path = data.out_path;
      }
      if (typeof data.error === "string") {
        result.error = data.error;
      }
      comm.dispose();
      resolve(result);
    };
    comm.onClose = () => {
      if (settled) {
        return;
      }
      settled = true;
      reject(new Error("simple_export comm closed before a reply arrived"));
    };

    comm.open({
      action: "export_sdoctest",
      in_path: inPath,
      out_path: outPath,
    });
  });
}

/** Register the "Export notebook as SDoctest" command against `commands`,
 * bound to the tracker's current notebook. Returns the disposable command
 * registration so callers (index.ts) can add it to a palette. */
export function registerExportSdoctestCommand(
  commands: CommandRegistry,
  notebooks: { currentWidget: NotebookPanel | null }
): ReturnType<CommandRegistry["addCommand"]> {
  return commands.addCommand(EXPORT_SDOCTEST_COMMAND_ID, {
    label: "Export notebook as SDoctest",
    isEnabled: () => notebooks.currentWidget !== null,
    execute: async () => {
      const panel = notebooks.currentWidget;
      if (!panel) {
        return { status: "error", error: "no active notebook" } as ExportSdoctestResult;
      }
      const kernel = panel.sessionContext.session?.kernel;
      if (!kernel) {
        return { status: "error", error: "notebook has no running kernel" } as ExportSdoctestResult;
      }
      const inPath = panel.context.path;
      const outPath = deriveSdoctestOutPath(inPath);
      return requestSdoctestExport(kernel, inPath, outPath);
    },
  });
}
