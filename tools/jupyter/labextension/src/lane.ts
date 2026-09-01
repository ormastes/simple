// Lane picker (X3): toolbar dropdown driven by the `simple_lane` kernel comm.
//
// Wire contract (P1, `src/app/jupyter_kernel/main.spl`
// handle_comm_open/handle_comm_msg/lane_status_content`): `comm_open` gets an
// immediate `comm_msg` reply with `{"mode": "<current>", "lanes": [...]}`;
// sending `{"set_mode": "<name>"}` over the comm changes the session's
// default mode (server-side `%mode`) and triggers another `comm_msg` reply
// with the updated status. That reply is the *only* thing this module trusts
// -- `selectLane` does not optimistically update the dropdown, so the picker
// always reflects server-confirmed state, never a guess.
//
// Design doc §6 describes a richer picker ("shows lanes with ✓/skip/blocked
// and the reason on hover"); P1's wire shape has no per-lane status yet
// (`lanes` is a flat string array, currently always `["interpreter"]`), so
// that part of §6 is not implementable against the current kernel and is not
// attempted here -- see the X3 task report for the filed follow-up.
import { Widget } from "@lumino/widgets";
import type { NotebookPanel, INotebookTracker } from "@jupyterlab/notebook";
import { ModeStatusWidget } from "./status";

export const SIMPLE_LANE_COMM_TARGET = "simple_lane";

export interface LaneStatus {
  mode: string;
  lanes: string[];
}

/** Minimal comm-channel shape this module depends on -- a structural subset
 * of `@jupyterlab/services`' `IComm`, kept local so unit tests can supply a
 * plain mock without pulling in a live kernel connection (that package's
 * ESM-only build can't be imported under this repo's ts-jest transform --
 * see tests/index.test.ts's note on the same issue for @jupyterlab/*). */
export interface ILaneComm {
  open(data?: unknown): unknown;
  send(data: unknown): unknown;
  onMsg: (msg: { content: { data: unknown } }) => void;
}

/** Parse a `simple_lane` comm payload (the `data` field of a comm_open reply
 * or a comm_msg push). Returns undefined for anything that doesn't match the
 * `{mode: string, lanes: string[]}` shape P1 sends, rather than throwing --
 * a malformed or foreign payload should leave the picker showing its
 * last-known-good state, not crash the extension. */
export function parseLaneStatus(data: unknown): LaneStatus | undefined {
  if (typeof data !== "object" || data === null) {
    return undefined;
  }
  const obj = data as Record<string, unknown>;
  const mode = obj.mode;
  const lanes = obj.lanes;
  if (typeof mode !== "string" || !Array.isArray(lanes)) {
    return undefined;
  }
  if (!lanes.every((lane) => typeof lane === "string")) {
    return undefined;
  }
  return { mode, lanes: lanes as string[] };
}

/** Toolbar dropdown: a plain `<select>` wrapped in a Lumino Widget, matching
 * status.ts's choice to avoid a React dependency. */
export class LanePickerWidget extends Widget {
  constructor(onLaneSelected: (lane: string) => void) {
    const select = document.createElement("select");
    select.classList.add("simple-lane-picker");
    super({ node: select });
    this.addClass("simple-lane-picker-widget");
    this.node.title = "Simple notebook execution lane";
    this._select = select;
    this._select.addEventListener("change", () => {
      onLaneSelected(this._select.value);
    });
  }

  /** Replace the dropdown's options with `lanes`, selecting `mode`. If the
   * server's current mode isn't in the lane list, it's prepended as an extra
   * option -- the notebook's actual state must never be silently dropped
   * from what the picker can display. */
  setLanes(lanes: string[], mode: string): void {
    const values = lanes.includes(mode) ? lanes : [mode, ...lanes];
    this._select.innerHTML = "";
    for (const lane of values) {
      const option = document.createElement("option");
      option.value = lane;
      option.textContent = lane;
      this._select.appendChild(option);
    }
    this._select.value = mode;
  }

  get value(): string {
    return this._select.value;
  }

  private _select: HTMLSelectElement;
}

/** Wires one notebook's `LanePickerWidget` to its `simple_lane` comm and to
 * the shared status-bar `ModeStatusWidget`. Kept independent of any live
 * JupyterLab objects (comm, panel) so the message-parsing/dropdown-update
 * logic is unit-testable with a mock comm. */
export class LanePickerController {
  constructor(picker: LanePickerWidget, statusWidget: ModeStatusWidget, isActive: () => boolean) {
    this._picker = picker;
    this._statusWidget = statusWidget;
    this._isActive = isActive;
  }

  /** Feed a parsed comm payload into the picker + (if this notebook is the
   * front end's active one) the status-bar widget. */
  applyStatus(status: LaneStatus): void {
    this._lastStatus = status;
    this._picker.setLanes(status.lanes, status.mode);
    if (this._isActive()) {
      this._statusWidget.mode = status.mode;
    }
  }

  /** Handle a raw comm message (comm_open reply or comm_msg push); ignores
   * anything that doesn't parse as a LaneStatus. */
  handleCommData(data: unknown): void {
    const status = parseLaneStatus(data);
    if (status) {
      this.applyStatus(status);
    }
  }

  /** Attach to a live comm: hook `onMsg` before calling `open()`, since P1's
   * `handle_comm_open` replies synchronously with the current status. A
   * comm attached earlier (e.g. before a kernel restart) has its handler
   * neutralized so a late, stale message can't clobber state read from the
   * new comm. */
  attachComm(comm: ILaneComm): void {
    if (this._comm) {
      this._comm.onMsg = () => {};
    }
    this._comm = comm;
    comm.onMsg = (msg) => {
      if (this._comm !== comm) {
        return;
      }
      this.handleCommData(msg.content.data);
    };
    comm.open();
  }

  /** User picked a lane in the dropdown: send `{set_mode}` over the comm.
   * No optimistic local update -- the picker/status only ever reflect the
   * comm_msg reply this triggers, i.e. server-confirmed state. */
  selectLane(lane: string): void {
    this._comm?.send({ set_mode: lane });
  }

  get lastStatus(): LaneStatus | undefined {
    return this._lastStatus;
  }

  private _picker: LanePickerWidget;
  private _statusWidget: ModeStatusWidget;
  private _isActive: () => boolean;
  private _comm: ILaneComm | undefined;
  private _lastStatus: LaneStatus | undefined;
}

/** Wire a lane picker into every notebook panel's toolbar, bound to that
 * panel's `simple_lane` comm, and keep `statusWidget` in sync with whichever
 * notebook is currently active (`isActive`'s check on `notebooks.currentWidget`
 * -- a background notebook's comm pushes must not overwrite the status bar
 * for the notebook the user is actually looking at). */
export function wireLanePicker(notebooks: INotebookTracker, statusWidget: ModeStatusWidget): void {
  notebooks.widgetAdded.connect((_sender, panel: NotebookPanel) => {
    const isActive = (): boolean => notebooks.currentWidget === panel;
    let controller!: LanePickerController;
    const widget = new LanePickerWidget((lane) => controller.selectLane(lane));
    controller = new LanePickerController(widget, statusWidget, isActive);
    panel.toolbar.insertItem(10, "simple-lane-picker", widget);

    const attach = (): void => {
      const kernel = panel.sessionContext.session?.kernel;
      if (!kernel) {
        return;
      }
      const comm = kernel.createComm(SIMPLE_LANE_COMM_TARGET) as unknown as ILaneComm;
      controller.attachComm(comm);
    };
    // Apply immediately: a restored session may add the panel *after* its
    // kernel already connected (same restored-session case kernel.ts's
    // wireKernelLanguageMapping documents), in which case kernelChanged
    // never fires.
    attach();
    panel.sessionContext.kernelChanged.connect(() => attach());
  });
}
