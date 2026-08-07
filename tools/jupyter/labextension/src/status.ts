// Status-bar "execution mode / lane" indicator (X2).
//
// Shows the current notebook's execution mode (local CPU/JIT vs a remote
// lane such as GPU/JTAG/board). Lane-switching magics land in K3 and the
// lane picker comm lands in X3 (see
// doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md); until
// then every Simple notebook runs in the "local" lane by definition, so this
// widget is a real, registered status-bar item with a fixed placeholder
// value rather than a stub -- X3 replaces `DEFAULT_MODE` with a live value
// sourced from the lane comm, it does not need to register the widget itself.
import { Widget } from "@lumino/widgets";

export const DEFAULT_MODE = "local";
export const MODE_STATUS_ITEM_ID = "simple-lang:mode-status";

/** A minimal status-bar widget rendering "Simple: <mode>". Kept as a plain
 * `Widget` (not a React component) so it has no extra runtime dependency
 * beyond `@lumino/widgets`, already required by every JupyterLab plugin. */
export class ModeStatusWidget extends Widget {
  constructor(mode: string = DEFAULT_MODE) {
    super({ node: ModeStatusWidget._createNode() });
    this.addClass("simple-mode-status");
    this._mode = mode;
    this._render();
  }

  get mode(): string {
    return this._mode;
  }

  set mode(value: string) {
    if (value === this._mode) {
      return;
    }
    this._mode = value;
    this._render();
  }

  private _render(): void {
    this.node.textContent = `Simple: ${this._mode}`;
    this.node.title = `Simple notebook execution lane: ${this._mode}`;
  }

  private static _createNode(): HTMLElement {
    const node = document.createElement("div");
    node.classList.add("simple-mode-status");
    return node;
  }

  private _mode: string;
}
