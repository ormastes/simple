// Status-bar "execution mode / lane" indicator (X2).
//
// Shows the current notebook's execution mode (local CPU/JIT vs a remote
// lane such as GPU/JTAG/board). `DEFAULT_MODE` remains the widget's initial
// value (matches the kernel's own default before any comm reply arrives);
// X3 (./lane.ts) feeds it live updates sourced from the `simple_lane` comm
// once a notebook connects, rather than registering its own widget.
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
