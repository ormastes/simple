/**
 * @jest-environment jsdom
 */
import { DEFAULT_MODE, ModeStatusWidget, MODE_STATUS_ITEM_ID } from "../src/status";

describe("mode status-bar widget (X2)", () => {
  it("defaults to the 'local' placeholder lane", () => {
    const widget = new ModeStatusWidget();
    expect(widget.mode).toBe("local");
    expect(DEFAULT_MODE).toBe("local");
    expect(widget.node.textContent).toBe("Simple: local");
  });

  it("has a stable status item id for registration", () => {
    expect(MODE_STATUS_ITEM_ID).toBe("simple-lang:mode-status");
  });

  it("re-renders when the mode is changed (future lane-picker hook, X3)", () => {
    const widget = new ModeStatusWidget();
    widget.mode = "gpu-remote-0";
    expect(widget.node.textContent).toBe("Simple: gpu-remote-0");
    expect(widget.node.title).toContain("gpu-remote-0");
  });

  it("is a no-op re-render when set to the same mode", () => {
    const widget = new ModeStatusWidget("local");
    widget.mode = "local";
    expect(widget.node.textContent).toBe("Simple: local");
  });
});
