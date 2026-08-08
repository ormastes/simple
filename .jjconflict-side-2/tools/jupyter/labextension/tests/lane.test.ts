/**
 * @jest-environment jsdom
 */
import { Signal } from "@lumino/signaling";
import {
  LanePickerController,
  LanePickerWidget,
  SIMPLE_LANE_COMM_TARGET,
  parseLaneStatus,
  wireLanePicker,
} from "../src/lane";
import { ModeStatusWidget } from "../src/status";

/** Minimal fake comm, matching export.test.ts's style: captures what was
 * sent/opened and lets the test drive `onMsg` the way a real `simple_lane`
 * comm_msg push would. */
function makeFakeComm() {
  const comm: any = {
    onMsg: undefined,
    opened: false,
    sent: [] as unknown[],
    open: jest.fn(() => {
      comm.opened = true;
    }),
    send: jest.fn((data: unknown) => {
      comm.sent.push(data);
    }),
  };
  return comm;
}

function pushStatus(comm: any, mode: string, lanes: string[]): void {
  comm.onMsg({ content: { data: { mode, lanes } } });
}

describe("parseLaneStatus (X3)", () => {
  it("parses P1's exact wire shape", () => {
    expect(parseLaneStatus({ mode: "interpreter", lanes: ["interpreter"] })).toEqual({
      mode: "interpreter",
      lanes: ["interpreter"],
    });
  });

  it("rejects null / non-object payloads", () => {
    expect(parseLaneStatus(null)).toBeUndefined();
    expect(parseLaneStatus(undefined)).toBeUndefined();
    expect(parseLaneStatus("interpreter")).toBeUndefined();
    expect(parseLaneStatus(42)).toBeUndefined();
  });

  it("rejects a missing or non-string mode", () => {
    expect(parseLaneStatus({ lanes: ["interpreter"] })).toBeUndefined();
    expect(parseLaneStatus({ mode: 1, lanes: ["interpreter"] })).toBeUndefined();
  });

  it("rejects a missing or non-array lanes field", () => {
    expect(parseLaneStatus({ mode: "interpreter" })).toBeUndefined();
    expect(parseLaneStatus({ mode: "interpreter", lanes: "interpreter" })).toBeUndefined();
  });

  it("rejects a lanes array with a non-string element", () => {
    expect(parseLaneStatus({ mode: "interpreter", lanes: ["interpreter", 1] })).toBeUndefined();
  });
});

describe("LanePickerWidget (X3)", () => {
  it("populates <select> options from the lane list and selects mode", () => {
    const widget = new LanePickerWidget(() => {});
    widget.setLanes(["interpreter", "gpu-remote-0"], "interpreter");
    const select = widget.node as HTMLSelectElement;
    expect(Array.from(select.options).map((o) => o.value)).toEqual(["interpreter", "gpu-remote-0"]);
    expect(widget.value).toBe("interpreter");
  });

  it("prepends the current mode if it isn't in the lane list, rather than dropping it", () => {
    const widget = new LanePickerWidget(() => {});
    widget.setLanes(["interpreter"], "gpu-remote-0");
    const select = widget.node as HTMLSelectElement;
    expect(Array.from(select.options).map((o) => o.value)).toEqual(["gpu-remote-0", "interpreter"]);
    expect(widget.value).toBe("gpu-remote-0");
  });

  it("invokes the onLaneSelected callback with the new value on change", () => {
    const onLaneSelected = jest.fn();
    const widget = new LanePickerWidget(onLaneSelected);
    widget.setLanes(["interpreter", "gpu-remote-0"], "interpreter");
    const select = widget.node as HTMLSelectElement;
    select.value = "gpu-remote-0";
    select.dispatchEvent(new Event("change"));
    expect(onLaneSelected).toHaveBeenCalledWith("gpu-remote-0");
  });
});

describe("LanePickerController (X3)", () => {
  function makeController(isActive = () => true) {
    const picker = new LanePickerWidget(() => {});
    const status = new ModeStatusWidget();
    const controller = new LanePickerController(picker, status, isActive);
    return { picker, status, controller };
  }

  it("comm_open reply updates the dropdown and (when active) the status widget", () => {
    const { picker, status, controller } = makeController();
    const comm = makeFakeComm();

    controller.attachComm(comm);
    expect(comm.opened).toBe(true);

    pushStatus(comm, "interpreter", ["interpreter"]);

    expect(picker.value).toBe("interpreter");
    expect(status.mode).toBe("interpreter");
  });

  it("does not update the status widget when this notebook is not the active one", () => {
    const { picker, status, controller } = makeController(() => false);
    const comm = makeFakeComm();
    controller.attachComm(comm);

    pushStatus(comm, "gpu-remote-0", ["interpreter", "gpu-remote-0"]);

    expect(picker.value).toBe("gpu-remote-0"); // dropdown always updates
    expect(status.mode).toBe("local"); // status widget untouched
  });

  it("selecting a lane sends {set_mode} and does NOT optimistically update state", () => {
    const { picker, status, controller } = makeController();
    const comm = makeFakeComm();
    controller.attachComm(comm);
    pushStatus(comm, "interpreter", ["interpreter", "gpu-remote-0"]);

    controller.selectLane("gpu-remote-0");

    expect(comm.sent).toEqual([{ set_mode: "gpu-remote-0" }]);
    // No comm_msg reply has arrived yet -- state must still show the old mode.
    expect(picker.value).toBe("interpreter");
    expect(status.mode).toBe("interpreter");

    // The kernel's reply arrives asynchronously as another comm_msg push.
    pushStatus(comm, "gpu-remote-0", ["interpreter", "gpu-remote-0"]);
    expect(picker.value).toBe("gpu-remote-0");
    expect(status.mode).toBe("gpu-remote-0");
  });

  it("selectLane before any comm is attached is a silent no-op (no throw)", () => {
    const { controller } = makeController();
    expect(() => controller.selectLane("gpu-remote-0")).not.toThrow();
  });

  it("ignores a message that doesn't parse as a LaneStatus", () => {
    const { picker, controller } = makeController();
    const comm = makeFakeComm();
    controller.attachComm(comm);
    picker.setLanes(["interpreter"], "interpreter");

    comm.onMsg({ content: { data: { unrelated: true } } });

    expect(picker.value).toBe("interpreter");
    expect(controller.lastStatus).toBeUndefined();
  });

  it("attaching a new comm (e.g. kernel restart) neutralizes the previous comm's onMsg", () => {
    const { picker, controller } = makeController();
    const commA = makeFakeComm();
    const commB = makeFakeComm();

    controller.attachComm(commA);
    controller.attachComm(commB);

    // A stale message arriving late on the old comm must not clobber state
    // read from the new one.
    pushStatus(commA, "stale-mode", ["stale-mode"]);
    expect(picker.value).not.toBe("stale-mode");

    pushStatus(commB, "interpreter", ["interpreter"]);
    expect(picker.value).toBe("interpreter");
  });
});

describe("wireLanePicker (X3)", () => {
  function makeFakePanel(comm: ReturnType<typeof makeFakeComm>, kernelLanguage = "simple") {
    const insertItem = jest.fn();
    const kernelChanged = new Signal<any, void>({});
    const panel: any = {
      toolbar: { insertItem },
      sessionContext: {
        kernelChanged,
        session: {
          kernel: {
            createComm: jest.fn((_target: string) => comm),
          },
        },
      },
    };
    return { panel, insertItem, kernelChanged };
  }

  it("inserts a lane-picker toolbar item and opens the simple_lane comm on widgetAdded", () => {
    const comm = makeFakeComm();
    const { panel, insertItem } = makeFakePanel(comm);
    const widgetAdded = new Signal<any, any>({});
    const notebooks: any = { widgetAdded, currentWidget: panel };

    wireLanePicker(notebooks, new ModeStatusWidget());
    widgetAdded.emit(panel);

    expect(insertItem).toHaveBeenCalledTimes(1);
    const [, name, widget] = insertItem.mock.calls[0];
    expect(name).toBe("simple-lane-picker");
    expect(widget).toBeInstanceOf(LanePickerWidget);
    expect(panel.sessionContext.session.kernel.createComm).toHaveBeenCalledWith(SIMPLE_LANE_COMM_TARGET);
    expect(comm.opened).toBe(true);
  });

  it("re-attaches the comm on kernelChanged (e.g. kernel restart)", () => {
    const comm = makeFakeComm();
    const { panel, kernelChanged } = makeFakePanel(comm);
    const widgetAdded = new Signal<any, any>({});
    const notebooks: any = { widgetAdded, currentWidget: panel };

    wireLanePicker(notebooks, new ModeStatusWidget());
    widgetAdded.emit(panel);
    (panel.sessionContext.session.kernel.createComm as jest.Mock).mockClear();

    kernelChanged.emit(undefined);

    expect(panel.sessionContext.session.kernel.createComm).toHaveBeenCalledWith(SIMPLE_LANE_COMM_TARGET);
  });

  it("does not throw when a panel is added with no kernel yet connected", () => {
    const widgetAdded = new Signal<any, any>({});
    const notebooks: any = { widgetAdded, currentWidget: null };
    const panel: any = {
      toolbar: { insertItem: jest.fn() },
      sessionContext: { session: undefined, kernelChanged: new Signal<any, void>({}) },
    };

    wireLanePicker(notebooks, new ModeStatusWidget());
    expect(() => widgetAdded.emit(panel)).not.toThrow();
  });
});
