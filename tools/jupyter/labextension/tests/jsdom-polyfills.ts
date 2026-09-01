// jsdom 20 (pinned via jest-environment-jsdom) does not implement
// `DragEvent`, which `@lumino/dragdrop` (a transitive dependency of
// `@lumino/widgets`, used by status.ts's ModeStatusWidget) references at
// module-evaluation time (`class Event extends DragEvent`). Polyfill the
// bare minimum so importing `@lumino/widgets` under jsdom doesn't throw;
// none of these tests exercise real drag-and-drop.
if (typeof (globalThis as any).DragEvent === "undefined") {
  (globalThis as any).DragEvent = class DragEvent extends Event {
    dataTransfer: unknown;
    constructor(type: string, eventInitDict?: EventInit & { dataTransfer?: unknown }) {
      super(type, eventInitDict);
      this.dataTransfer = eventInitDict?.dataTransfer ?? null;
    }
  };
}
