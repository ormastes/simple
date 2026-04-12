"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.EditorMarkerManager = void 0;
function cloneState(state) {
    return {
        breakpoints: [...state.breakpoints],
    };
}
class EditorMarkerManager {
    constructor() {
        this.states = new Map();
    }
    getState(documentUri) {
        const state = this.states.get(documentUri.toString());
        return state ? cloneState(state) : { breakpoints: [] };
    }
    toggleBreakpoint(documentUri, line) {
        const key = documentUri.toString();
        const state = this.getOrCreateState(key);
        const index = state.breakpoints.indexOf(line);
        if (index >= 0) {
            state.breakpoints.splice(index, 1);
        }
        else {
            state.breakpoints.push(line);
            state.breakpoints.sort((left, right) => left - right);
        }
        return cloneState(state);
    }
    getOrCreateState(key) {
        let state = this.states.get(key);
        if (!state) {
            state = { breakpoints: [] };
            this.states.set(key, state);
        }
        return state;
    }
}
exports.EditorMarkerManager = EditorMarkerManager;
//# sourceMappingURL=editorMarkers.js.map