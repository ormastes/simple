import * as vscode from 'vscode';

export interface EditorMarkerState {
    breakpoints: number[];
}

function cloneState(state: EditorMarkerState): EditorMarkerState {
    return {
        breakpoints: [...state.breakpoints],
    };
}

export class EditorMarkerManager {
    private readonly states = new Map<string, EditorMarkerState>();

    public getState(documentUri: vscode.Uri): EditorMarkerState {
        const state = this.states.get(documentUri.toString());
        return state ? cloneState(state) : { breakpoints: [] };
    }

    public toggleBreakpoint(documentUri: vscode.Uri, line: number): EditorMarkerState {
        const key = documentUri.toString();
        const state = this.getOrCreateState(key);
        const index = state.breakpoints.indexOf(line);
        if (index >= 0) {
            state.breakpoints.splice(index, 1);
        } else {
            state.breakpoints.push(line);
            state.breakpoints.sort((left, right) => left - right);
        }
        return cloneState(state);
    }

    private getOrCreateState(key: string): EditorMarkerState {
        let state = this.states.get(key);
        if (!state) {
            state = { breakpoints: [] };
            this.states.set(key, state);
        }
        return state;
    }
}
