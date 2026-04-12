/**
 * CodeMirror 6-based webview editor for the Rich Custom Editor.
 *
 * Provides:
 * - Full code editing (syntax highlighting, keybindings, search, undo/redo)
 * - Inline math rendering via widget decorations at natural height
 * - Image rendering via widget decorations
 * - Cursor-aware view mode: raw source when cursor is in a block
 * - Two-way sync with the VS Code document model
 */

import {
    EditorView, keymap, drawSelection, highlightActiveLine,
    highlightSpecialChars, highlightActiveLineGutter,
    gutter, GutterMarker, type BlockInfo, type Extension,
} from '@codemirror/view';
import { EditorState } from '@codemirror/state';
import { defaultKeymap, history, historyKeymap, indentWithTab } from '@codemirror/commands';
import { bracketMatching, indentOnInput, syntaxHighlighting, defaultHighlightStyle, HighlightStyle } from '@codemirror/language';
import { searchKeymap, highlightSelectionMatches } from '@codemirror/search';
import { autocompletion, closeBrackets, closeBracketsKeymap } from '@codemirror/autocomplete';
import { tags } from '@lezer/highlight';
import { simpleLanguage } from './simpleLang';
import { createDecorationPlugin, type RenderableBlockInfo } from './decorationPlugin';

// ── VS Code API ──────────────────────────────────────────────────────

declare function acquireVsCodeApi(): {
    postMessage(msg: unknown): void;
    getState(): unknown;
    setState(state: unknown): void;
};

// ── Types ────────────────────────────────────────────────────────────

interface SyncMessage {
    type: 'sync';
    sourceText: string;
    selectionStart: number;
    selectionEnd: number;
    settings: {
        showBlockBorders: boolean;
        centerLineNumbers: boolean;
    };
    blocks: Array<{
        kind: string;
        from: number;
        to: number;
        content: string;
        prefix: string;
        renderedHtml: string;
        imageUri?: string;
        displayMode: 'inline' | 'block';
        status: 'ok' | 'error';
        errorMessage?: string;
    }>;
}

type HostMessage = SyncMessage | { type: 'error'; message: string };

function applyEditorSettings(settings?: SyncMessage['settings']): void {
    const root = document.documentElement;
    const showBlockBorders = settings?.showBlockBorders ?? false;
    const centerLineNumbers = settings?.centerLineNumbers ?? true;

    root.style.setProperty(
        '--simple-rich-block-border',
        showBlockBorders
            ? 'color-mix(in srgb, var(--vscode-editor-foreground) 18%, transparent)'
            : 'transparent',
    );
    root.style.setProperty(
        '--simple-rich-label-bg',
        showBlockBorders
            ? 'color-mix(in srgb, var(--vscode-editor-foreground) 10%, transparent)'
            : 'transparent',
    );
    root.classList.toggle('simple-rich-center-line-numbers', centerLineNumbers);
}

class RichLineNumberWidgetMarker extends GutterMarker {
    constructor(
        readonly lineNumber: string,
        readonly height: number,
    ) {
        super();
    }

    eq(other: RichLineNumberWidgetMarker): boolean {
        return this.lineNumber === other.lineNumber
            && Math.round(this.height) === Math.round(other.height);
    }

    toDOM(): Node {
        const wrap = document.createElement('div');
        wrap.className = 'cm-rich-line-number-marker';
        wrap.textContent = this.lineNumber;
        if (this.height > 0) {
            wrap.style.height = `${this.height}px`;
        }
        return wrap;
    }
}

function maxLineNumber(lines: number): string {
    let last = 9;
    while (last < lines) {
        last = last * 10 + 9;
    }
    return String(last);
}

function createRichLineNumberGutter(): Extension {
    return gutter({
        class: 'cm-lineNumbers',
        lineMarker(view, line: BlockInfo, otherMarkers) {
            if (otherMarkers.some((marker) => marker.toDOM)) {
                return null;
            }
            return new RichLineNumberWidgetMarker(
                String(view.state.doc.lineAt(line.from).number),
                line.height,
            );
        },
        initialSpacer(view) {
            return new RichLineNumberWidgetMarker(maxLineNumber(view.state.doc.lines), 0);
        },
        updateSpacer(spacer, update) {
            const max = maxLineNumber(update.view.state.doc.lines);
            return max === spacer.lineNumber ? spacer : new RichLineNumberWidgetMarker(max, 0);
        },
    });
}

// ── VS Code theme for CodeMirror ─────────────────────────────────────

const vsCodeTheme = EditorView.theme({
    '&': {
        height: '100%',
        fontSize: 'var(--vscode-editor-font-size)',
        fontFamily: 'var(--vscode-editor-font-family)',
        backgroundColor: 'var(--vscode-editor-background)',
        color: 'var(--vscode-editor-foreground)',
    },
    '.cm-content': {
        caretColor: 'var(--vscode-editorCursor-foreground)',
        lineHeight: '1.5',
    },
    '.cm-cursor, .cm-dropCursor': {
        borderLeftColor: 'var(--vscode-editorCursor-foreground)',
    },
    '&.cm-focused .cm-selectionBackground, .cm-selectionBackground': {
        backgroundColor: 'var(--vscode-editor-selectionBackground)',
    },
    '.cm-activeLine': {
        backgroundColor: 'var(--vscode-editor-lineHighlightBackground)',
    },
    '.cm-gutters': {
        backgroundColor: 'var(--vscode-editorGutter-background, var(--vscode-editor-background))',
        color: 'var(--vscode-editorLineNumber-foreground)',
        border: 'none',
    },
    '.cm-rich-line-number-marker': {
        display: 'flex',
        alignItems: 'flex-start',
        justifyContent: 'flex-end',
        width: '100%',
        boxSizing: 'border-box',
    },
    '&.simple-rich-center-line-numbers .cm-rich-line-number-marker': {
        alignItems: 'center',
    },
    '.cm-activeLineGutter': {
        backgroundColor: 'var(--vscode-editor-lineHighlightBackground)',
        color: 'var(--vscode-editorLineNumber-activeForeground)',
    },
    '.cm-matchingBracket': {
        backgroundColor: 'var(--vscode-editorBracketMatch-background)',
        outline: '1px solid var(--vscode-editorBracketMatch-border)',
    },
    '.cm-searchMatch': {
        backgroundColor: 'var(--vscode-editor-findMatchHighlightBackground)',
    },
    '.cm-searchMatch.cm-searchMatch-selected': {
        backgroundColor: 'var(--vscode-editor-findMatchBackground)',
    },
    // Math widget
    '.cm-math-widget': {
        display: 'inline-flex',
        alignItems: 'center',
        gap: '4px',
        padding: '4px 8px',
        margin: '2px 0',
        borderRadius: '4px',
        backgroundColor: 'transparent',
        border: '1px solid var(--simple-rich-block-border)',
        verticalAlign: 'middle',
        cursor: 'pointer',
    },
    '.cm-math-rendered': {
        display: 'inline-block',
        color: 'var(--vscode-editor-foreground)',
    },
    '.cm-math-rendered .katex': {
        color: 'inherit',
    },
    '.cm-math-rendered .frac-line': {
        borderBottomWidth: '0.09em !important',
        minHeight: '0.09em',
    },
    '.cm-math-label': {
        fontSize: '0.75em',
        fontWeight: '600',
        color: 'var(--vscode-editorLineNumber-foreground)',
        padding: '0 4px',
        borderRadius: '3px',
        backgroundColor: 'var(--simple-rich-label-bg)',
    },
    // Image widget
    '.cm-image-widget': {
        display: 'inline-flex',
        verticalAlign: 'middle',
        alignItems: 'center',
        padding: '6px 8px',
        margin: '2px 0',
        borderRadius: '6px',
        backgroundColor: 'transparent',
        border: '1px solid var(--simple-rich-block-border)',
        textAlign: 'center',
        maxWidth: '100%',
    },
    '.cm-image-widget img': {
        borderRadius: '4px',
        boxShadow: '0 1px 4px color-mix(in srgb, black 20%, transparent)',
    },
    // Error & placeholder
    '.cm-image-error': {
        display: 'inline-block',
        padding: '4px 8px',
        borderRadius: '4px',
        color: 'var(--vscode-errorForeground)',
        backgroundColor: 'color-mix(in srgb, var(--vscode-errorForeground) 10%, transparent)',
        fontStyle: 'italic',
        fontSize: '0.9em',
    },
    '.cm-placeholder-widget': {
        display: 'inline-block',
        padding: '2px 6px',
        borderRadius: '4px',
        backgroundColor: 'transparent',
        border: '1px solid var(--simple-rich-block-border)',
        color: 'var(--vscode-descriptionForeground)',
        fontStyle: 'italic',
        fontSize: '0.9em',
    },
}, { dark: true });

const simpleHighlightStyle = HighlightStyle.define([
    { tag: tags.keyword, color: 'var(--vscode-symbolIcon-keywordForeground, #c586c0)' },
    { tag: tags.typeName, color: 'var(--vscode-symbolIcon-classForeground, #4ec9b0)' },
    { tag: tags.variableName, color: 'var(--vscode-symbolIcon-variableForeground, #9cdcfe)' },
    { tag: tags.string, color: 'var(--vscode-symbolIcon-stringForeground, #ce9178)' },
    { tag: tags.number, color: 'var(--vscode-symbolIcon-numberForeground, #b5cea8)' },
    { tag: tags.lineComment, color: 'var(--vscode-symbolIcon-commentForeground, #6a9955)', fontStyle: 'italic' },
    { tag: tags.operator, color: 'var(--vscode-symbolIcon-operatorForeground, #d4d4d4)' },
    { tag: tags.bracket, color: 'var(--vscode-editorBracketHighlight-foreground1, #ffd700)' },
    { tag: tags.atom, color: 'var(--vscode-symbolIcon-constantForeground, #569cd6)', fontStyle: 'italic' },
]);

// ── Editor creation ──────────────────────────────────────────────────

function createEditor(
    parent: HTMLElement,
    initialText: string,
    renderedBlocksRef: { current: Map<string, RenderableBlockInfo> },
    onEdit: (text: string, selStart: number, selEnd: number) => void,
    onSelectionChange: (selStart: number, selEnd: number) => void,
): {
    view: EditorView;
    refreshDecorations: () => void;
    setDoc: (text: string, selStart?: number, selEnd?: number) => void;
} {
    let isApplyingSync = false;
    let editTimer: ReturnType<typeof setTimeout> | null = null;

    const decorationPlugin = createDecorationPlugin(() => renderedBlocksRef.current);

    const editListener = EditorView.updateListener.of((update) => {
        if (isApplyingSync) return;

        if (update.docChanged) {
            if (editTimer) clearTimeout(editTimer);
            editTimer = setTimeout(() => {
                const sel = update.view.state.selection.main;
                onEdit(update.view.state.doc.toString(), sel.anchor, sel.head);
            }, 120);
        } else if (update.selectionSet) {
            const sel = update.view.state.selection.main;
            onSelectionChange(sel.anchor, sel.head);
        }
    });

    const extensions: Extension[] = [
        createRichLineNumberGutter(),
        highlightActiveLineGutter(),
        highlightSpecialChars(),
        history(),
        drawSelection(),
        EditorState.allowMultipleSelections.of(true),
        indentOnInput(),
        bracketMatching(),
        closeBrackets(),
        autocompletion(),
        highlightActiveLine(),
        highlightSelectionMatches(),
        keymap.of([
            ...closeBracketsKeymap,
            ...defaultKeymap,
            ...searchKeymap,
            ...historyKeymap,
            indentWithTab,
        ]),
        simpleLanguage,
        vsCodeTheme,
        syntaxHighlighting(simpleHighlightStyle),
        syntaxHighlighting(defaultHighlightStyle, { fallback: true }),
        decorationPlugin,
        editListener,
    ];

    const view = new EditorView({
        state: EditorState.create({
            doc: initialText,
            extensions,
        }),
        parent,
    });

    return {
        view,

        refreshDecorations() {
            // Force decoration rebuild by dispatching empty transaction
            view.dispatch({});
        },

        setDoc(text: string, selStart?: number, selEnd?: number) {
            if (view.state.doc.toString() === text && selStart === undefined) return;

            isApplyingSync = true;
            try {
                const changes = view.state.doc.toString() !== text
                    ? { from: 0, to: view.state.doc.length, insert: text }
                    : undefined;

                const selection = selStart !== undefined
                    ? { anchor: Math.min(selStart, text.length), head: Math.min(selEnd ?? selStart, text.length) }
                    : undefined;

                view.dispatch({
                    ...(changes ? { changes } : {}),
                    ...(selection ? { selection } : {}),
                });
            } finally {
                isApplyingSync = false;
            }
        },
    };
}

// ── Boot: wire up VS Code messaging ──────────────────────────────────

export function boot(vsCodeApi?: { postMessage(msg: unknown): void }): void {
    const vscode = vsCodeApi ?? acquireVsCodeApi();
    const editorContainer = document.getElementById('editor-container');
    if (!editorContainer) return;

    const renderedBlocksRef: { current: Map<string, RenderableBlockInfo> } = {
        current: new Map(),
    };

    let editor: ReturnType<typeof createEditor> | null = null;

    function initEditor(text: string, selStart: number, selEnd: number) {
        editor = createEditor(
            editorContainer!,
            text,
            renderedBlocksRef,
            (source, sStart, sEnd) => {
                vscode.postMessage({ type: 'editAll', source, selectionStart: sStart, selectionEnd: sEnd });
            },
            (sStart, sEnd) => {
                vscode.postMessage({ type: 'selectionChanged', selectionStart: sStart, selectionEnd: sEnd });
            },
        );
        if (selStart > 0 || selEnd > 0) {
            editor.setDoc(text, selStart, selEnd);
        }
    }

    window.addEventListener('message', (event) => {
        const msg = event.data as HostMessage;

        if (msg.type === 'sync') {
            applyEditorSettings(msg.settings);
            // Update rendered blocks cache
            renderedBlocksRef.current.clear();
            if (msg.blocks) {
                for (const block of msg.blocks) {
                    const key = `${block.prefix}:${block.content}`;
                    renderedBlocksRef.current.set(key, block);
                }
            }

            if (!editor) {
                initEditor(msg.sourceText, msg.selectionStart, msg.selectionEnd);
            } else {
                editor.setDoc(msg.sourceText, msg.selectionStart, msg.selectionEnd);
            }
            editor!.refreshDecorations();
        }
    });

    // Request initial state
    vscode.postMessage({ type: 'ready' });
}
