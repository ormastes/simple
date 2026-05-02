/**
 * CodeMirror-based webview editor for the Math Custom Editor.
 *
 * This module runs inside a VS Code webview. It provides:
 * - Full code editing (syntax highlighting, keybindings, search, undo/redo)
 * - Inline math rendering via widget decorations at natural height
 * - Cursor-aware reveal: shows raw source when cursor is in a math block
 * - Two-way sync with the VS Code document model
 */

import {
    EditorView, keymap, drawSelection, highlightActiveLine,
    highlightSpecialChars, lineNumbers, highlightActiveLineGutter,
    ViewPlugin, ViewUpdate, Decoration, DecorationSet, WidgetType,
    type PluginValue,
} from '@codemirror/view';
import { EditorState, type Extension, RangeSetBuilder } from '@codemirror/state';
import { defaultKeymap, history, historyKeymap, indentWithTab } from '@codemirror/commands';
import { bracketMatching, indentOnInput, syntaxHighlighting, defaultHighlightStyle, HighlightStyle } from '@codemirror/language';
import { searchKeymap, highlightSelectionMatches } from '@codemirror/search';
import { autocompletion, closeBrackets, closeBracketsKeymap } from '@codemirror/autocomplete';
import { tags } from '@lezer/highlight';
import { simpleLanguage } from './simpleLang';

// ── VS Code API ──────────────────────────────────────────────────────

declare function acquireVsCodeApi(): {
    postMessage(msg: unknown): void;
    getState(): unknown;
    setState(state: unknown): void;
};

// ── Types ────────────────────────────────────────────────────────────

interface MathBlockInfo {
    from: number;
    to: number;
    prefixEnd: number; // end of "m{" / "loss{" / "nograd{"
    content: string;
    prefix: string;
    renderedHtml: string; // KaTeX HTML from host
}

interface SyncMessage {
    type: 'sync';
    sourceText: string;
    selectionStart: number;
    selectionEnd: number;
    mathBlocks: MathBlockInfo[];
}

interface FocusedBlockMessage {
    type: 'focusedBlock';
    html: string;
    label: string;
    source: string;
    pretty: string;
    statusKind: string;
    statusMessage: string;
    hasContent: boolean;
}

type HostMessage = SyncMessage | FocusedBlockMessage;

// ── Math block regex (mirrors host-side) ─────────────────────────────

const MATH_BLOCK_REGEX = /\b(?<prefix>m|loss|nograd)\{([^}]*(?:\{[^}]*\}[^}]*)*)\}/gs;

function detectMathBlocks(text: string): Array<{ from: number; to: number; prefixEnd: number; content: string; prefix: string }> {
    const blocks: Array<{ from: number; to: number; prefixEnd: number; content: string; prefix: string }> = [];
    MATH_BLOCK_REGEX.lastIndex = 0;
    let match: RegExpExecArray | null;
    while ((match = MATH_BLOCK_REGEX.exec(text)) !== null) {
        const prefix = match.groups?.prefix ?? 'm';
        blocks.push({
            from: match.index,
            to: match.index + match[0].length,
            prefixEnd: match.index + prefix.length + 1, // after "m{" etc.
            content: match[2].trim(),
            prefix,
        });
    }
    return blocks;
}

// ── Math Widget ──────────────────────────────────────────────────────

class MathWidget extends WidgetType {
    constructor(
        readonly html: string,
        readonly prefix: string,
        readonly content: string,
    ) {
        super();
    }

    eq(other: MathWidget): boolean {
        return this.html === other.html && this.prefix === other.prefix;
    }

    toDOM(): HTMLElement {
        const wrap = document.createElement('span');
        wrap.className = 'cm-math-widget';

        // Prefix indicator
        if (this.prefix !== 'm') {
            const label = document.createElement('span');
            label.className = 'cm-math-label';
            label.textContent = this.prefix === 'loss' ? 'L' : '\u2205';
            wrap.appendChild(label);
        }

        // Rendered math at natural height
        const rendered = document.createElement('span');
        rendered.className = 'cm-math-rendered';
        rendered.innerHTML = this.html;
        wrap.appendChild(rendered);

        return wrap;
    }

    ignoreEvent(): boolean {
        return false;
    }
}

// Placeholder widget used when host hasn't sent rendered HTML yet
class MathPlaceholderWidget extends WidgetType {
    constructor(readonly content: string, readonly prefix: string) {
        super();
    }

    eq(other: MathPlaceholderWidget): boolean {
        return this.content === other.content && this.prefix === other.prefix;
    }

    toDOM(): HTMLElement {
        const wrap = document.createElement('span');
        wrap.className = 'cm-math-placeholder';
        wrap.textContent = this.prefix === 'm' ? `m{ ${this.content} }` :
            `${this.prefix}{ ${this.content} }`;
        return wrap;
    }

    ignoreEvent(): boolean {
        return false;
    }
}

// ── Math decoration plugin ───────────────────────────────────────────

interface MathPluginState extends PluginValue {
    decorations: DecorationSet;
}

function buildMathDecorations(
    view: EditorView,
    renderedBlocks: Map<string, string>,
): DecorationSet {
    const builder = new RangeSetBuilder<Decoration>();
    const doc = view.state.doc;
    const text = doc.toString();
    const blocks = detectMathBlocks(text);

    // Get cursor position for cursor-aware reveal
    const cursor = view.state.selection.main.head;

    for (const block of blocks) {
        // Cursor-aware reveal: if cursor is inside the block, skip decoration
        if (cursor >= block.from && cursor <= block.to) {
            continue;
        }

        const key = `${block.prefix}:${block.content}`;
        const html = renderedBlocks.get(key);

        if (html) {
            builder.add(
                block.from,
                block.to,
                Decoration.replace({
                    widget: new MathWidget(html, block.prefix, block.content),
                }),
            );
        } else {
            // Show placeholder until host sends rendered HTML
            builder.add(
                block.from,
                block.to,
                Decoration.replace({
                    widget: new MathPlaceholderWidget(block.content, block.prefix),
                }),
            );
        }
    }

    return builder.finish();
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
    // Math widget styles
    '.cm-math-widget': {
        display: 'inline-flex',
        alignItems: 'center',
        gap: '4px',
        padding: '4px 8px',
        margin: '2px 0',
        borderRadius: '4px',
        backgroundColor: 'color-mix(in srgb, var(--vscode-editor-foreground) 8%, transparent)',
        border: '1px solid color-mix(in srgb, var(--vscode-editor-foreground) 15%, transparent)',
        verticalAlign: 'middle',
        cursor: 'pointer',
    },
    '.cm-math-rendered': {
        // Natural height — no clamping, this is the whole point of the custom editor
        display: 'inline-block',
    },
    '.cm-math-label': {
        fontSize: '0.75em',
        fontWeight: '600',
        color: 'var(--vscode-editorLineNumber-foreground)',
        padding: '0 4px',
        borderRadius: '3px',
        backgroundColor: 'color-mix(in srgb, var(--vscode-editor-foreground) 12%, transparent)',
    },
    '.cm-math-placeholder': {
        display: 'inline-block',
        padding: '2px 6px',
        borderRadius: '4px',
        backgroundColor: 'color-mix(in srgb, var(--vscode-editor-foreground) 5%, transparent)',
        color: 'var(--vscode-descriptionForeground)',
        fontStyle: 'italic',
        fontSize: '0.9em',
    },
}, { dark: true });

// Syntax highlighting colors matching VS Code
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

// ── Editor initialization ────────────────────────────────────────────

export function createEditor(
    parent: HTMLElement,
    initialText: string,
    onEdit: (text: string, selStart: number, selEnd: number) => void,
    onSelectionChange: (selStart: number, selEnd: number) => void,
): {
    view: EditorView;
    updateRenderedBlocks: (blocks: Map<string, string>) => void;
    setDoc: (text: string, selStart?: number, selEnd?: number) => void;
} {
    // Rendered math HTML from host, keyed by "prefix:content"
    let renderedBlocks = new Map<string, string>();

    let isApplyingSync = false;
    let editTimer: ReturnType<typeof setTimeout> | null = null;

    // Math decoration plugin
    const mathPlugin = ViewPlugin.define<MathPluginState>((view) => ({
        decorations: buildMathDecorations(view, renderedBlocks),
        update(update: ViewUpdate) {
            if (update.docChanged || update.selectionSet) {
                this.decorations = buildMathDecorations(update.view, renderedBlocks);
            }
        },
    }), {
        decorations: (v) => v.decorations,
    });

    // Edit/selection listener
    const editListener = EditorView.updateListener.of((update: ViewUpdate) => {
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
        lineNumbers(),
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
        mathPlugin,
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

        updateRenderedBlocks(blocks: Map<string, string>) {
            renderedBlocks = blocks;
            // Force re-decoration
            const plugin = view.plugin(mathPlugin);
            if (plugin) {
                plugin.decorations = buildMathDecorations(view, renderedBlocks);
                view.dispatch({}); // trigger update cycle
            }
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

    // Right panel elements
    const renderedEl = document.getElementById('rendered');
    const blockLabelEl = document.getElementById('block-label');
    const blockSourceEl = document.getElementById('block-source');
    const blockPrettyEl = document.getElementById('block-pretty');
    const renderStatusEl = document.getElementById('render-status');
    const selectionEl = document.getElementById('selection');

    let editor: ReturnType<typeof createEditor> | null = null;
    const renderedBlocksMap = new Map<string, string>();

    function statusClass(kind: string): string {
        switch (kind) {
            case 'error': return 'status status-error';
            case 'ok': return 'status status-ok';
            default: return 'status status-info';
        }
    }

    function initEditor(text: string, selStart: number, selEnd: number) {
        editor = createEditor(
            editorContainer!,
            text,
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
            // Update rendered blocks cache
            if (msg.mathBlocks) {
                renderedBlocksMap.clear();
                for (const block of msg.mathBlocks) {
                    const key = `${block.prefix}:${block.content}`;
                    renderedBlocksMap.set(key, block.renderedHtml);
                }
            }

            if (!editor) {
                initEditor(msg.sourceText, msg.selectionStart, msg.selectionEnd);
                editor!.updateRenderedBlocks(renderedBlocksMap);
            } else {
                editor.setDoc(msg.sourceText, msg.selectionStart, msg.selectionEnd);
                editor.updateRenderedBlocks(renderedBlocksMap);
            }

            if (selectionEl) {
                selectionEl.textContent = `${msg.selectionStart}-${msg.selectionEnd}`;
            }
        }

        if (msg.type === 'focusedBlock') {
            if (renderStatusEl) {
                renderStatusEl.className = statusClass(msg.statusKind);
                renderStatusEl.dataset.kind = msg.statusKind;
                renderStatusEl.textContent = msg.statusMessage;
            }
            if (blockLabelEl) {
                blockLabelEl.textContent = msg.label;
            }
            if (msg.hasContent) {
                if (renderedEl) renderedEl.innerHTML = msg.html;
                if (blockSourceEl) blockSourceEl.textContent = msg.source;
                if (blockPrettyEl) blockPrettyEl.textContent = msg.pretty;
            } else {
                if (renderedEl) renderedEl.innerHTML = '<div class="empty-state">Move the caret into a math block.</div>';
                if (blockSourceEl) blockSourceEl.innerHTML = '<span class="empty-state">No active math block</span>';
                if (blockPrettyEl) blockPrettyEl.innerHTML = '<span class="empty-state">No active math block</span>';
            }
        }
    });

    // Request initial state
    vscode.postMessage({ type: 'ready' });
}
