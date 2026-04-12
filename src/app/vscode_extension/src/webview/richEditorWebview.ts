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
    Decoration, GutterMarker, WidgetType, gutter, lineNumbers, lineNumberWidgetMarker, type BlockInfo, type DecorationSet, type Extension, type ViewUpdate,
} from '@codemirror/view';
import { EditorState, RangeSetBuilder, StateEffect, StateField } from '@codemirror/state';
import { defaultKeymap, history, historyKeymap, indentWithTab } from '@codemirror/commands';
import { bracketMatching, indentOnInput, syntaxHighlighting, defaultHighlightStyle, HighlightStyle } from '@codemirror/language';
import { searchKeymap, highlightSelectionMatches } from '@codemirror/search';
import { autocompletion, closeBrackets, closeBracketsKeymap } from '@codemirror/autocomplete';
import { tags } from '@lezer/highlight';
import { simpleLanguage } from './simpleLang';
import { createDecorationPlugin, type RenderableBlockInfo } from './decorationPlugin';
import { MathWidget } from './widgets/mathWidget';

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
    symbols: Array<{
        name: string;
        kind: string;
        detail: string;
        line: number;
        from: number;
        to: number;
    }>;
    tests: Array<{
        kind: string;
        label: string;
        line: number;
        from: number;
        to: number;
    }>;
    markers: {
        breakpoints: number[];
    };
}

type HostMessage = SyncMessage | { type: 'error'; message: string };

const ENABLE_TEST_LINE_WIDGETS = true;
const ENABLE_SYMBOL_HOVER = true;
const ENABLE_FULL_LINE_BLOCK_MATH = true;

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

interface RichEditorSymbol {
    name: string;
    kind: string;
    detail: string;
    line: number;
    from: number;
    to: number;
}

interface RichEditorTestBlock {
    kind: string;
    label: string;
    line: number;
    from: number;
    to: number;
}

interface RichEditorMarkers {
    breakpoints: number[];
}

class TestRunGutterMarker extends GutterMarker {
    constructor(readonly test: RichEditorTestBlock | null) {
        super();
    }

    eq(other: TestRunGutterMarker): boolean {
        return this.test?.kind === other.test?.kind
            && this.test?.label === other.test?.label
            && this.test?.line === other.test?.line;
    }

    toDOM(): HTMLElement {
        const node = document.createElement('span');
        node.className = 'cm-test-gutter-icon';
        if (this.test) {
            node.title = `Run ${this.test.kind}: ${this.test.label}`;
            node.setAttribute('aria-label', node.title);
        } else {
            node.classList.add('cm-test-gutter-icon-spacer');
            node.setAttribute('aria-hidden', 'true');
        }
        return node;
    }
}

class BreakpointGutterMarker extends GutterMarker {
    constructor(readonly active: boolean) {
        super();
    }

    eq(other: BreakpointGutterMarker): boolean {
        return this.active === other.active;
    }

    toDOM(): HTMLElement {
        const node = document.createElement('span');
        node.className = `cm-breakpoint-gutter-icon${this.active ? ' cm-breakpoint-gutter-icon-active' : ''}`;
        if (!this.active) {
            node.classList.add('cm-breakpoint-gutter-icon-spacer');
            node.setAttribute('aria-hidden', 'true');
        }
        return node;
    }
}

const MATH_BLOCK_REGEX = /\b(?<prefix>m|loss|nograd|img|graph)\{([^}]*(?:\{[^}]*\}[^}]*)*)\}/gs;

interface FullLineMathBlock {
    from: number;
    to: number;
    lineFrom: number;
    lineTo: number;
    content: string;
    prefix: string;
}

function detectFullLineMathBlocks(state: EditorState): FullLineMathBlock[] {
    const blocks: FullLineMathBlock[] = [];
    const text = state.doc.toString();
    MATH_BLOCK_REGEX.lastIndex = 0;

    let match: RegExpExecArray | null;
    while ((match = MATH_BLOCK_REGEX.exec(text)) !== null) {
        const line = state.doc.lineAt(match.index);
        const lineText = state.doc.sliceString(line.from, line.to);
        const leading = lineText.length - lineText.trimStart().length;
        const trailing = lineText.length - lineText.trimEnd().length;
        const from = match.index;
        const to = match.index + match[0].length;
        if (match.groups?.prefix === 'img') {
            continue;
        }
        if (line.from + leading !== from || line.to - trailing !== to) {
            continue;
        }
        blocks.push({
            from,
            to,
            lineFrom: line.from,
            lineTo: line.to,
            content: match[2].trim(),
            prefix: match.groups?.prefix ?? 'm',
        });
    }

    return blocks;
}

const refreshRenderedBlocksEffect = StateEffect.define<void>();

function buildFullLineMathDecorations(
    state: EditorState,
    renderedBlocks: Map<string, RenderableBlockInfo>,
): DecorationSet {
    const builder = new RangeSetBuilder<Decoration>();
    const cursor = state.selection.main.head;

    for (const block of detectFullLineMathBlocks(state)) {
        if (cursor >= block.from && cursor <= block.to) {
            continue;
        }

        const key = `${block.prefix}:${block.content}`;
        const info = renderedBlocks.get(key);
        if (!info?.renderedHtml) {
            continue;
        }

        builder.add(
            block.lineFrom,
            block.lineTo,
            Decoration.replace({
                widget: new MathWidget(info.renderedHtml, block.prefix, block.content, 'block'),
                block: true,
            }),
        );
    }

    return builder.finish();
}

function createFullLineMathField(
    getRenderedBlocks: () => Map<string, RenderableBlockInfo>,
): StateField<DecorationSet> {
    return StateField.define<DecorationSet>({
        create(state) {
            return buildFullLineMathDecorations(state, getRenderedBlocks());
        },
        update(value, tr) {
            if (
                tr.docChanged
                || tr.selection
                || tr.effects.some((effect) => effect.is(refreshRenderedBlocksEffect))
            ) {
                return buildFullLineMathDecorations(tr.state, getRenderedBlocks());
            }
            return value;
        },
        provide: (field) => EditorView.decorations.from(field),
    });
}

function createMathAwareLineNumberSetup(): Extension[] {
    return [
        lineNumbers(),
        lineNumberWidgetMarker.of((view: EditorView, widget: WidgetType, block: BlockInfo) => {
            if (!(widget instanceof MathWidget) || widget.displayMode !== 'block') {
                return null;
            }
            const lineNumber = String(view.state.doc.lineAt(block.from).number);
            return new RichLineNumberWidgetMarker(lineNumber, block.height);
        }),
    ];
}

function shouldRefreshGutterMarkers(update: ViewUpdate): boolean {
    return update.docChanged
        || update.transactions.some((transaction) =>
            transaction.effects.some((effect) => effect.is(refreshRenderedBlocksEffect)));
}

function buildTestRunMarkers(
    state: EditorState,
    tests: RichEditorTestBlock[],
): RangeSetBuilder<GutterMarker> {
    const builder = new RangeSetBuilder<GutterMarker>();
    for (const test of tests) {
        const lineNumber = test.line + 1;
        if (lineNumber < 1 || lineNumber > state.doc.lines) {
            continue;
        }
        const line = state.doc.line(lineNumber);
        builder.add(line.from, line.from, new TestRunGutterMarker(test));
    }
    return builder;
}

function createTestRunGutter(
    getTests: () => RichEditorTestBlock[],
    onRunTest: (test: RichEditorTestBlock) => void,
): Extension {
    return gutter({
        class: 'cm-test-run-gutter',
        markers(view) {
            return buildTestRunMarkers(view.state, getTests()).finish();
        },
        lineMarkerChange(update) {
            return shouldRefreshGutterMarkers(update);
        },
        initialSpacer() {
            return new TestRunGutterMarker(null);
        },
        domEventHandlers: {
            mousedown(view, line, event) {
                const test = getTests().find((candidate) => candidate.line === view.state.doc.lineAt(line.from).number - 1);
                if (!test) {
                    return false;
                }
                event.preventDefault();
                onRunTest(test);
                return true;
            },
        },
    });
}

function buildBreakpointMarkers(
    state: EditorState,
    markers: RichEditorMarkers,
): RangeSetBuilder<GutterMarker> {
    const builder = new RangeSetBuilder<GutterMarker>();
    const activeBreakpoints = new Set(markers.breakpoints);

    for (let lineNumber = 1; lineNumber <= state.doc.lines; lineNumber += 1) {
        const line = state.doc.line(lineNumber);
        if (activeBreakpoints.has(lineNumber - 1)) {
            builder.add(line.from, line.from, new BreakpointGutterMarker(true));
        }
    }

    return builder;
}

function createBreakpointGutter(
    getMarkers: () => RichEditorMarkers,
    onToggleBreakpoint: (line: number) => void,
): Extension {
    return gutter({
        class: 'cm-breakpoint-gutter',
        markers(view) {
            return buildBreakpointMarkers(view.state, getMarkers()).finish();
        },
        lineMarkerChange(update) {
            return shouldRefreshGutterMarkers(update);
        },
        initialSpacer() {
            return new BreakpointGutterMarker(false);
        },
        domEventHandlers: {
            mousedown(view, line, event) {
                event.preventDefault();
                onToggleBreakpoint(view.state.doc.lineAt(line.from).number - 1);
                return true;
            },
        },
    });
}

function isIdentifierChar(char: string | undefined): boolean {
    return !!char && /[A-Za-z0-9_]/.test(char);
}

function readIdentifierAt(state: EditorState, pos: number): { word: string; from: number; to: number } | null {
    const line = state.doc.lineAt(pos);
    const localPos = pos - line.from;
    const text = line.text;

    let start = localPos;
    if (!isIdentifierChar(text[start]) && isIdentifierChar(text[start - 1])) {
        start -= 1;
    }
    if (!isIdentifierChar(text[start])) {
        return null;
    }

    let end = start;
    while (start > 0 && isIdentifierChar(text[start - 1])) {
        start -= 1;
    }
    while (end < text.length && isIdentifierChar(text[end])) {
        end += 1;
    }

    return {
        word: text.slice(start, end),
        from: line.from + start,
        to: line.from + end,
    };
}

function attachHoverOverlay(
    view: EditorView,
    parent: HTMLElement,
    getSymbols: () => RichEditorSymbol[],
): () => void {
    const tooltip = document.createElement('div');
    tooltip.className = 'simple-rich-hover-tooltip';
    tooltip.hidden = true;
    parent.appendChild(tooltip);

    const hide = () => {
        tooltip.hidden = true;
    };

    const onMouseMove = (event: MouseEvent) => {
        const pos = view.posAtCoords({ x: event.clientX, y: event.clientY });
        if (pos === null) {
            hide();
            return;
        }

        const ident = readIdentifierAt(view.state, pos);
        if (!ident) {
            hide();
            return;
        }

        const symbol = getSymbols().find((candidate) => candidate.name === ident.word);
        if (!symbol) {
            hide();
            return;
        }

        tooltip.innerHTML = `
            <strong>${symbol.name}</strong>
            <div>${symbol.detail} · ${symbol.kind}</div>
            <div>line ${symbol.line + 1}</div>
        `;

        const parentRect = parent.getBoundingClientRect();
        tooltip.style.left = `${event.clientX - parentRect.left + 12}px`;
        tooltip.style.top = `${event.clientY - parentRect.top + 16}px`;
        tooltip.hidden = false;
    };

    view.dom.addEventListener('mousemove', onMouseMove);
    view.dom.addEventListener('mouseleave', hide);
    view.dom.addEventListener('mousedown', hide);

    return () => {
        view.dom.removeEventListener('mousemove', onMouseMove);
        view.dom.removeEventListener('mouseleave', hide);
        view.dom.removeEventListener('mousedown', hide);
        tooltip.remove();
    };
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
    '.cm-line': {
        paddingTop: '0',
        paddingBottom: '0',
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
        padding: '1px 8px',
        margin: '0',
        borderRadius: '4px',
        backgroundColor: 'transparent',
        border: '1px solid var(--simple-rich-block-border)',
        verticalAlign: 'middle',
        cursor: 'pointer',
    },
    '.cm-math-widget-block': {
        display: 'flex',
        width: 'fit-content',
        maxWidth: '100%',
        margin: '0',
        paddingTop: '0',
        paddingBottom: '0',
        minHeight: '0',
    },
    '.cm-math-widget-block .katex-display': {
        margin: '0',
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
    '.cm-breakpoint-gutter, .cm-test-run-gutter': {
        width: '16px',
        minWidth: '16px',
    },
    '.cm-breakpoint-gutter .cm-gutterElement, .cm-test-run-gutter .cm-gutterElement': {
        width: '16px',
        padding: '0 2px',
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
    },
    '.cm-test-gutter-icon': {
        display: 'inline-block',
        width: '0',
        height: '0',
        borderTop: '4px solid transparent',
        borderBottom: '4px solid transparent',
        borderLeft: '7px solid var(--vscode-testing-runAction, var(--vscode-debugIcon-startForeground, var(--vscode-terminal-ansiGreen, #89d185)))',
        opacity: '0.95',
    },
    '.cm-test-gutter-icon-spacer': {
        borderLeftColor: 'transparent',
        opacity: '0',
    },
    '.cm-breakpoint-gutter-icon': {
        display: 'inline-block',
        width: '8px',
        height: '8px',
        borderRadius: '50%',
        backgroundColor: 'transparent',
    },
    '.cm-breakpoint-gutter-icon-active': {
        backgroundColor: 'var(--vscode-debugIcon-breakpointForeground, var(--vscode-editorError-foreground, #e51400))',
        boxShadow: '0 0 0 1px color-mix(in srgb, black 15%, transparent)',
    },
    '.cm-breakpoint-gutter-icon-spacer': {
        backgroundColor: 'transparent',
    },
    '.simple-rich-hover-tooltip': {
        position: 'absolute',
        zIndex: '20',
        minWidth: '140px',
        maxWidth: '240px',
        padding: '8px 10px',
        borderRadius: '6px',
        border: '1px solid color-mix(in srgb, var(--vscode-editorHoverWidget-border) 70%, transparent)',
        backgroundColor: 'var(--vscode-editorHoverWidget-background)',
        color: 'var(--vscode-editorHoverWidget-foreground)',
        boxShadow: '0 6px 20px color-mix(in srgb, black 25%, transparent)',
        pointerEvents: 'none',
        fontSize: '12px',
        lineHeight: '1.4',
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
    symbolsRef: { current: RichEditorSymbol[] },
    testsRef: { current: RichEditorTestBlock[] },
    markersRef: { current: RichEditorMarkers },
    onEdit: (text: string, selStart: number, selEnd: number) => void,
    onSelectionChange: (selStart: number, selEnd: number) => void,
    onRunTest: (test: RichEditorTestBlock) => void,
    onToggleBreakpoint: (line: number) => void,
): {
    view: EditorView;
    refreshDecorations: () => void;
    setDoc: (text: string, selStart?: number, selEnd?: number) => void;
    enableHoverOverlay: () => void;
} {
    let isApplyingSync = false;
    let editTimer: ReturnType<typeof setTimeout> | null = null;
    let hoverCleanup: (() => void) | null = null;

    const decorationPlugin = createDecorationPlugin(() => renderedBlocksRef.current);
    const fullLineMathField = ENABLE_FULL_LINE_BLOCK_MATH
        ? createFullLineMathField(() => renderedBlocksRef.current)
        : null;
    const testRunGutter = ENABLE_TEST_LINE_WIDGETS
        ? createTestRunGutter(() => testsRef.current, onRunTest)
        : null;
    const breakpointGutter = createBreakpointGutter(() => markersRef.current, onToggleBreakpoint);

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
        breakpointGutter,
        ...(testRunGutter ? [testRunGutter] : []),
        ...createMathAwareLineNumberSetup(),
        ...(fullLineMathField ? [fullLineMathField] : []),
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

    const state = EditorState.create({
        doc: initialText,
        extensions,
    });
    const view = new EditorView({
        state,
        parent,
    });
    return {
        view,

        refreshDecorations() {
            view.dispatch({
                effects: [refreshRenderedBlocksEffect.of()],
            });
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

        enableHoverOverlay() {
            if (!ENABLE_SYMBOL_HOVER || hoverCleanup || symbolsRef.current.length === 0) {
                return;
            }
            try {
                hoverCleanup = attachHoverOverlay(view, parent, () => symbolsRef.current);
            } catch (error) {
                console.error('Simple Rich Editor: hover overlay disabled after initialization failure', error);
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
    const symbolsRef: { current: RichEditorSymbol[] } = { current: [] };
    const testsRef: { current: RichEditorTestBlock[] } = { current: [] };
    const markersRef: { current: RichEditorMarkers } = { current: { breakpoints: [] } };

    let editor: ReturnType<typeof createEditor> | null = null;

    function initEditor(text: string, selStart: number, selEnd: number) {
        editor = createEditor(
            editorContainer!,
            text,
            renderedBlocksRef,
            symbolsRef,
            testsRef,
            markersRef,
            (source, sStart, sEnd) => {
                vscode.postMessage({ type: 'editAll', source, selectionStart: sStart, selectionEnd: sEnd });
            },
            (sStart, sEnd) => {
                vscode.postMessage({ type: 'selectionChanged', selectionStart: sStart, selectionEnd: sEnd });
            },
            (test) => {
                vscode.postMessage({
                    type: 'runTestFromLine',
                    line: test.line,
                    kind: test.kind,
                    label: test.label,
                });
            },
            (line) => {
                vscode.postMessage({
                    type: 'toggleBreakpointFromLine',
                    line,
                });
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
            renderedBlocksRef.current.clear();
            symbolsRef.current = msg.symbols ?? [];
            testsRef.current = msg.tests ?? [];
            markersRef.current = msg.markers ?? { breakpoints: [] };
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
            editor!.enableHoverOverlay();
            editor!.refreshDecorations();
        }
    });

    // Request initial state
    vscode.postMessage({ type: 'ready' });
}

(globalThis as typeof globalThis & { RichEditorWebview?: { boot: typeof boot } }).RichEditorWebview = { boot };
