/**
 * CodeMirror 6 widget for rendered math blocks.
 * Displays KaTeX HTML at natural height (variable line height).
 */

import { WidgetType } from '@codemirror/view';

export class MathWidget extends WidgetType {
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

        // Prefix indicator for loss/nograd
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
