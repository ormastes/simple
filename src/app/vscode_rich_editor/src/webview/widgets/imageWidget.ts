/**
 * CodeMirror 6 widget for rendered images.
 * Replaces img{} blocks with actual <img> elements at natural dimensions.
 */

import { WidgetType } from '@codemirror/view';

export class ImageWidget extends WidgetType {
    constructor(
        readonly uri: string,
        readonly path: string,
    ) {
        super();
    }

    eq(other: ImageWidget): boolean {
        return this.uri === other.uri;
    }

    toDOM(): HTMLElement {
        const wrap = document.createElement('div');
        wrap.className = 'cm-image-widget';

        const img = document.createElement('img');
        img.src = this.uri;
        img.alt = this.path;
        img.style.maxWidth = '100%';
        img.style.maxHeight = '400px';
        img.style.objectFit = 'contain';
        img.draggable = false;

        img.onerror = () => {
            wrap.textContent = `[Image not found: ${this.path}]`;
            wrap.classList.add('cm-image-error');
        };

        wrap.appendChild(img);
        return wrap;
    }

    ignoreEvent(): boolean {
        return false;
    }
}
