/* ============================================
   Before/After Comparison Slider
   Mouse & touch drag support
   ============================================ */

const Slider = {
    slider: null,
    handle: null,
    afterEl: null,
    isDragging: false,
    sliderRect: null,

    init() {
        this.slider = document.getElementById('comparison-slider');
        this.handle = document.getElementById('comparison-handle');
        this.afterEl = this.slider ? this.slider.querySelector('.comparison-after') : null;

        if (!this.slider || !this.handle || !this.afterEl) return;

        // Mouse events
        this.slider.addEventListener('mousedown', (e) => this.startDrag(e));
        document.addEventListener('mousemove', (e) => this.onDrag(e));
        document.addEventListener('mouseup', () => this.endDrag());

        // Touch events
        this.slider.addEventListener('touchstart', (e) => this.startDrag(e), { passive: false });
        document.addEventListener('touchmove', (e) => this.onDrag(e), { passive: false });
        document.addEventListener('touchend', () => this.endDrag());

        // Set initial position to 50%
        this.setPosition(50);
    },

    startDrag(e) {
        e.preventDefault();
        this.isDragging = true;
        this.sliderRect = this.slider.getBoundingClientRect();
        this.slider.classList.add('dragging');
        this.onDrag(e);
    },

    onDrag(e) {
        if (!this.isDragging) return;

        let clientX;
        if (e.type.startsWith('touch')) {
            clientX = e.touches[0].clientX;
        } else {
            clientX = e.clientX;
        }

        if (!this.sliderRect) {
            this.sliderRect = this.slider.getBoundingClientRect();
        }

        const x = clientX - this.sliderRect.left;
        const width = this.sliderRect.width;
        let percent = (x / width) * 100;

        // Clamp between 2% and 98%
        percent = Math.max(2, Math.min(98, percent));

        this.setPosition(percent);
    },

    endDrag() {
        if (!this.isDragging) return;
        this.isDragging = false;
        this.slider.classList.remove('dragging');
        this.sliderRect = null;
    },

    setPosition(percent) {
        if (!this.afterEl || !this.handle) return;
        this.afterEl.style.clipPath = `inset(0 0 0 ${percent}%)`;
        this.handle.style.left = `${percent}%`;
    },

    setImages(beforeSrc, afterSrc) {
        const beforeImg = document.getElementById('result-before');
        const afterImg = document.getElementById('result-after');

        if (beforeImg) beforeImg.src = beforeSrc;
        if (afterImg) afterImg.src = afterSrc;

        // Reset to 50%
        this.setPosition(50);
    },

    show() {
        const section = document.getElementById('result-section');
        if (section) {
            section.classList.remove('hidden');
            // Scroll into view smoothly
            setTimeout(() => {
                section.scrollIntoView({ behavior: 'smooth', block: 'start' });
            }, 100);
        }
    },

    hide() {
        const section = document.getElementById('result-section');
        if (section) section.classList.add('hidden');
    }
};
