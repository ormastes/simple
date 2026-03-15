/* ============================================
   Main Application
   Initialize modules, wire events, manage state
   ============================================ */

const App = {
    isGenerating: false,
    lastResultURL: null,

    async init() {
        // Initialize all modules
        await I18N.init();
        Upload.init();
        Options.init();
        Slider.init();
        Gallery.init();
        API.init('');

        // Bind events
        this.bindGenerateButton();
        this.bindDownloadButton();
        this.bindRetryButton();

        // Initial state
        this.updateGenerateButton();

        console.log('[HairChanger] App initialized');
    },

    bindGenerateButton() {
        const btn = document.getElementById('generate-btn');
        if (!btn) return;

        btn.addEventListener('click', () => {
            if (!this.isGenerating) {
                this.generate();
            }
        });
    },

    bindDownloadButton() {
        const btn = document.getElementById('download-btn');
        if (!btn) return;

        btn.addEventListener('click', () => {
            if (this.lastResultURL) {
                API.downloadResult(this.lastResultURL, 'hair_changer_result.png');
            }
        });
    },

    bindRetryButton() {
        const btn = document.getElementById('retry-btn');
        if (!btn) return;

        btn.addEventListener('click', () => {
            if (!this.isGenerating) {
                this.generate();
            }
        });
    },

    updateGenerateButton() {
        const btn = document.getElementById('generate-btn');
        if (!btn) return;

        const hasFace = Upload.hasFiles();
        btn.disabled = !hasFace || this.isGenerating;
    },

    setGenerating(state) {
        this.isGenerating = state;
        const btn = document.getElementById('generate-btn');
        if (!btn) return;

        const textEl = btn.querySelector('.btn-text');
        const loadingEl = btn.querySelector('.btn-loading');

        if (state) {
            textEl.classList.add('hidden');
            loadingEl.classList.remove('hidden');
            btn.disabled = true;
        } else {
            textEl.classList.remove('hidden');
            loadingEl.classList.add('hidden');
            this.updateGenerateButton();
        }
    },

    async generate() {
        if (this.isGenerating) return;

        const faceFile = Upload.getFaceFile();
        if (!faceFile) {
            alert(I18N.t('error_no_face'));
            return;
        }

        const hairFile = Upload.getHairFile();
        const options = Options.getAll();

        this.setGenerating(true);

        try {
            const result = await API.generate(faceFile, hairFile, options);

            if (result.job_id) {
                // Async processing — poll for result
                const finalResult = await API.pollForResult(result.job_id, (status) => {
                    // Could update progress UI here
                    console.log('[HairChanger] Status:', status.state);
                });
                this.showResult(finalResult);
            } else if (result.result_image) {
                // Direct result
                this.showResult(result);
            } else {
                throw new Error(I18N.t('error_unexpected'));
            }
        } catch (error) {
            console.error('[HairChanger] Generation failed:', error);
            alert(I18N.t('error_generation_failed') + '\n' + error.message);
        } finally {
            this.setGenerating(false);
        }
    },

    showResult(result) {
        const beforeSrc = Upload.getFaceDataURL();
        const afterSrc = result.result_image || result.image_url;

        if (!afterSrc) {
            console.error('[HairChanger] No result image in response');
            return;
        }

        this.lastResultURL = afterSrc;

        // Set images in slider
        Slider.setImages(beforeSrc, afterSrc);
        Slider.show();
    }
};

// Start when DOM is ready
document.addEventListener('DOMContentLoaded', () => {
    App.init();
});
