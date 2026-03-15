/* ============================================
   Image Upload Module
   Handles file selection, drag & drop, preview
   ============================================ */

const Upload = {
    faceFile: null,
    hairFile: null,

    init() {
        this.setupUploadBox('face');
        this.setupUploadBox('hair');
    },

    setupUploadBox(type) {
        const box = document.getElementById(`${type}-upload`);
        const input = document.getElementById(`${type}-input`);
        const preview = document.getElementById(`${type}-preview`);
        const placeholder = document.getElementById(`${type}-placeholder`);

        // Click to open file picker
        box.addEventListener('click', (e) => {
            if (e.target === input) return;
            input.click();
        });

        // File input change
        input.addEventListener('change', (e) => {
            const file = e.target.files[0];
            if (file) this.handleFile(type, file);
        });

        // Drag & drop
        box.addEventListener('dragenter', (e) => {
            e.preventDefault();
            e.stopPropagation();
            box.classList.add('drag-over');
        });

        box.addEventListener('dragover', (e) => {
            e.preventDefault();
            e.stopPropagation();
            box.classList.add('drag-over');
        });

        box.addEventListener('dragleave', (e) => {
            e.preventDefault();
            e.stopPropagation();
            // Only remove if leaving the box itself
            if (!box.contains(e.relatedTarget)) {
                box.classList.remove('drag-over');
            }
        });

        box.addEventListener('drop', (e) => {
            e.preventDefault();
            e.stopPropagation();
            box.classList.remove('drag-over');

            const files = e.dataTransfer.files;
            if (files.length > 0) {
                const file = files[0];
                if (this.validateFile(file)) {
                    this.handleFile(type, file);
                }
            }
        });
    },

    validateFile(file) {
        // Check if it's an image
        if (!file.type.startsWith('image/')) {
            alert(I18N.t('error_not_image'));
            return false;
        }

        // Max 10MB
        const maxSize = 10 * 1024 * 1024;
        if (file.size > maxSize) {
            alert(I18N.t('error_file_too_large'));
            return false;
        }

        return true;
    },

    handleFile(type, file) {
        if (!this.validateFile(file)) return;

        if (type === 'face') {
            this.faceFile = file;
        } else {
            this.hairFile = file;
        }

        // Show preview
        const preview = document.getElementById(`${type}-preview`);
        const placeholder = document.getElementById(`${type}-placeholder`);
        const box = document.getElementById(`${type}-upload`);
        const reader = new FileReader();

        reader.onload = (e) => {
            preview.src = e.target.result;
            preview.classList.remove('hidden');
            placeholder.classList.add('hidden');
            box.classList.add('has-image');
        };

        reader.readAsDataURL(file);

        // Notify app to update generate button state
        if (typeof App !== 'undefined' && App.updateGenerateButton) {
            App.updateGenerateButton();
        }
    },

    getFaceFile() {
        return this.faceFile;
    },

    getHairFile() {
        return this.hairFile;
    },

    hasFiles() {
        return this.faceFile !== null;
    },

    hasBothFiles() {
        return this.faceFile !== null && this.hairFile !== null;
    },

    getFaceDataURL() {
        const preview = document.getElementById('face-preview');
        return preview.src || null;
    },

    getHairDataURL() {
        const preview = document.getElementById('hair-preview');
        return preview.src || null;
    },

    reset(type) {
        if (type === 'face' || !type) {
            this.faceFile = null;
            const preview = document.getElementById('face-preview');
            const placeholder = document.getElementById('face-placeholder');
            const box = document.getElementById('face-upload');
            const input = document.getElementById('face-input');
            preview.src = '';
            preview.classList.add('hidden');
            placeholder.classList.remove('hidden');
            box.classList.remove('has-image');
            input.value = '';
        }

        if (type === 'hair' || !type) {
            this.hairFile = null;
            const preview = document.getElementById('hair-preview');
            const placeholder = document.getElementById('hair-placeholder');
            const box = document.getElementById('hair-upload');
            const input = document.getElementById('hair-input');
            preview.src = '';
            preview.classList.add('hidden');
            placeholder.classList.remove('hidden');
            box.classList.remove('has-image');
            input.value = '';
        }
    }
};
