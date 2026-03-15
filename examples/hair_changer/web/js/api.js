/* ============================================
   Backend API Module
   Fetch wrapper for hair changer endpoints
   ============================================ */

const API = {
    baseURL: '',

    init(baseURL) {
        // Allow configuring the backend URL
        // Default: same origin (relative paths)
        this.baseURL = baseURL || '';
    },

    async generate(faceFile, hairFile, options) {
        const formData = new FormData();

        // Required: face image
        formData.append('face_image', faceFile);

        // Optional: hair reference image
        if (hairFile) {
            formData.append('hair_reference', hairFile);
        }

        // Options as JSON string
        formData.append('options', JSON.stringify(options));

        // Prompt string
        const prompt = Options.buildPromptString();
        if (prompt) {
            formData.append('prompt', prompt);
        }

        const response = await fetch(`${this.baseURL}/api/generate`, {
            method: 'POST',
            body: formData,
        });

        if (!response.ok) {
            const error = await response.json().catch(() => ({ error: 'Unknown error' }));
            throw new Error(error.error || `HTTP ${response.status}`);
        }

        return await response.json();
    },

    async getStatus(jobId) {
        const response = await fetch(`${this.baseURL}/api/status/${jobId}`);

        if (!response.ok) {
            throw new Error(`HTTP ${response.status}`);
        }

        return await response.json();
    },

    async getResult(jobId) {
        const response = await fetch(`${this.baseURL}/api/result/${jobId}`);

        if (!response.ok) {
            throw new Error(`HTTP ${response.status}`);
        }

        return await response.json();
    },

    async pollForResult(jobId, onProgress) {
        const maxAttempts = 60;  // 60 * 2s = 2 minutes max
        const interval = 2000;

        for (let i = 0; i < maxAttempts; i++) {
            const status = await this.getStatus(jobId);

            if (onProgress) {
                onProgress(status);
            }

            if (status.state === 'completed') {
                return await this.getResult(jobId);
            }

            if (status.state === 'failed') {
                throw new Error(status.error || I18N.t('error_generation_failed'));
            }

            // Wait before next poll
            await new Promise(resolve => setTimeout(resolve, interval));
        }

        throw new Error(I18N.t('error_timeout'));
    },

    async downloadResult(imageURL, filename) {
        const response = await fetch(imageURL);
        const blob = await response.blob();

        const url = URL.createObjectURL(blob);
        const a = document.createElement('a');
        a.href = url;
        a.download = filename || 'hair_result.png';
        document.body.appendChild(a);
        a.click();
        document.body.removeChild(a);
        URL.revokeObjectURL(url);
    },

    async getGalleryPresets() {
        try {
            const response = await fetch(`${this.baseURL}/api/gallery`);
            if (!response.ok) return null;
            return await response.json();
        } catch {
            return null;
        }
    }
};
