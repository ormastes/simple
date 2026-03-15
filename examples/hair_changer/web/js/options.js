/* ============================================
   Hair Options Module
   Collect options, check feasibility
   ============================================ */

const Options = {
    init() {
        // Bind change listeners to all inputs
        const inputs = document.querySelectorAll(
            '.options-section input[type="radio"], .options-section input[type="checkbox"]'
        );
        inputs.forEach(input => {
            input.addEventListener('change', () => {
                this.checkFeasibility();
                if (typeof App !== 'undefined' && App.updateGenerateButton) {
                    App.updateGenerateButton();
                }
            });
        });
    },

    getAll() {
        const options = {};

        // Radio buttons
        const radios = document.querySelectorAll('.options-section input[type="radio"]:checked');
        radios.forEach(radio => {
            options[radio.name] = radio.value;
        });

        // Checkboxes
        options.treatments = [];
        const checkboxes = document.querySelectorAll('.options-section input[type="checkbox"]:checked');
        checkboxes.forEach(cb => {
            if (cb.name === 'dye') {
                options.dye = true;
            } else if (cb.name === 'perm') {
                options.perm = true;
            } else if (cb.name === 'treatment') {
                options.treatments.push(cb.value);
            }
        });

        return options;
    },

    buildPromptString() {
        const opts = this.getAll();
        const parts = [];

        // Length
        if (opts.target_length) {
            const lengthMap = {
                short: 'short hair',
                medium: 'medium length hair',
                long: 'long hair'
            };
            parts.push(lengthMap[opts.target_length] || opts.target_length);
        }

        // Type
        if (opts.hair_type) {
            const typeMap = {
                straight: 'straight',
                wavy: 'wavy',
                curly: 'curly'
            };
            parts.push(typeMap[opts.hair_type] || opts.hair_type);
        }

        // Color
        if (opts.color && opts.color !== 'natural') {
            const colorMap = {
                blonde: 'blonde',
                ash_brown: 'ash brown',
                red: 'red',
                platinum: 'platinum blonde'
            };
            parts.push(colorMap[opts.color] || opts.color);
        }

        // Bangs
        if (opts.bangs && opts.bangs !== 'none') {
            const bangsMap = {
                curtain: 'curtain bangs',
                side: 'side bangs',
                blunt: 'blunt bangs'
            };
            parts.push(bangsMap[opts.bangs] || opts.bangs);
        }

        // Treatments
        if (opts.dye) parts.push('hair dye');
        if (opts.perm) parts.push('perm');
        if (opts.treatments.includes('highlights')) parts.push('highlights');
        if (opts.treatments.includes('balayage')) parts.push('balayage');

        return parts.join(', ');
    },

    checkFeasibility() {
        const opts = this.getAll();
        const warningEl = document.getElementById('feasibility-warning');
        const messageEl = document.getElementById('feasibility-message');

        const warnings = [];

        // Check shaved to long
        if (opts.current_length === 'shaved' && opts.target_length === 'long') {
            warnings.push(I18N.t('warn_shaved_to_long'));
        }

        // Check perm on very short hair
        if (opts.perm && opts.target_length === 'short' && opts.current_length === 'shaved') {
            warnings.push(I18N.t('warn_perm_short'));
        }

        // Check multiple treatments
        const treatmentCount = (opts.dye ? 1 : 0) + (opts.perm ? 1 : 0) + opts.treatments.length;
        if (treatmentCount >= 3) {
            warnings.push(I18N.t('warn_many_treatments'));
        }

        if (warnings.length > 0) {
            messageEl.textContent = warnings.join(' ');
            warningEl.classList.remove('hidden');
        } else {
            warningEl.classList.add('hidden');
        }
    },

    applyPreset(preset) {
        // Apply a gallery preset
        if (preset.target_length) {
            const radio = document.querySelector(`input[name="target_length"][value="${preset.target_length}"]`);
            if (radio) radio.checked = true;
        }
        if (preset.hair_type) {
            const radio = document.querySelector(`input[name="hair_type"][value="${preset.hair_type}"]`);
            if (radio) radio.checked = true;
        }
        if (preset.color) {
            const radio = document.querySelector(`input[name="color"][value="${preset.color}"]`);
            if (radio) radio.checked = true;
        }
        if (preset.bangs) {
            const radio = document.querySelector(`input[name="bangs"][value="${preset.bangs}"]`);
            if (radio) radio.checked = true;
        }

        // Checkboxes - reset all first
        document.querySelectorAll('.options-section input[type="checkbox"]').forEach(cb => {
            cb.checked = false;
        });

        if (preset.dye) {
            const cb = document.querySelector('input[name="dye"]');
            if (cb) cb.checked = true;
        }
        if (preset.perm) {
            const cb = document.querySelector('input[name="perm"]');
            if (cb) cb.checked = true;
        }
        if (preset.treatments) {
            preset.treatments.forEach(t => {
                const cb = document.querySelector(`input[name="treatment"][value="${t}"]`);
                if (cb) cb.checked = true;
            });
        }

        this.checkFeasibility();
    }
};
