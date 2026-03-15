/* ============================================
   Internationalization (i18n) Module
   ============================================ */

const I18N = {
    currentLang: 'ko',
    translations: {},

    async init() {
        await Promise.all([
            this.loadLang('ko'),
            this.loadLang('en'),
            this.loadLang('ja'),
        ]);

        // Restore saved language preference
        const saved = localStorage.getItem('hair_changer_lang');
        if (saved && this.translations[saved]) {
            this.currentLang = saved;
        }

        this.apply();
        this.bindSwitcher();
    },

    async loadLang(lang) {
        try {
            const resp = await fetch(`i18n/${lang}.json`);
            if (!resp.ok) throw new Error(`HTTP ${resp.status}`);
            this.translations[lang] = await resp.json();
        } catch (e) {
            console.warn(`[i18n] Failed to load ${lang} translations:`, e.message);
        }
    },

    setLang(lang) {
        if (!this.translations[lang]) return;
        this.currentLang = lang;
        document.documentElement.lang = lang;
        localStorage.setItem('hair_changer_lang', lang);
        this.apply();
        this.updateSwitcher();
    },

    t(key) {
        const trans = this.translations[this.currentLang];
        if (trans && trans[key] !== undefined) return trans[key];
        // Fallback to English
        const en = this.translations['en'];
        if (en && en[key] !== undefined) return en[key];
        // Fallback to Korean
        const ko = this.translations['ko'];
        if (ko && ko[key] !== undefined) return ko[key];
        return key;
    },

    apply() {
        document.querySelectorAll('[data-i18n]').forEach(el => {
            const key = el.getAttribute('data-i18n');
            const translated = this.t(key);
            if (translated !== key || el.textContent === '') {
                el.textContent = translated;
            }
        });

        // Update document title
        const title = this.t('page_title');
        if (title !== 'page_title') {
            document.title = title;
        }
    },

    bindSwitcher() {
        const buttons = document.querySelectorAll('.lang-btn');
        buttons.forEach(btn => {
            btn.addEventListener('click', () => {
                const lang = btn.getAttribute('data-lang');
                this.setLang(lang);
            });
        });
        this.updateSwitcher();
    },

    updateSwitcher() {
        document.querySelectorAll('.lang-btn').forEach(btn => {
            const lang = btn.getAttribute('data-lang');
            btn.classList.toggle('active', lang === this.currentLang);
        });
    }
};
