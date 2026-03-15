/* ============================================
   Style Gallery Module
   Load presets, render cards, filter
   ============================================ */

const Gallery = {
    presets: [],
    currentCategory: 'all',
    selectedPreset: null,

    init() {
        this.loadPresets();
        this.bindTabs();
        this.render();
    },

    loadPresets() {
        // Built-in gallery presets
        this.presets = [
            {
                id: 'short-bob',
                name_ko: '단발 보브컷',
                name_en: 'Short Bob Cut',
                name_ja: 'ショートボブ',
                categories: ['short'],
                tags: ['short', 'bob'],
                options: { target_length: 'short', hair_type: 'straight', color: 'natural', bangs: 'none' },
                color: '#E0E7FF'
            },
            {
                id: 'curtain-bangs-medium',
                name_ko: '커튼뱅 미디엄',
                name_en: 'Curtain Bangs Medium',
                name_ja: 'カーテンバング ミディアム',
                categories: ['medium'],
                tags: ['medium', 'bangs'],
                options: { target_length: 'medium', hair_type: 'straight', color: 'natural', bangs: 'curtain' },
                color: '#FCE7F3'
            },
            {
                id: 'ash-brown-wave',
                name_ko: '애쉬브라운 웨이브',
                name_en: 'Ash Brown Wave',
                name_ja: 'アッシュブラウン ウェーブ',
                categories: ['medium', 'color'],
                tags: ['medium', 'color', 'wave'],
                options: { target_length: 'medium', hair_type: 'wavy', color: 'ash_brown', bangs: 'side', dye: true },
                color: '#FEF3C7'
            },
            {
                id: 'long-layered',
                name_ko: '롱 레이어드',
                name_en: 'Long Layered',
                name_ja: 'ロング レイヤード',
                categories: ['long'],
                tags: ['long', 'layered'],
                options: { target_length: 'long', hair_type: 'straight', color: 'natural', bangs: 'none' },
                color: '#DBEAFE'
            },
            {
                id: 'platinum-pixie',
                name_ko: '플래티넘 픽시컷',
                name_en: 'Platinum Pixie',
                name_ja: 'プラチナ ピクシー',
                categories: ['short', 'color'],
                tags: ['short', 'color', 'platinum'],
                options: { target_length: 'short', hair_type: 'straight', color: 'platinum', bangs: 'side', dye: true },
                color: '#F3E8FF'
            },
            {
                id: 'korean-perm',
                name_ko: '한국식 S컬 펌',
                name_en: 'Korean S-Curl Perm',
                name_ja: '韓国式 Sカール パーマ',
                categories: ['medium', 'perm'],
                tags: ['medium', 'perm', 'curl'],
                options: { target_length: 'medium', hair_type: 'wavy', color: 'natural', bangs: 'curtain', perm: true },
                color: '#D1FAE5'
            },
            {
                id: 'balayage-long',
                name_ko: '발라야쥬 롱헤어',
                name_en: 'Balayage Long Hair',
                name_ja: 'バレイヤージュ ロングヘア',
                categories: ['long', 'color'],
                tags: ['long', 'color', 'balayage'],
                options: { target_length: 'long', hair_type: 'wavy', color: 'ash_brown', bangs: 'none', treatments: ['balayage'] },
                color: '#FEF3C7'
            },
            {
                id: 'red-curly-medium',
                name_ko: '레드 곱슬 미디엄',
                name_en: 'Red Curly Medium',
                name_ja: 'レッド カーリー ミディアム',
                categories: ['medium', 'color', 'perm'],
                tags: ['medium', 'color', 'curly', 'red'],
                options: { target_length: 'medium', hair_type: 'curly', color: 'red', bangs: 'blunt', dye: true, perm: true },
                color: '#FEE2E2'
            },
            {
                id: 'blonde-bob',
                name_ko: '금발 보브',
                name_en: 'Blonde Bob',
                name_ja: 'ブロンド ボブ',
                categories: ['short', 'color'],
                tags: ['short', 'color', 'blonde'],
                options: { target_length: 'short', hair_type: 'straight', color: 'blonde', bangs: 'blunt', dye: true },
                color: '#FEF9C3'
            },
            {
                id: 'highlights-long-wave',
                name_ko: '하이라이트 롱 웨이브',
                name_en: 'Highlights Long Wave',
                name_ja: 'ハイライト ロング ウェーブ',
                categories: ['long', 'color'],
                tags: ['long', 'color', 'highlights', 'wave'],
                options: { target_length: 'long', hair_type: 'wavy', color: 'natural', bangs: 'curtain', treatments: ['highlights'] },
                color: '#ECFDF5'
            },
            {
                id: 'natural-perm-short',
                name_ko: '내추럴 펌 숏',
                name_en: 'Natural Perm Short',
                name_ja: 'ナチュラルパーマ ショート',
                categories: ['short', 'perm'],
                tags: ['short', 'perm', 'natural'],
                options: { target_length: 'short', hair_type: 'curly', color: 'natural', bangs: 'none', perm: true },
                color: '#D1FAE5'
            },
            {
                id: 'c-curl-perm',
                name_ko: 'C컬 펌 미디엄',
                name_en: 'C-Curl Perm Medium',
                name_ja: 'Cカール パーマ ミディアム',
                categories: ['medium', 'perm'],
                tags: ['medium', 'perm', 'c-curl'],
                options: { target_length: 'medium', hair_type: 'wavy', color: 'natural', bangs: 'side', perm: true },
                color: '#E0E7FF'
            }
        ];
    },

    bindTabs() {
        const tabContainer = document.getElementById('gallery-tabs');
        if (!tabContainer) return;

        tabContainer.addEventListener('click', (e) => {
            const btn = e.target.closest('.tab-btn');
            if (!btn) return;

            const category = btn.getAttribute('data-category');
            this.currentCategory = category;

            // Update active tab
            tabContainer.querySelectorAll('.tab-btn').forEach(b => b.classList.remove('active'));
            btn.classList.add('active');

            this.render();
        });
    },

    getFiltered() {
        if (this.currentCategory === 'all') return this.presets;
        return this.presets.filter(p => p.categories.includes(this.currentCategory));
    },

    getPresetName(preset) {
        const lang = I18N.currentLang;
        if (lang === 'ko') return preset.name_ko;
        if (lang === 'ja') return preset.name_ja;
        return preset.name_en;
    },

    render() {
        const grid = document.getElementById('gallery-grid');
        if (!grid) return;

        const filtered = this.getFiltered();

        if (filtered.length === 0) {
            grid.innerHTML = `
                <div class="gallery-empty">
                    <div class="gallery-empty-icon">💇</div>
                    <p>${I18N.t('gallery_empty')}</p>
                </div>
            `;
            return;
        }

        grid.innerHTML = filtered.map(preset => `
            <div class="gallery-card ${this.selectedPreset === preset.id ? 'selected' : ''}"
                 data-preset-id="${preset.id}">
                <div class="gallery-card-img-wrapper">
                    <div class="gallery-card-img" style="background: ${preset.color}; display: flex; align-items: center; justify-content: center; font-size: 2.5rem; aspect-ratio: 3/4;">
                        💇
                    </div>
                </div>
                <div class="gallery-card-info">
                    <div class="gallery-card-name">${this.getPresetName(preset)}</div>
                    <div class="gallery-card-tags">
                        ${preset.tags.map(tag => {
                            let cls = 'gallery-tag';
                            if (['color', 'blonde', 'red', 'platinum', 'ash_brown', 'balayage', 'highlights'].includes(tag)) cls += ' tag-color';
                            else if (['perm', 'curl', 'curly', 'c-curl'].includes(tag)) cls += ' tag-perm';
                            else if (['short', 'medium', 'long', 'layered'].includes(tag)) cls += ' tag-length';
                            return `<span class="${cls}">${I18N.t('tag_' + tag) || tag}</span>`;
                        }).join('')}
                    </div>
                </div>
            </div>
        `).join('');

        // Bind card clicks
        grid.querySelectorAll('.gallery-card').forEach(card => {
            card.addEventListener('click', () => {
                const id = card.getAttribute('data-preset-id');
                this.selectPreset(id);
            });
        });
    },

    selectPreset(id) {
        const preset = this.presets.find(p => p.id === id);
        if (!preset) return;

        // Toggle selection
        if (this.selectedPreset === id) {
            this.selectedPreset = null;
        } else {
            this.selectedPreset = id;
            // Apply preset options
            Options.applyPreset(preset.options);
        }

        this.render();
    }
};
