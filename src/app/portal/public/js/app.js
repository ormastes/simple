/* Simple Language Portal - Client-side JavaScript */

(function() {
    "use strict";

    /* ==================================================================
       Search Autocomplete
       ================================================================== */

    var searchInput = document.getElementById("search-input");
    var suggestionsBox = null;
    var debounceTimer = null;

    function initSearch() {
        if (!searchInput) return;

        suggestionsBox = document.createElement("div");
        suggestionsBox.className = "search-suggestions";
        suggestionsBox.style.display = "none";
        searchInput.parentElement.style.position = "relative";
        searchInput.parentElement.appendChild(suggestionsBox);

        searchInput.addEventListener("input", function() {
            clearTimeout(debounceTimer);
            var query = searchInput.value.trim();
            if (query.length < 2) {
                hideSuggestions();
                return;
            }
            debounceTimer = setTimeout(function() {
                fetchSuggestions(query);
            }, 250);
        });

        searchInput.addEventListener("blur", function() {
            setTimeout(hideSuggestions, 200);
        });

        searchInput.addEventListener("keydown", function(e) {
            if (e.key === "Escape") {
                hideSuggestions();
            }
        });
    }

    function fetchSuggestions(query) {
        var xhr = new XMLHttpRequest();
        xhr.open("GET", "/api/v1/packages?q=" + encodeURIComponent(query) + "&per_page=5");
        xhr.onload = function() {
            if (xhr.status === 200) {
                try {
                    var data = JSON.parse(xhr.responseText);
                    showSuggestions(data.packages || []);
                } catch (e) {
                    hideSuggestions();
                }
            }
        };
        xhr.onerror = function() {
            hideSuggestions();
        };
        xhr.send();
    }

    function showSuggestions(packages) {
        if (!suggestionsBox) return;
        if (packages.length === 0) {
            hideSuggestions();
            return;
        }

        var html = "";
        for (var i = 0; i < packages.length; i++) {
            var pkg = packages[i];
            html += '<a href="/packages/' + escapeHtml(pkg.name) + '" class="suggestion-item">';
            html += '<span class="suggestion-name">' + escapeHtml(pkg.name) + '</span>';
            if (pkg.description) {
                html += '<span class="suggestion-desc">' + escapeHtml(pkg.description) + '</span>';
            }
            html += '</a>';
        }

        suggestionsBox.innerHTML = html;
        suggestionsBox.style.display = "block";
    }

    function hideSuggestions() {
        if (suggestionsBox) {
            suggestionsBox.style.display = "none";
        }
    }

    /* ==================================================================
       Copy to Clipboard
       ================================================================== */

    window.copyToClipboard = function(text) {
        if (navigator.clipboard) {
            navigator.clipboard.writeText(text).then(function() {
                showCopyFeedback();
            });
        } else {
            var textarea = document.createElement("textarea");
            textarea.value = text;
            textarea.style.position = "fixed";
            textarea.style.opacity = "0";
            document.body.appendChild(textarea);
            textarea.select();
            try {
                document.execCommand("copy");
                showCopyFeedback();
            } catch (e) {
                // Silently fail
            }
            document.body.removeChild(textarea);
        }
    };

    function showCopyFeedback() {
        var btns = document.querySelectorAll(".btn-copy");
        for (var i = 0; i < btns.length; i++) {
            var btn = btns[i];
            var original = btn.textContent;
            btn.textContent = "Copied!";
            (function(b, o) {
                setTimeout(function() { b.textContent = o; }, 1500);
            })(btn, original);
        }
    }

    /* ==================================================================
       Flash Message Auto-dismiss
       ================================================================== */

    function initFlashDismiss() {
        var flashes = document.querySelectorAll(".flash");
        for (var i = 0; i < flashes.length; i++) {
            (function(flash) {
                setTimeout(function() {
                    flash.style.transition = "opacity 0.3s ease";
                    flash.style.opacity = "0";
                    setTimeout(function() {
                        flash.style.display = "none";
                    }, 300);
                }, 5000);
            })(flashes[i]);
        }
    }

    /* ==================================================================
       Form Validation (client-side)
       ================================================================== */

    function initFormValidation() {
        var forms = document.querySelectorAll(".auth-form");
        for (var i = 0; i < forms.length; i++) {
            forms[i].addEventListener("submit", function(e) {
                var passwordInput = this.querySelector('input[name="password"]');
                var confirmInput = this.querySelector('input[name="password_confirm"]');

                if (passwordInput && confirmInput) {
                    if (passwordInput.value !== confirmInput.value) {
                        e.preventDefault();
                        showFormError(this, "Passwords do not match.");
                        return false;
                    }
                }
            });
        }
    }

    function showFormError(form, message) {
        var existing = form.parentElement.querySelector(".flash-error.client-error");
        if (existing) {
            existing.remove();
        }

        var div = document.createElement("div");
        div.className = "flash flash-error client-error";
        div.textContent = message;
        form.parentElement.insertBefore(div, form);
    }

    /* ==================================================================
       Utilities
       ================================================================== */

    function escapeHtml(text) {
        var div = document.createElement("div");
        div.appendChild(document.createTextNode(text));
        return div.innerHTML;
    }

    /* ==================================================================
       CSS for Autocomplete (injected)
       ================================================================== */

    var style = document.createElement("style");
    style.textContent = [
        ".search-suggestions {",
        "  position: absolute;",
        "  top: 100%;",
        "  left: 0;",
        "  right: 0;",
        "  background: white;",
        "  border: 1px solid #e2e8f0;",
        "  border-top: none;",
        "  border-radius: 0 0 4px 4px;",
        "  box-shadow: 0 4px 6px rgba(0,0,0,0.07);",
        "  z-index: 200;",
        "  max-height: 300px;",
        "  overflow-y: auto;",
        "}",
        ".suggestion-item {",
        "  display: block;",
        "  padding: 0.5rem 0.75rem;",
        "  color: #2d3748;",
        "  text-decoration: none;",
        "  border-bottom: 1px solid #f1f5f9;",
        "}",
        ".suggestion-item:hover {",
        "  background: #f8f9fa;",
        "}",
        ".suggestion-name {",
        "  font-weight: 500;",
        "  display: block;",
        "}",
        ".suggestion-desc {",
        "  font-size: 0.8125rem;",
        "  color: #718096;",
        "  display: block;",
        "  white-space: nowrap;",
        "  overflow: hidden;",
        "  text-overflow: ellipsis;",
        "}"
    ].join("\n");
    document.head.appendChild(style);

    /* ==================================================================
       Init
       ================================================================== */

    document.addEventListener("DOMContentLoaded", function() {
        initSearch();
        initFlashDismiss();
        initFormValidation();
    });

})();
