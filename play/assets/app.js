/* Play reader — shared by the index page and the worksheet pages. */
(() => {
  "use strict";

  const PAGE = document.body.dataset.page || "index";
  const BASE = document.body.dataset.base || (PAGE === "worksheet" ? "../" : "");
  const DATA = BASE + "data/";
  const SHEET_DIR = PAGE === "worksheet" ? "" : "worksheets/";
  const state = { index: null, sheet: null, cache: new Map(), modulePromises: new Map(), searchRows: [] };

  const $ = (sel, root = document) => root.querySelector(sel);
  const $$ = (sel, root = document) => Array.from(root.querySelectorAll(sel));

  const KEYWORDS = new Set(("example theorem lemma def abbrev instance structure class " +
    "inductive axiom opaque constant import open namespace section end variable universe " +
    "noncomputable set_option attribute where by fun let have show from exact apply refine " +
    "intro intros rw simp simpa rfl trivial calc obtain rcases rintro cases induction " +
    "constructor ext funext congr convert assumption specialize subst at in with if then " +
    "else match do return deriving mutual private protected scoped local unsafe partial").split(/\s+/));

  const STOP_TOKENS = new Set(["x", "y", "z", "n", "m", "k", "p", "q", "f", "g", "h",
    "a", "b", "c", "d", "e", "u", "v", "w", "r", "s", "t", "i", "j", "l", "o",
    "the", "and", "or", "is", "are", "of", "to", "in", "on", "for", "with"]);

  function esc(s) {
    return String(s == null ? "" : s)
      .replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;")
      .replace(/"/g, "&quot;");
  }

  // Classic script shards, not fetch: this is what makes file:// work in
  // Chrome, where fetch/XHR is blocked for local files.
  function loadScript(src) {
    return new Promise((resolve, reject) => {
      const el = document.createElement("script");
      el.src = src;
      el.onload = () => resolve();
      el.onerror = () => reject(new Error("could not load " + src));
      document.head.appendChild(el);
    });
  }

  /* ------------------------- shared module loading ---------------------- */
  // The unit of shared data is the defining module: play/data/modules/<ModulePath>.js
  // holds every card declared in that module, used by any worksheet.

  function hasCard(name) {
    return !!(name && state.index && state.index.card_module &&
      state.index.card_module[name]);
  }

  function getCard(name) {
    return state.cache.get(name) || null;
  }

  async function loadModule(module) {
    if (!module) return;
    if (state.modulePromises.has(module)) return state.modulePromises.get(module);
    const promise = (async () => {
      const path = module.split(".").map(encodeURIComponent).join("/");
      await loadScript(DATA + "modules/" + path + ".js");
      const payload = (window.PLAY_MODULES || {})[module];
      if (!payload) throw new Error("module shard did not register " + module);
      for (const [name, card] of Object.entries(payload.cards || {})) {
        state.cache.set(name, card);
      }
    })();
    state.modulePromises.set(module, promise);
    try {
      await promise;
    } catch (e) {
      state.modulePromises.delete(module);
      throw e;
    }
  }

  async function loadCard(name) {
    if (state.cache.has(name)) return state.cache.get(name);
    const module = state.index.card_module[name];
    if (!module) return null;
    await loadModule(module);
    return state.cache.get(name) || null;
  }

  async function prefetchModules(modules) {
    await Promise.all((modules || []).map((m) =>
      loadModule(m).catch((e) => console.warn("play: module failed", m, e))));
  }

  /* ------------------------------ markdown ------------------------------ */

  function inlineMd(s) {
    s = esc(s);
    s = s.replace(/`([^`]+)`/g, (_, c) => `<code>${c}</code>`);
    s = s.replace(/\*\*([^*]+)\*\*/g, "<strong>$1</strong>");
    s = s.replace(/(^|[^*])\*([^*]+)\*/g, "$1<em>$2</em>");
    s = s.replace(/\[([^\]]+)\]\((https?:[^)\s]+)\)/g,
      (_, t, u) => `<a href="${u}" target="_blank" rel="noopener">${t}</a>`);
    s = s.replace(/&lt;(https?:[^&\s]+)&gt;/g,
      (_, u) => `<a href="${u}" target="_blank" rel="noopener">${u}</a>`);
    return s;
  }

  function md(src) {
    const lines = String(src || "").replace(/\r/g, "").split("\n");
    const out = [];
    let i = 0;
    while (i < lines.length) {
      let line = lines[i];
      if (!line.trim()) { i++; continue; }
      let m = line.match(/^```\s*(\w*)\s*$/);
      if (m) {
        const buf = [];
        i++;
        while (i < lines.length && !/^```\s*$/.test(lines[i])) buf.push(lines[i++]);
        i++;
        out.push(`<pre class="mono">${esc(buf.join("\n"))}</pre>`);
        continue;
      }
      m = line.match(/^(#{1,6})\s+(.*)$/);
      if (m) {
        const level = Math.min(6, m[1].length + 1);
        out.push(`<h${level}>${inlineMd(m[2])}</h${level}>`);
        i++;
        continue;
      }
      if (/^\s*[-*]\s+/.test(line)) {
        const items = [];
        while (i < lines.length && /^\s*[-*]\s+/.test(lines[i])) {
          items.push(`<li>${inlineMd(lines[i].replace(/^\s*[-*]\s+/, ""))}</li>`);
          i++;
        }
        out.push(`<ul>${items.join("")}</ul>`);
        continue;
      }
      if (/^\s*\d+\.\s+/.test(line)) {
        const items = [];
        while (i < lines.length && /^\s*\d+\.\s+/.test(lines[i])) {
          items.push(`<li>${inlineMd(lines[i].replace(/^\s*\d+\.\s+/, ""))}</li>`);
          i++;
        }
        out.push(`<ol>${items.join("")}</ol>`);
        continue;
      }
      if (/^>\s?/.test(line)) {
        const buf = [];
        while (i < lines.length && /^>\s?/.test(lines[i])) {
          buf.push(lines[i].replace(/^>\s?/, ""));
          i++;
        }
        out.push(`<blockquote>${md(buf.join("\n"))}</blockquote>`);
        continue;
      }
      const para = [];
      while (i < lines.length && lines[i].trim() &&
             !/^(#{1,6})\s|^\s*[-*]\s|^\s*\d+\.\s|^>|^```/.test(lines[i])) {
        para.push(lines[i]);
        i++;
      }
      out.push(`<p>${inlineMd(para.join(" "))}</p>`);
    }
    return out.join("\n");
  }

  /* --------------------------- Lean highlighting ------------------------ */

  function highlightLean(code) {
    const re = /(\/-[\s\S]*?-\/)|(--[^\n]*)|("(?:\\.|[^"\\])*")|(\b\d+(?:\.\d+)?\b)|([\p{L}_][\p{L}\p{N}_'₀-₉]*(?:\.[\p{L}_][\p{L}\p{N}_'₀-₉]*)*)/gu;
    let out = "";
    let last = 0;
    let m;
    while ((m = re.exec(code)) !== null) {
      out += esc(code.slice(last, m.index));
      const tok = m[0];
      if (m[1] || m[2]) out += `<span class="tok-com">${esc(tok)}</span>`;
      else if (m[3]) out += `<span class="tok-str">${esc(tok)}</span>`;
      else if (m[4]) out += `<span class="tok-num">${esc(tok)}</span>`;
      else if (KEYWORDS.has(tok)) out += `<span class="tok-kw">${esc(tok)}</span>`;
      else out += `<span class="tok-id" data-tok="${esc(tok)}">${esc(tok)}</span>`;
      last = m.index + tok.length;
    }
    out += esc(code.slice(last));
    return out;
  }

  function resolveName(tok) {
    if (!tok) return null;
    if (hasCard(tok)) return tok;
    const alias = state.index.aliases[tok];
    if (alias && hasCard(alias)) return alias;
    if (STOP_TOKENS.has(tok)) return null;
    const short = tok.includes(".") ? tok.split(".").pop() : tok;
    if (short.length < 2) return null;
    const cands = state.index.by_short[short] || [];
    if (cands.length === 1) return cands[0];
    return null;
  }

  function makeDeclLink(name, text, cls = "") {
    return `<a class="decl ${cls}" href="#decl=${encodeURIComponent(name)}" data-name="${esc(name)}">${esc(text)}</a>`;
  }

  function linkifyCode(root) {
    $$(".tok-id", root).forEach((el) => {
      const tok = el.dataset.tok;
      const name = resolveName(tok);
      if (!name) return;
      const a = document.createElement("a");
      a.href = "#decl=" + encodeURIComponent(name);
      a.className = "decl tok-id";
      a.dataset.name = name;
      a.dataset.tok = tok;
      a.textContent = tok;
      el.replaceWith(a);
    });
  }

  function linkifyProse(root) {
    $$("code", root).forEach((el) => {
      const text = el.textContent.trim();
      const name = resolveName(text);
      if (!name) return;
      el.innerHTML = makeDeclLink(name, text);
    });
    $$("a[href]", root).forEach((a) => {
      if (!/^https?:/.test(a.getAttribute("href"))) return;
      a.target = "_blank";
      a.rel = "noopener";
    });
  }

  function oneLine(s, max = 260) {
    const t = String(s || "").replace(/\s+/g, " ").trim();
    return t.length > max ? t.slice(0, max - 1) + "…" : t;
  }

  /* ------------------------------ cards -------------------------------- */

  function refLink(ref) {
    const text = ref.name;
    const label = hasCard(ref.name)
      ? `<a class="decl" href="#decl=${encodeURIComponent(ref.name)}" data-name="${esc(ref.name)}">${esc(text)}</a>`
      : `<span class="muted" title="not in this build">${esc(text)}</span>`;
    return `<li>${label} <span class="where">${esc(ref.where || "")}</span>
      <span class="mod" title="${esc(ref.module || "")}">${esc((ref.module || "").split(".").slice(-2).join("."))}</span></li>`;
  }

  let cardSeq = 0;
  async function renderCard(name) {
    const panel = $("#cardpanel");
    if (!panel) return;
    const seq = ++cardSeq;
    document.body.classList.add("card-open");
    panel.hidden = false;
    panel.innerHTML = `<div class="card-head"><button class="card-close" title="close">×</button>
      <span class="pill">…</span><h2>${esc(name)}</h2><div class="full">loading module…</div></div>
      <div class="card-body"><p class="empty">Loading shared module…</p></div>`;
    attachPanelEvents();
    let card = null;
    let loadError = null;
    try {
      card = await loadCard(name);
    } catch (e) {
      loadError = e;
    }
    if (seq !== cardSeq) return;
    if (!card) {
      panel.innerHTML = `<div class="card-head"><button class="card-close" title="close">×</button>
        <h2>${esc(name)}</h2><div class="full">not in this build</div></div>
        <div class="card-body"><div class="stub">${esc(loadError ?
          "Could not load the shared module: " + loadError.message :
          "This name was not exported. It is beyond the one-layer MVP index, or did not resolve in the worksheet's open namespaces.")}</div></div>`;
      attachPanelEvents();
      return;
    }
    const sig = card.signature_source || "";
    const body = card.body_source || "";
    const doc = card.doc ? `<div class="card-doc md">${md(card.doc)}</div>` : "";
    const chips = (card.worksheets || []).map((s) =>
      `<a class="pill" href="${SHEET_DIR}${encodeURIComponent(s)}.html#decl=${encodeURIComponent(name)}">${esc(s)}</a>`
    ).join(" ");
    const loc = card.has_source
      ? `${esc(card.source_file)}:${card.range ? card.range.start.line : "?"}`
      : "source not indexed";
    const typeBlock = card.elaborated_type
      ? `<div class="lab">elaborated type</div><pre class="type-pre">${esc(card.elaborated_type)}</pre>`
      : `<p class="empty">No elaborated type was exported.</p>`;
    const refs = (card.refs || []).length
      ? `<ul class="refs">${card.refs.map(refLink).join("")}</ul>`
      : `<p class="empty">No references in this build (or this is a reference card: one layer only).</p>`;
    const bodyOpen = ["def", "abbrev", "instance", "structure", "inductive"].includes(card.kind);
    const bodyBlock = body
      ? `<details class="body-wrap" ${bodyOpen ? "open" : ""}>
           <summary>${card.kind === "theorem" ? "proof" : "body"}</summary>
           <pre class="mono">${highlightLean(body)}</pre>
         </details>` : "";

    panel.innerHTML = `
      <div class="card-head">
        <button class="card-close" title="close">×</button>
        <span class="pill ${esc(card.kind)}">${esc(card.kind)}</span>
        <h2>${esc(card.short || name)}</h2>
        <div class="full">${esc(name)}</div>
      </div>
      <div class="card-body">
        <div class="card-meta">
          <span class="mono small">${esc(card.module || "")}</span>
          <span class="muted small">${loc}</span>
          ${chips}
          <button class="copy" data-copy="${esc(name)}">copy name</button>
        </div>
        ${doc}
        <div class="tabs">
          <button data-tab="source" class="active">Source</button>
          <button data-tab="type">Type</button>
          <button data-tab="refs">References${card.refs && card.refs.length ? ` (${card.refs.length})` : ""}</button>
        </div>
        <div class="tab active card-source" data-tab="source">
          ${sig ? `<pre class="mono">${highlightLean(sig)}</pre>${bodyBlock}`
                : `<p class="empty">${esc(card.source_note || "The source file for this module is not indexed.")} The elaborated type is available under “Type”.</p>`}
        </div>
        <div class="tab" data-tab="type">${typeBlock}</div>
        <div class="tab" data-tab="refs">${refs}</div>
      </div>`;
    attachPanelEvents();
    linkifyCode(panel);
    linkifyProse(panel);
    $$(".decl", panel).forEach((a) => { if (a.dataset.name === name) a.classList.add("active"); });
    panel.scrollTop = 0;
  }

  function attachPanelEvents() {
    const panel = $("#cardpanel");
    if (!panel) return;
    const close = $(".card-close", panel);
    if (close) close.addEventListener("click", closeCard);
    $$("[data-tab]", panel).forEach((b) => {
      if (b.tagName !== "BUTTON") return;
      b.addEventListener("click", () => {
        $$("button[data-tab]", panel).forEach((x) => x.classList.remove("active"));
        $$(".tab", panel).forEach((x) => x.classList.remove("active"));
        b.classList.add("active");
        const tab = $(`.tab[data-tab="${b.dataset.tab}"]`, panel);
        if (tab) tab.classList.add("active");
      });
    });
    $$(".copy", panel).forEach((b) => b.addEventListener("click", async () => {
      try {
        await navigator.clipboard.writeText(b.dataset.copy);
        b.textContent = "copied";
        setTimeout(() => { b.textContent = "copy name"; }, 1200);
      } catch (_) { /* ignore */ }
    }));
  }

  function openCard(name, push = true) {
    if (!name) return;
    const hash = "#decl=" + encodeURIComponent(name);
    if (push && location.hash !== hash) location.hash = hash;
    renderCard(name);
  }

  function closeCard() {
    const panel = $("#cardpanel");
    if (panel) panel.hidden = true;
    document.body.classList.remove("card-open");
    if (location.hash.startsWith("#decl=")) {
      history.pushState(null, "", location.pathname + location.search);
    }
  }

  function route() {
    const h = location.hash || "";
    if (h.startsWith("#decl=")) {
      renderCard(decodeURIComponent(h.slice(6)));
      return;
    }
    const panel = $("#cardpanel");
    if (panel) panel.hidden = true;
    document.body.classList.remove("card-open");
    if (h.startsWith("#q=")) {
      const input = $("#search");
      if (input) {
        input.value = decodeURIComponent(h.slice(3));
        input.dispatchEvent(new Event("input", { bubbles: true }));
        input.focus();
      }
    }
  }

  /* ------------------------------ search ------------------------------- */

  function searchMatches(q) {
    q = q.trim().toLowerCase();
    if (!q) return [];
    const rows = [];
    for (const name of state.index.names || []) {
      const short = name.split(".").pop().toLowerCase();
      const summary = (state.index.search[name] || state.index.summaries[name] || "").toLowerCase();
      let score = 0;
      if (short === q || name.toLowerCase() === q) score = 100;
      else if (short.startsWith(q)) score = 80;
      else if (name.toLowerCase().includes(q)) score = 60;
      else if (summary.includes(q)) score = 30;
      if (score) rows.push({ name, score, summary: state.index.summaries[name] || "" });
    }
    rows.sort((a, b) => b.score - a.score || a.name.length - b.name.length || a.name.localeCompare(b.name));
    return rows.slice(0, 40);
  }

  function setupZonesToggle() {
    const btn = $("#zones-toggle");
    if (!btn) return;
    const KEY = "play.zonesHidden";
    let hidden = false;
    try { hidden = localStorage.getItem(KEY) === "1"; } catch (_) { /* file:// may deny storage */ }
    const apply = () => {
      document.body.classList.toggle("outline-hidden", hidden);
      btn.textContent = hidden ? "Show zones" : "Hide zones";
      btn.setAttribute("aria-expanded", String(!hidden));
    };
    apply();
    btn.addEventListener("click", () => {
      hidden = !hidden;
      try { localStorage.setItem(KEY, hidden ? "1" : "0"); } catch (_) { /* ignore */ }
      apply();
    });
  }

  function setupSearch() {
    const input = $("#search");
    const box = $("#search-results");
    if (!input || !box || !state.index) return;
    const render = () => {
      const rows = searchMatches(input.value);
      state.searchRows = rows;
      if (!input.value.trim() || !rows.length) {
        box.hidden = true;
        box.innerHTML = "";
        return;
      }
      box.innerHTML = rows.map((r, i) => {
        return `<button class="row" data-name="${esc(r.name)}" data-idx="${i}">
          <span class="mono">${esc(r.name)}</span>
          <div class="sub">${esc((r.summary || "").replace(/\s+/g, " ").slice(0, 110))}</div>
        </button>`;
      }).join("");
      box.hidden = false;
      $$(".row", box).forEach((b) => b.addEventListener("click", () => {
        input.value = "";
        box.hidden = true;
        openCard(b.dataset.name);
      }));
    };
    input.addEventListener("input", render);
    input.addEventListener("focus", render);
    input.addEventListener("keydown", (e) => {
      if (e.key === "Escape") { box.hidden = true; input.blur(); }
      if (e.key === "Enter" && state.searchRows.length) {
        const n = state.searchRows[0].name;
        input.value = ""; box.hidden = true; openCard(n);
      }
    });
    document.addEventListener("click", (e) => {
      if (!box.contains(e.target) && e.target !== input) box.hidden = true;
    });
  }

  /* --------------------------- worksheet page -------------------------- */

  function renderWorksheet() {
    const d = state.sheet;
    document.title = d.title + " · FLT play";
    const h1 = $("#ws-title");
    if (h1) h1.textContent = d.title;
    const tag = $("#ws-tagline");
    if (tag) tag.textContent = d.tagline || "";
    const subj = $("#ws-subject");
    if (subj) { subj.innerHTML = md(d.subject || ""); linkifyProse(subj); }
    const meta = $("#ws-meta");
    if (meta) {
      const rows = [
        ["reads", d.reads || "—"],
        ["status", d.status || "—"],
        ["date", d.date || "—"],
        ["file", d.file || "—"],
        ["check", d.check || "—"],
      ];
      meta.innerHTML = rows.map(([k, v]) =>
        `<div class="k">${esc(k)}</div><div class="v mono small">${inlineMd(v)}</div>`).join("");
    }

    const outline = $("#outline");
    if (outline) {
      outline.innerHTML = `<h3>zones</h3>` + (d.zones || []).map((z) =>
        `<a href="#zone-${esc(z.id)}"><span class="zone-id">${esc(z.id)}</span>${esc(z.title)}</a>`
      ).join("");
    }

    const article = $("#worksheet");
    if (!article) return;
    const parts = [];
    let current = null;
    const openZone = (id) => {
      const z = (d.zones || []).find((x) => x.id === id);
      if (!z) return;
      parts.push(`<section class="zone" id="zone-${esc(z.id)}">
        <h2><span class="zone-id">Zone ${esc(z.id)}</span>${esc(z.title)}</h2>`);
    };
    const closeZone = () => { if (current !== null) parts.push("</section>"); };

    for (const block of d.blocks || []) {
      if (block.zone && block.zone !== current) {
        closeZone();
        openZone(block.zone);
        current = block.zone;
      }
      if (!block.zone && current === null) {
        parts.push(`<section class="zone" id="zone-prelude">`);
        current = "__prelude";
      }
      parts.push(renderBlock(block));
    }
    closeZone();
    article.innerHTML = parts.join("\n");
    linkifyProse(article);
    linkifyCode(article);
  }

  function renderBlock(b) {
    if (b.type === "prose") {
      return `<div class="md">${md(b.md)}</div>`;
    }
    if (b.type === "code") {
      return `<div class="codeblock"><pre>${highlightLean(b.text)}</pre></div>`;
    }
    if (b.type === "example" || b.type === "decl") {
      const doc = b.doc ? `<div class="md doc">${md(b.doc)}</div>` : "";
      return `<div class="codeblock">${doc}<pre>${highlightLean(b.text)}</pre></div>`;
    }
    if (b.type === "check") {
      const card = b.card ? getCard(b.card) : null;
      if (!card) {
        return `<div class="codeblock"><pre>${highlightLean(b.raw || "#check " + (b.name || b.expr || ""))}</pre></div>`;
      }
      const sig = oneLine(card.signature_source || card.elaborated_type, 240);
      return `<div class="check-inline">
        <span class="pill ${esc(card.kind)}">${esc(card.kind)}</span>
        <a class="decl mono" href="#decl=${encodeURIComponent(card.name)}" data-name="${esc(card.name)}">${esc(b.display || card.name)}</a>
        <span class="sig" title="${esc(sig)}">${esc(sig)}</span>
        <button class="open" data-open="${esc(card.name)}">card</button>
      </div>`;
    }
    if (b.type === "print") {
      const card = b.card ? getCard(b.card) : null;
      if (!card) {
        return `<div class="codeblock"><pre>${highlightLean(b.raw || "#print " + (b.name || ""))}</pre></div>`;
      }
      const body = card.body_source || "";
      const sig = card.signature_source || card.elaborated_type || "";
      return `<details class="inline-def" open>
        <summary><span class="pill ${esc(card.kind)}">${esc(card.kind)}</span>
          <a class="decl mono" href="#decl=${encodeURIComponent(card.name)}" data-name="${esc(card.name)}">${esc(card.name)}</a>
          <span class="muted small"> source, not the elaborated #print term</span></summary>
        <pre>${highlightLean(sig + (body ? "\n" + body : ""))}</pre>
      </details>`;
    }
    return `<div class="md">${md(JSON.stringify(b))}</div>`;
  }

  /* ------------------------------ index page --------------------------- */

  function renderIndex() {
    const grid = $("#sheets");
    if (!grid) return;
    const entries = Object.values(state.index.worksheets || {})
      .sort((a, b) => a.slug.localeCompare(b.slug));
    grid.innerHTML = entries.map((s) => {
      const n = s.card_count || 0;
      return `<a class="sheet-card" href="worksheets/${encodeURIComponent(s.slug)}.html">
        <h3>${esc(s.title)}</h3>
        <div class="tag">${esc(s.tagline || "")}</div>
        <p>${esc((s.subject || "").slice(0, 220))}</p>
        <div class="meta">
          <span class="pill">${esc(s.status || "open")}</span>
          <span class="pill">${esc(s.date || "")}</span>
          <span class="pill">${n} cards</span>
        </div>
      </a>`;
    }).join("");
  }

  /* -------------------------------- boot ------------------------------- */

  async function boot() {
    await loadScript(DATA + "index.js");
    state.index = window.PLAY_INDEX;
    if (!state.index) throw new Error("index.js did not register PLAY_INDEX");
    if (PAGE === "index") {
      renderIndex();
    } else {
      const slug = document.body.dataset.slug;
      await loadScript(DATA + `ws-${slug}.js`);
      state.sheet = (window.PLAY_WORKSHEETS || {})[slug];
      if (!state.sheet) throw new Error("worksheet shard did not register " + slug);
      await prefetchModules(state.sheet.modules);
      renderWorksheet();
      document.body.classList.remove("card-open");
    }
    setupZonesToggle();
    setupSearch();
    document.addEventListener("click", (e) => {
      const a = e.target.closest("a.decl[data-name]");
      if (!a) return;
      if (e.metaKey || e.ctrlKey || e.shiftKey || e.button === 1) return;
      e.preventDefault();
      openCard(a.dataset.name);
    });
    document.addEventListener("click", (e) => {
      const b = e.target.closest("button[data-open]");
      if (!b) return;
      openCard(b.dataset.open);
    });
    window.addEventListener("hashchange", route);
    route();
  }

  boot().then(() => {
    window.__PLAY_BOOTED = true;
  }).catch((err) => {
    const main = $("#worksheet") || $("#sheets") || document.body;
    main.innerHTML = `<div class="stub">Could not load the Play data.<br>
      <span class="mono small">${esc(err.message)}</span><br>
      The app loads classic script shards from <code>data/</code>, so it works
      when opened from disk; if a shard is missing, rebuild the data.</div>`;
    window.__PLAY_ERROR = err;
    console.error(err);
  });
})();
