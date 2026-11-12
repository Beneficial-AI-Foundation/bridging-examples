// Inline the stylesheet, icons, scripts and data into shared/template.html: one offline page.
import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { deflateRawSync } from "node:zlib";

const read = (path) => readFileSync(new URL(path, import.meta.url), "utf8");
// The page allows only its own inline scripts, by hash, instead of any inline script.
const inline = "script-src 'unsafe-inline'";

/** `verso`, when given, holds Verso's rendering of the Lean files with its stylesheet and scripts
 * (see `buildVerso` in build.mjs). Its markup is large and repetitive, so it is embedded packed. */
export function renderHtml(bundle, verso = null) {
  const data = JSON.stringify(bundle).replaceAll("<", "\\u003c");
  const packed = verso && deflateRawSync(JSON.stringify({ files: verso.files, docs: verso.docs }), { level: 9 }).toString("base64");
  const html = read("shared/template.html")
    .replace(/\s*<script id="template-entry">[\s\S]*?<\/script>/, "")
    .replace("<!-- BROWSER_ICONS -->", () => read("shared/icons.svg"))
    .replace("/* BROWSER_STYLE */", () => read("shared/style.css") + (verso ? verso.style + read("shared/verso.css") : ""))
    .replace("<!-- BROWSER_VERSO -->", () => verso
      ? `<script type="application/octet-stream" id="verso-data">${packed}</script>\n  <script>${verso.script}</script>` : "")
    .replace("<!-- BROWSER_DATA -->", () => data)
    .replace("/* BROWSER_APP */", () => read("shared/app.js")
      .replace("/* PANEL_STATE */", () => read("shared/panel-state.cjs"))
      .replace("/* EXPLORER_STATE */", () => read("shared/explorer-state.cjs")));
  const hashes = [...html.matchAll(/<script>([\s\S]*?)<\/script>/g)]
    .map(([, text]) => `'sha256-${createHash("sha256").update(text).digest("base64")}'`);
  assert(hashes.length && html.includes(inline), "The template's script policy changed");
  return html.replace(inline, () => `script-src ${hashes.join(" ")}`);
}
