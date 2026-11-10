// Cut Verso's HTML for a module into one fragment per source line, so the explorer can keep its
// line numbers, atom selection and proof folding.

const TOKEN = /(<(?:[^>"']|"[^"]*"|'[^']*')*>)|([^<]+)/g;
const VOID = new Set(['input', 'br', 'img', 'hr', 'meta', 'link']);
// A proof state or a message stays whole, on the line where it ends.
const ATOMIC = ['tactic-state', 'hover-container'];

/** Every element open at a line end is closed there and reopened on the next line. The pieces
 * of a tactic that spans lines share `data-tid`; its proof state is in the last piece. Hover ids
 * get the module as a prefix so the tables of several modules can be merged. */
export function splitLines(html, module) {
  const lines = [[]], stack = [];
  let atomic = 0, count = 0;
  const out = text => lines.at(-1).push(text);
  for (const match of html.matchAll(TOKEN)) {
    let tag = match[1];
    const text = match[2];
    if (text !== undefined) {
      if (atomic) { out(text); continue; }
      text.split('\n').forEach((part, index) => {
        if (index) {
          for (const open of [...stack].reverse()) out(`</${open.name}>`);
          lines.push([]);
          for (const open of stack) out(open.tag);
        }
        if (part) out(part);
      });
      continue;
    }
    if (tag.startsWith('</')) {
      if (stack.pop().root) atomic--;
      out(tag);
      continue;
    }
    if (tag.startsWith('<!')) { out(tag); continue; }
    const name = tag.match(/<\s*([A-Za-z0-9-]+)/)[1];
    const classes = new Set((tag.match(/class="([^"]*)"/)?.[1] || '').split(/\s+/).filter(Boolean));
    tag = tag.replace(/data-verso-hover="(\d+)"/g, (_, id) => `data-verso-hover="${module}:${id}"`);
    if (!atomic && name === 'span' && (classes.has('tactic') || classes.has('has-info'))) {
      count++;
      tag = `${tag.slice(0, -1).replace(/\/+$/, '')} ${classes.has('tactic') ? 'data-tid' : 'data-iid'}="${module}:${count}">`;
    }
    out(tag);
    if (tag.endsWith('/>') || VOID.has(name)) continue;
    const root = !atomic && ATOMIC.some(c => classes.has(c));
    if (root) atomic++;
    stack.push({ tag, name, root });
  }
  return lines.map(parts => parts.join(''));
}

const KEYWORDS = new Set(['at', 'from', 'end', 'fun', 'do', 'by', 'have', 'show', 'let', 'in', 'if', 'then', 'else',
  'match', 'with', 'where', 'def', 'theorem', 'open', 'import', 'namespace', 'section', 'instance', 'structure',
  'class', 'deriving', 'mut', 'for', 'return', 'break', 'continue', 'unless', 'try', 'catch', 'finally', 'done',
  'local', 'private', 'protected']);
const NAME = /(<span class="(var|const) token" data-binding="([^"]*)"[^>]*>)([A-Za-z_]+)(<\/span>)/g;

/** SubVerso prints an escaped identifier (`«at»`) without its guillemets; put them back. */
export function guillemets(line) {
  return line.replace(NAME, (all, open, kind, binding, word, close) => {
    const last = kind === 'const' ? binding.slice('const-'.length).split('.').at(-1) : null;
    const escaped = KEYWORDS.has(word) && (kind === 'var' || last === word || last === `«${word}»`);
    return open + (escaped ? `«${word}»` : word) + close;
  });
}
