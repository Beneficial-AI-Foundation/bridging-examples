"use strict";
// The explorer's lookups: examples, bridge methods and atoms, the declarations shown for an atom
// in each panel, proof folding, URL parameters, and the messages of empty panels.
const Explorer = {
  stages: ['rust', 'aeneas', 'spec', 'crypto', 'bridge'],
  // `files` shows whole files; `declaration` restricts each panel to the selected atom.
  mode: value => value === 'declaration' ? 'declaration' : 'files',
  toggleMode: value => value === 'declaration' ? 'files' : 'declaration',
  // The label shown before a declaration; only assumptions have one.
  evidence(declaration) {
    if (declaration.projectionOf) return null;
    if (declaration.status === 'assumption') return { kind: 'assumption', label: 'Assumption' };
    return null;
  },
  example(bundle, id) { return bundle.examples.find(e => e.id === id) || bundle.examples.find(e => e.id === bundle.defaultExample) || bundle.examples[0]; },
  // `example` as shown for one of its bridge methods, the first unless `id` names another: the
  // files and declarations of the method with those of the shared files it does not replace, and
  // the method's atoms and coverage. The files are the objects of `example`. An example without
  // methods is returned as it is.
  view(example, id) {
    const method = example.methods?.find(m => m.id === id) || example.methods?.[0];
    if (!method) return example;
    const shown = (entry, path) => entry.method ? entry.method === method.id : !method.replaces.includes(path);
    return { ...example, method, items: method.items, coverage: method.coverage,
      files: Object.fromEntries(Object.entries(example.files).filter(([path, file]) => shown(file, path))),
      declarations: example.declarations.filter(d => shown(d, d.file)) };
  },
  // An atom by id, Lean name, alias (`item-aliases` in Cargo.toml) or unique suffix.
  item(example, id) {
    if (!id) return null;
    id = example.itemAliases?.[id] || id;
    const suffixes = example.items.filter(i => i.id.endsWith('.' + id));
    return example.items.find(i => i.id === id || i.leanName === id) ||
      (suffixes.length === 1 ? suffixes[0] : null);
  },
  // The atom that line `line` of `file` belongs to, or null.
  atomAt(example, stage, file, line) {
    const declarations = example.declarations.filter(d => d.stage === stage && d.file === file &&
      d.start <= line && line <= (d.end || Infinity));
    const owners = example.items.filter(item => declarations.some(d =>
      (Array.isArray(item[stage]) && item[stage].includes(d.name)) ||
      (['spec', 'bridge'].includes(stage) && item.assumptions?.includes(d.name)) ||
      d.links?.some(link => link.targets.includes(item.leanName))));
    if (owners.length === 1) return owners[0];
    // A trait method lies inside its trait: the atom with the smallest range containing the line
    // owns it, and atoms with equally small ranges remain ambiguous.
    const sizes = example.items.map(i => this.entries(example, i, stage)
      .filter(r => r.file === file && r.start <= line && line <= (r.end || Infinity))
      .map(r => (r.end || Infinity) - r.start));
    const smallest = Math.min(...sizes.flat());
    const matches = example.items.filter((_, index) => sizes[index].includes(smallest));
    return matches.length === 1 ? matches[0] : null;
  },
  // The atom `id` and the file of each panel; the panel clicked (`origin`) keeps its file.
  selection(example, id, support, origin) {
    const item = this.item(example, id);
    const files = Object.fromEntries(this.stages.map(stage => [stage,
      this.file(example, item, stage, origin?.stage === stage ? origin.file : null, support)]));
    return { item, files };
  },
  // A plain left click, without selected text, selects the atom of a line.
  shouldSelectCode(event, selectedText) {
    return event.button === 0 && event.detail <= 1 && !selectedText &&
      !event.ctrlKey && !event.metaKey && !event.altKey && !event.shiftKey;
  },
  // What `item` highlights in `stage`: its Rust or Aeneas range, or its linked declarations,
  // with its assumptions and hypotheses in Spec and Bridge.
  entries(example, item, stage) {
    if (!item) return [];
    if (stage === 'rust' || stage === 'aeneas') return item[stage] ? [item[stage]] : [];
    const names = [...(item[stage] || []),
      ...(['spec', 'bridge'].includes(stage) ? [...(item.assumptions || []), ...(item.hypotheses || [])] : [])];
    return example.declarations.filter(d => d.stage === stage && names.includes(d.name));
  },
  // The line ranges drawn: the whole file, or the `selected` ranges with adjacent ones merged.
  sourceBlocks(example, file, selected) {
    const lineCount = file.text.split('\n').length;
    const ranges = [];
    for (const entry of (selected || [{ start: 1, end: lineCount }])
      .map(entry => ({ start: entry.start, end: entry.end ?? lineCount }))
      .sort((a, b) => a.start - b.start)) {
      const previous = ranges.at(-1);
      if (previous && entry.start <= previous.end + 1) previous.end = Math.max(previous.end, entry.end);
      else ranges.push({ start: entry.start, end: entry.end });
    }
    return ranges;
  },
  // Cuts a line range into parts, marking the proofs of Spec and Bridge theorems for folding.
  // `proofRange` counts UTF-8 bytes from the declaration's first line; parts count characters.
  proofParts(file, declarations, range) {
    const rows = file.text.split('\n');
    let offset = 0;
    const starts = rows.map(row => { const start = offset; offset += row.length + 1; return start; });
    const start = starts[range.start - 1];
    const end = starts[range.end] ?? file.text.length;
    const parts = [];
    const append = (from, to, declaration) => {
      if (from >= to) return;
      const index = starts.findLastIndex(start => start <= from);
      parts.push({ text: file.text.slice(from, to), line: index + 1,
        column: from - starts[index], declaration });
    };
    const proofs = !['spec', 'bridge'].includes(file.stage) ? [] : declarations.filter(d =>
      d.file === file.path && d.kind === 'theorem' && !d.projectionOf && d.proofRange).flatMap(d => {
        const {startByte, endByte} = d.proofRange;
        const source = rows.slice(d.start - 1, d.end).join('\n');
        const bytes = new TextEncoder().encode(source);
        if (!Number.isInteger(startByte) || !Number.isInteger(endByte) ||
            startByte < 0 || startByte >= endByte || endByte > bytes.length) return [];
        const decoder = new TextDecoder();
        const base = starts[d.start - 1];
        return [{ declaration: d,
          start: base + decoder.decode(bytes.slice(0, startByte)).length,
          end: base + decoder.decode(bytes.slice(0, endByte)).length }];
      }).filter(proof => proof.start < end && proof.end > start).sort((a, b) => a.start - b.start);
    let cursor = start;
    for (const proof of proofs) {
      const begin = Math.max(cursor, proof.start);
      const stop = Math.min(end, proof.end);
      if (stop <= begin) continue;
      append(cursor, begin);
      append(begin, stop, proof.declaration);
      cursor = stop;
    }
    append(cursor, end);
    return parts;
  },
  // The files of a panel, main files first; supporting files only when `support` is set.
  files(example, stage, support) {
    return Object.keys(example.files).filter(p => example.files[p].stage === stage && (support || !example.files[p].support))
      .sort((a, b) => Number(example.files[a].support) - Number(example.files[b].support) || a.localeCompare(b));
  },
  // The file a panel shows: `requested`, else the first with `item`, else the first.
  file(example, item, stage, requested, support) {
    const files = this.files(example, stage, support);
    return files.includes(requested) ? requested : this.entries(example, item, stage).find(e => files.includes(e.file))?.file || files[0];
  },
  // The example, bridge method, atom and mode of a URL; old links (`properties`, `security`) open
  // Bridge.
  normalize(bundle, params) {
    const example = this.view(this.example(bundle, params.get('example')), params.get('method'));
    const item = this.item(example, params.get('item'));
    const normalized = new URLSearchParams(params);
    if (params.has('security') && !params.has('bridge')) {
      normalized.set('bridge', params.get('security'));
      normalized.delete('widths');
    }
    if (params.has('properties')) {
      if (params.get('properties') === '1') normalized.set('bridge', '1');
      normalized.delete('widths');
    }
    const oldFile = params.get('propertiesFile') || params.get('bridgeFile');
    if (oldFile?.endsWith('/Properties.lean')) {
      normalized.set('bridgeFile', oldFile.replace(/Properties\.lean$/, 'Bridge.lean'));
    }
    for (const key of ['properties', 'propertiesFile', 'security', 'securityFile']) normalized.delete(key);
    return { example: example.id, method: example.method?.id ?? null, item: item?.id ?? null, mode: this.mode(params.get('mode')), params: normalized };
  },
  // The message of a panel with nothing to show for `item`.
  pending(example, item, stage) {
    if (stage === 'aeneas' && example.extraction === 'missing') return 'Not extracted';
    if (!item) return example.extraction === 'missing' ? 'Coverage unknown until extraction' : 'No source file';
    if (item.assumptions?.length) return stage === 'crypto' ? 'External operation: see its assumption'
      : 'Assumed external operation';
    if (example.extraction === 'missing') return 'Coverage unknown until extraction';
    if (stage === 'spec' && item.category && item.category !== 'functions') return 'Type or trait: no functional specification';
    return { spec: 'Functional specification pending', crypto: 'Crypto counterpart pending' }[stage] || 'Bridge theorem pending';
  },
};
