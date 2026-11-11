(() => {
'use strict';
/* PANEL_STATE */
/* EXPLORER_STATE */
const bundle = JSON.parse(document.getElementById('source-data').textContent);
const $ = s => document.querySelector(s);
const esc = x => String(x).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const titles = { rust:'Rust', aeneas:'Aeneas', spec:'Spec', crypto:'Crypto', bridge:'Bridge' };
let data, item, home = false, state = {}, files = {}, drag = null;
const widths = new Map();
const openProofs = new Set();
const mobile = matchMedia('(max-width: 760px)');
const icon = name => `<svg viewBox="0 0 24 24" aria-hidden="true"><use href="#icon-${name}"></use></svg>`;

function load() {
  const params = new URLSearchParams(location.hash.slice(1));
  home = params.get('view') === 'home' || (!params.has('example') && !bundle.defaultExample);
  const selected = Explorer.normalize(bundle, params);
  data = Explorer.example(bundle, selected.example);
  item = Explorer.item(data, selected.item);
  state = { example:data.id, item:item?.id ?? '', mode:item ? selected.mode : 'files', support:params.get('support') === '1', font:Math.min(18, Math.max(10, Number(params.get('font')) || 12)),
    ...Panels.read(selected.params) };
  widths.set(Panels.signature(state), Panels.readWeights(state, selected.params.get('widths')));
  for (const stage of Explorer.stages) files[stage] = Explorer.file(data, item, stage, selected.params.get(`${stage}File`), state.support);
}
function save() {
  if (home) return;
  const p = new URLSearchParams();
  for (const [k,v] of Object.entries(state)) if (v !== '') p.set(k, typeof v === 'boolean' ? +v : v);
  for (const stage of Explorer.stages) if (files[stage]) p.set(`${stage}File`, files[stage]);
  p.set('widths', Panels.weights(state, widths.get(Panels.signature(state))).map(n => n.toFixed(6)).join(','));
  history.replaceState(null, '', `#${p}`);
}
function select(id, origin) {
  const selected = Explorer.selection(data,id,state.support,origin);
  item = selected.item; files = selected.files; state.item = item?.id ?? '';
  if (!item) state.mode = 'files';
  save(); render();
  if (origin && state.mode === 'files') {
    const panel = $('#pane-body-'+origin.stage);
    panel.scrollTop = origin.top;
    panel.scrollLeft = origin.left;
  }
}
function highlight(line) {
  const parts = line.split(/(\/\/.*|--.*|"(?:\\.|[^"\\])*"|\b(?:pub|fn|let|mut|type|trait|struct|impl|def|abbrev|theorem|structure|namespace|end|import|open|where|do|by|pure|match|with|if|then|else|fun|return|some|none|Some|None)\b|\b\d+\b)/g);
  return parts.map((p,i) => i % 2 ? `<span class="token-${p.startsWith('//') || p.startsWith('--') ? 'comment' : /^\d/.test(p) ? 'number' : p.startsWith('"') ? 'string' : 'keyword'}">${esc(p)}</span>` : esc(p)).join('');
}
function ranges(stage) { return Explorer.entries(data,item,stage); }
function visibleText(stage) {
  const file = data.files[files[stage]];
  if (!file) return '';
  if (state.mode === 'files') return file.text;
  const entries = ranges(stage).filter(r => r.file === file.path);
  return entries.map(r => file.text.split('\n').slice(r.start-1,r.end).join('\n')).join('\n\n');
}
function codePart(file, stage, part) {
  const rows = part.text.replace(/\n$/, '').split('\n');
  let firstLine = part.line;
  if (part.column > 0 && !rows[0].trim()) { rows.shift(); firstLine++; }
  if (!rows.length) return '';
  const selected = ranges(stage).filter(r => r.file === file.path);
  const declarations = data.declarations.filter(d => d.file === file.path);
  let blockComment = false;
  return `<pre class="code${file.html ? ' hl lean' : ''}">${rows.map((line,i) => {
    const n = firstLine+i;
    if (line.includes('/-') || line.includes('/*')) blockComment = true;
    // Verso's markup for a whole source line; a row cut by proof folding keeps the plain colouring.
    const verso = file.html && line === (file.rows ||= file.text.split('\n'))[n-1] ? file.html[n-1] : null;
    const text = verso ?? (blockComment ? `<span class="token-comment">${esc(line)}</span>` : highlight(line));
    if (line.includes('-/') || line.includes('*/')) blockComment = false;
    const focused = selected.some(r => n >= r.start && n <= (r.end || Infinity));
    const declaration = (i > 0 || part.column === 0 || firstLine !== part.line) && declarations.find(d => d.start === n);
    const evidence = declaration && Explorer.evidence(declaration);
    const trustTitle = declaration && declaration.status + ': ' + declaration.type;
    const badge = evidence ? `<span class="evidence-label ${evidence.kind}" title="${esc(declaration.status)}">${evidence.label}</span>` : '';
    const atom = Explorer.atomAt(data, stage, file.path, n);
    const number = atom ? `<button class="ln" data-atom="${esc(atom.id)}" title="Select ${esc(atom.name)}">${n}</button>` : `<span class="ln">${n}</span>`;
    return `${badge}<span class="line${focused ? ' focused':''}" data-line="${n}"${atom ? ` data-atom="${esc(atom.id)}"`:''}${declaration ? ` title="${esc(trustTitle)}"`:''}>${number}<code>${text || ' '}</code></span>`;
  }).join('')}</pre>`;
}
function code(file, stage, start, end) {
  return Explorer.proofParts(file,data.declarations,{start,end}).map(part=>{
    const content = codePart(file,stage,part);
    if (!part.declaration) return content;
    const key = `${data.id}:${part.declaration.name}`;
    return `<details class="proof-body" data-proof="${esc(key)}"${openProofs.has(key)?' open':''}><summary aria-label="Proof of ${esc(part.declaration.name)}">Proof</summary>${content}</details>`;
  }).join('');
}
function body(stage) {
  const file = data.files[files[stage]];
  const related = ranges(stage);
  const status = item && ['spec','crypto','bridge'].includes(stage) && !related.length ? `<div class="stage-status">${Explorer.pending(data,item,stage)}</div>` : '';
  if (!file) return `<div class="empty-additions"><strong>${Explorer.pending(data,item,stage)}</strong></div>`;
  const declarations = data.declarations.filter(d => d.file === file.path);
  const picker = declarations.length ? `<div class="related-context"><select data-declaration="${stage}" aria-label="${titles[stage]} declaration"><option value="">Declarations (${declarations.length})</option>${declarations.map(d => `<option value="${esc(d.name)}">${related.some(r=>r.name===d.name)?'* ':''}${esc(d.name)} (${esc(d.status)})</option>`).join('')}</select></div>` : '';
  const selected = state.mode === 'files' ? null : related.filter(r=>r.file===file.path);
  return status + picker + Explorer.sourceBlocks(data,file,selected).map(r=>code(file,stage,r.start,r.end)).join('');
}
// Overview: Rust is extracted to Aeneas, Spec states what the extracted function returns, and
// Bridge relates the extracted function to Crypto, using Spec.
function overview() {
  const stage=(key,x,y,caption)=>`<g class="stage ${key}"><rect x="${x}" y="${y}" width="152" height="64" rx="6"/><rect class="dot" x="${x+14}" y="${y+17}" width="8" height="8" rx="2"/><text class="name" x="${x+30}" y="${y+25}">${titles[key]}</text><text class="shape" x="${x+14}" y="${y+48}">${caption}</text></g>`;
  const arrow=x=>`<path class="link" d="M${x+4} 44H${x+52}" marker-end="url(#overview-arrow)"/>`;
  const diagram=`<svg class="overview" viewBox="0 0 788 200" role="img" aria-label="Rust is extracted to Aeneas. Spec states what the extracted function returns. Bridge shows the extracted function equal in distribution to the Crypto algorithm, given assumptions, and uses Spec.">
    <defs><marker id="overview-arrow" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0 0L8 4L0 8z"/></marker></defs>
    ${stage('rust',0,12,'fn f')}${stage('aeneas',212,12,'def f : Result')}${stage('spec',424,12,'theorem f_spec')}${stage('crypto',636,12,'def f : ProbComp')}${stage('bridge',424,124,'theorem f_bridge')}
    ${arrow(152)}${arrow(364)}
    <path class="link" d="M288 80V156H420" marker-start="url(#overview-arrow)"/><path class="link" d="M712 80V156H580" marker-start="url(#overview-arrow)"/>
    <path class="link" d="M500 80V120" marker-end="url(#overview-arrow)"/>
  </svg>`;
  const tiles=bundle.examples.map(e=>`<a class="example-tile" href="#example=${esc(e.id)}"><strong>${esc(e.name)}</strong><span>${esc(e.description||'')}</span></a>`).join('');
  return `<div class="home-inner">${diagram}<div class="example-tiles">${tiles}</div></div>`;
}
function layout() { return Panels.layout(state,widths.get(Panels.signature(state)),$('#panes').clientWidth); }
function resize() {
  if (mobile.matches || home) return;
  const l = layout();
  $('#panes').style.setProperty('--pane-columns',Object.values(l.sizes).map(n=>`${n}px`).join(' '));
  document.querySelectorAll('[data-resize]').forEach(el=>{
    const next=l.active[l.active.indexOf(el.dataset.resize)+1];
    el.setAttribute('aria-valuenow',Math.round(100*l.sizes[el.dataset.resize]/(l.sizes[el.dataset.resize]+l.sizes[next])));
  });
}
function endDrag(commit) {
  if (!drag) return;
  const old = drag; drag = null;
  if (!commit) widths.set(old.signature,old.weights);
  old.el.classList.remove('dragging'); document.body.classList.remove('resizing-panes');
  if (old.el.hasPointerCapture(old.pointer)) old.el.releasePointerCapture(old.pointer);
  old.el.blur(); resize(); save();
}
function resetWidths() { endDrag(false); widths.delete(Panels.signature(state)); resize(); save(); }
function wireResize() {
  for (const el of document.querySelectorAll('[data-resize]')) {
    el.onpointerdown=e=>{
      if(e.button!==0 || !e.isPrimary || mobile.matches) return;
      e.preventDefault();
      const signature=Panels.signature(state);
      drag={el,pointer:e.pointerId,x:e.clientX,layout:layout(),signature,weights:widths.get(signature)};
      el.setPointerCapture(e.pointerId); el.classList.add('dragging'); document.body.classList.add('resizing-panes');
    };
    el.onpointermove=e=>{if(drag?.pointer!==e.pointerId)return; widths.set(drag.signature,Panels.resize(drag.layout,el.dataset.resize,e.clientX-drag.x));resize();};
    el.onpointerup=e=>{if(drag?.pointer===e.pointerId)endDrag(true);};
    el.onpointercancel=el.onlostpointercapture=e=>{if(drag?.pointer===e.pointerId)endDrag(false);};
    el.ondblclick=resetWidths;
    el.onkeydown=e=>{
      if(['Home','Enter'].includes(e.key)){e.preventDefault();resetWidths();}
      else if(['ArrowLeft','ArrowRight'].includes(e.key)){e.preventDefault();widths.set(Panels.signature(state),Panels.resize(layout(),el.dataset.resize,(e.key==='ArrowLeft'?-1:1)*(e.shiftKey?48:16)));resize();save();}
      else if(e.key==='Escape')endDrag(false);
    };
  }
}
function render(preserveScroll = false) {
  const scroll = new Map(Explorer.stages.map(stage => [stage, $('#pane-body-'+stage)?.scrollTop]));
  endDrag(true);
  document.title=`${data.name} - Bridging Examples`;
  $('#home').hidden=!home; $('#panes').hidden=home; document.body.classList.toggle('at-home',home);
  $('#example-picker').value=home?'':data.id;
  if(home){document.title='Bridging Examples';return;}
  $('#item-picker').innerHTML=`<option value="">Declarations (${data.items.length})</option>`+data.items.map(i=>`<option value="${esc(i.id)}">${esc(i.name)}</option>`).join('');
  $('#item-picker').value=item?.id ?? '';
  $('#item-title').textContent=item?.name ?? data.name;
  $('#focus-declaration').disabled=!item;
  $('#item-summary').textContent=data.name;
  $('#check-status').textContent=data.coverage?`Spec ${data.coverage.spec}/${data.coverage.functions} · Crypto ${data.coverage.crypto}/${data.coverage.atoms} · Bridge ${data.coverage.bridge}/${data.coverage.atoms}`:'Not extracted';
  $('#focus-declaration').setAttribute('aria-pressed',state.mode==='declaration');
  $('#focus-declaration').title=state.mode==='files'?'Focus selected declaration':'Show full files';
  $('#focus-declaration').setAttribute('aria-label',$('#focus-declaration').title);
  $('#font-size').value=state.font; document.documentElement.style.setProperty('--code-size',`${state.font}px`);
  $('#show-support').checked=state.support;
  const active=Panels.active(state);
  $('#panes').innerHTML=Explorer.stages.map(stage=>{
    const expanded=state[stage],disabled=expanded&&active.length===1;
    const label=`${expanded?'Minimize':'Restore'} ${titles[stage]}`;
    const toggle=`<button class="pane-toggle" data-toggle="${stage}" title="${label}" aria-label="${label}" aria-expanded="${expanded}"${disabled?' disabled':''}>${icon(expanded?'minus':'plus')}</button>`;
    if(!expanded)return `<section class="pane ${stage} minimized"><div class="pane-header">${toggle}<h3>${titles[stage]}</h3></div></section>`;
    const options=Explorer.files(data,stage,state.support),file=data.files[files[stage]];
    const next=active[active.indexOf(stage)+1],previous=active[active.indexOf(stage)-1];
    const railsBefore=previous&&Explorer.stages[Explorer.stages.indexOf(stage)-1]!==previous;
    const handle=(left,right,side)=>`<div class="pane-resizer${side}" data-resize="${left}" role="separator" tabindex="0" aria-orientation="vertical" aria-valuemin="0" aria-valuemax="100" aria-label="Resize ${titles[left]} and ${titles[right]}" title="Drag to resize; double-click to reset"></div>`;
    return `<section class="pane ${stage}"><div class="pane-header"><div class="pane-title"><h3>${titles[stage]}</h3><div class="pane-actions"><button class="pane-toggle" data-copy="${stage}" title="Copy displayed source" aria-label="Copy ${titles[stage]} source"${!file?' disabled':''}>${icon('copy')}</button><button class="pane-toggle" data-download="${stage}" title="Download complete file" aria-label="Download ${titles[stage]} file"${!file?' disabled':''}>${icon('download')}</button>${toggle}</div></div><select class="source-picker" data-source="${stage}" aria-label="${titles[stage]} source file"${!options.length?' disabled':''}>${options.map(p=>`<option value="${esc(p)}"${files[stage]===p?' selected':''}>${esc(p)}</option>`).join('')}</select></div><div class="pane-body" id="pane-body-${stage}">${body(stage)}</div>${railsBefore?handle(previous,stage,' leading'):''}${next?handle(stage,next,''):''}</section>`;
  }).join('');
  for(const stage of Explorer.stages){$('#show-'+stage).checked=state[stage];$('#show-'+stage).disabled=state[stage]&&active.length===1;}
  document.querySelectorAll('.line[data-atom]').forEach(el=>el.onclick=event=>{
    if (!Explorer.shouldSelectCode(event,window.getSelection()?.toString()) || el.dataset.atom === item?.id) return;
    const panel = el.closest('.pane-body');
    const stage = panel.id.slice('pane-body-'.length);
    select(el.dataset.atom,{stage,file:files[stage],top:panel.scrollTop,left:panel.scrollLeft});
  });
  document.querySelectorAll('[data-toggle]').forEach(el=>el.onclick=()=>{Panels.set(state,el.dataset.toggle,!state[el.dataset.toggle]);save();render(true);});
  document.querySelectorAll('[data-proof]').forEach(el=>el.ontoggle=()=>{
    if(el.open)openProofs.add(el.dataset.proof);else openProofs.delete(el.dataset.proof);
  });
  document.querySelectorAll('[data-source]').forEach(el=>el.onchange=()=>{files[el.dataset.source]=el.value;save();render();});
  document.querySelectorAll('[data-copy]').forEach(el=>el.onclick=async()=>{
    const text=visibleText(el.dataset.copy);
    try{await navigator.clipboard.writeText(text);}catch{const area=document.createElement('textarea');area.value=text;document.body.append(area);area.select();document.execCommand('copy');area.remove();}
  });
  document.querySelectorAll('[data-download]').forEach(el=>el.onclick=()=>{
    const file=data.files[files[el.dataset.download]],a=document.createElement('a');
    a.href=URL.createObjectURL(new Blob([file.text],{type:'text/plain'}));a.download=file.path.split('/').at(-1);a.click();setTimeout(()=>URL.revokeObjectURL(a.href),1000);
  });
  document.querySelectorAll('[data-declaration]').forEach(el=>el.onchange=()=>{
    const d=data.declarations.find(d=>d.name===el.value); if(!d)return;
    const panel=$('#pane-body-'+el.dataset.declaration);
    panel.querySelector(`[data-line="${d.start}"]`)?.scrollIntoView({block:'center'});
    panel.querySelectorAll('.line').forEach(line=>line.classList.toggle('active-addition',+line.dataset.line>=d.start&&+line.dataset.line<=d.end));
  });
  wireResize();resize();bindVerso();
  if(state.mode==='files')for(const stage of active){const first=ranges(stage).find(r=>r.file===files[stage]);const panel=$('#pane-body-'+stage);const line=first&&panel?.querySelector(`[data-line="${first.start}"]`);const target=line;if(preserveScroll&&scroll.get(stage)!=null)panel.scrollTop=scroll.get(stage);else if(target)panel.scrollTop=Math.max(0,target.offsetTop-panel.offsetTop-45);}
}
function provenance() {
  const source = f => data.repository && data.revision && !data.dirty
    ? `<a href="${esc(data.repository+'/blob/'+data.revision+'/'+f.path.split('/').map(encodeURIComponent).join('/'))}" target="_blank" rel="noopener">${esc(f.path)}</a>` : esc(f.path);
  $('#provenance-body').innerHTML=`<p>Revision ${esc(data.revision||'unrecorded')}${data.dirty?' + local changes':''}. Spec and Bridge theorems take the assumptions listed below as explicit hypotheses; the only axioms are the opaque function symbols recorded by Aeneas. Assumptions are stated contracts, not verified library implementations.</p><p>${data.declarations.filter(d=>d.status==='assumption').map(d=>esc(d.name)).join('<br>')}</p><p>${data.coverage?`${data.coverage.checkedBridge} atoms have checked bridge theorems; ${data.coverage.bridge} have associated evidence.`:'Atom coverage is unknown until extraction.'}</p><p>${esc(bundle.lean)}${data.versions?` · Aeneas ${esc(data.versions.aeneas)} · Charon ${esc(data.versions.charon)}`:''}</p><p>${(bundle.references||[]).map(r=>`<a href="${esc(r.url)}" target="_blank" rel="noopener">${esc(r.path)}</a>`).join('<br>')}</p><table class="provenance-table">${Object.values(data.files).map(f=>`<tr><th>${esc(f.stage)}</th><td>${source(f)}<span class="hash">SHA-256 ${f.sha256}</span></td></tr>`).join('')}</table>${data.external?.length?`<h3>External boundaries</h3><ul>${data.external.map(d=>`<li>${esc(d.name)} (${esc(d.category)})</li>`).join('')}</ul>`:''}`;
  $('#provenance-dialog').showModal();
}
$('#example-picker').innerHTML='<option value="">Overview</option>'+bundle.examples.map(e=>`<option value="${esc(e.id)}">${esc(e.name)}</option>`).join('');
$('#example-picker').onchange=e=>{
  if(!e.target.value){location.hash='view=home';return;}
  home=false;data=Explorer.example(bundle,e.target.value);state.example=data.id;select(null);
};
$('#home').innerHTML=overview();
$('#item-picker').onchange=e=>select(e.target.value);
$('#focus-declaration').onclick=()=>{state.mode=Explorer.toggleMode(state.mode);save();render();};
for(const stage of Explorer.stages)$('#show-'+stage).onchange=e=>{Panels.set(state,stage,e.target.checked);save();render(true);};
$('#show-support').onchange=e=>{state.support=e.target.checked;for(const stage of Explorer.stages)files[stage]=Explorer.file(data,item,stage,files[stage],state.support);save();render();};
$('#font-size').onchange=e=>{state.font=Math.min(18,Math.max(10,Number(e.target.value)||12));save();render();};
$('#provenance').onclick=provenance;
$('#close-dialog').onclick=()=>$('#provenance-dialog').close();
window.addEventListener('hashchange',()=>{load();render();});
window.addEventListener('blur',()=>endDrag(false));
new ResizeObserver(resize).observe($('#panes'));
document.addEventListener('pointerdown',e=>{if(!$('#view-menu').contains(e.target))$('#view-menu').open=false;});
// Lean rendered by Verso, when the build includes it: hover types and docstrings, binding
// highlights, and the proof state after each tactic. The page is drawn first with its plain
// colouring and again when Verso's markup has been unpacked.
let versoReady = false;
function bindVerso() {
  if (!versoReady) return;
  document.querySelectorAll('.hl.lean .token, .hl.lean .has-info, .hl.lean .tactic').forEach(el => el._tippy?.destroy());
  // A tactic that spans several lines is cut into one piece per line, and only the last piece
  // carries the proof state: give the other pieces a copy.
  document.querySelectorAll('.hl.lean .tactic').forEach(el => {
    if (el.querySelector(':scope > .tactic-state')) return;
    const state = el.closest('.pane')?.querySelector(`.tactic[data-tid="${CSS.escape(el.dataset.tid || '')}"] > .tactic-state`);
    if (state) el.append(state.cloneNode(true)); else el.classList.remove('tactic');
  });
  window.versoInit();
}
async function loadVerso() {
  const packed = document.getElementById('verso-data');
  if (!packed || !window.versoInit || !window.DecompressionStream) return;
  const bytes = Uint8Array.from(atob(packed.textContent), c => c.charCodeAt(0));
  const stream = new Blob([bytes]).stream().pipeThrough(new DecompressionStream('deflate-raw'));
  const verso = JSON.parse(await new Response(stream).text());
  for (const example of bundle.examples) for (const file of Object.values(example.files)) file.html = verso.files[file.path];
  window.versoDocs = Promise.resolve(verso.docs);
  versoReady = true;
  render(true);
}
load();save();render();loadVerso();
})();
