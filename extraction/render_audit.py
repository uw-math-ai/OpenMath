"""Render extraction/audit_sample.json to a self-contained HTML viewer.

Shows, per entity: the judge verdict, the textbook statement, the blind
Lean->NL back-translation, and the raw Lean statement. Re-run after
back_translate.py to refresh the back-translation panel.
"""
import json
from pathlib import Path

IN = Path("extraction/audit_sample.json")
OUT = Path("extraction/audit_sample.html")

data = json.loads(IN.read_text(encoding="utf-8"))
data_js = json.dumps(data, ensure_ascii=False)

HTML = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<title>Audit Sample — Lean vs Butcher</title>
<script>
MathJax = {
  tex: {
    inlineMath: [['$','$'], ['\\(','\\)']],
    displayMath: [['\\[','\\]']],
    processEscapes: true,
  },
  options: { skipHtmlTags: ['script','noscript','style','textarea','pre','code'] },
  startup: { typeset: false },
};
</script>
<script async src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js"></script>
<style>
  *, *::before, *::after { box-sizing: border-box; margin: 0; padding: 0; }
  body { font-family: system-ui, -apple-system, sans-serif; background: #f5f5f7; color: #1a1a1a; padding: 1.5rem; }
  header { margin-bottom: 1.5rem; }
  header h1 { font-size: 1.4rem; font-weight: 600; }
  header p { color: #64748b; font-size: .9rem; margin-top: .25rem; }
  .legend { margin-top: .75rem; display: flex; gap: 1rem; font-size: .85rem; }
  .legend span { padding: .15rem .55rem; border-radius: 6px; font-weight: 600; }
  .ok { background: #dcfce7; color: #14532d; }
  .bad { background: #fee2e2; color: #7f1d1d; }
  .grid { display: grid; grid-template-columns: 1fr 1fr; gap: 1rem; }
  @media (max-width: 1300px) { .grid { grid-template-columns: 1fr; } }
  .col h2 { font-size: 1rem; font-weight: 600; margin-bottom: .75rem; padding: .5rem .75rem; border-radius: 6px; }
  .col.ok h2 { background: #dcfce7; color: #14532d; }
  .col.bad h2 { background: #fee2e2; color: #7f1d1d; }
  .card { background: white; border: 1px solid #e2e8f0; border-radius: 8px; padding: 1rem; margin-bottom: .9rem; box-shadow: 0 1px 2px rgba(0,0,0,.03); }
  .card-head { display: flex; align-items: baseline; gap: .5rem; margin-bottom: .5rem; flex-wrap: wrap; }
  .id { font-family: ui-monospace, Menlo, monospace; font-weight: 600; color: #1e40af; font-size: .9rem; }
  .kind { color: #64748b; font-size: .8rem; text-transform: uppercase; }
  .name { color: #334155; font-size: .9rem; flex: 1; }
  .score-tag { padding: .1rem .5rem; border-radius: 999px; font-size: .78rem; font-weight: 600; }
  .score-3 { background: #dcfce7; color: #14532d; }
  .score-1 { background: #fee2e2; color: #7f1d1d; }
  .judge-row { background: #f8fafc; border-left: 3px solid #6366f1; padding: .55rem .75rem; margin-bottom: .75rem; font-size: .85rem; border-radius: 0 6px 6px 0; }
  .judge-row .reason { font-style: italic; color: #475569; margin-top: .2rem; }
  .judge-row .imp { font-family: ui-monospace, Menlo, monospace; font-size: .78rem; color: #64748b; }
  .field { margin-top: .65rem; }
  .field-label { font-size: .72rem; color: #64748b; font-weight: 600; text-transform: uppercase; letter-spacing: .04em; margin-bottom: .25rem; }
  .nl-text { background: #fffbeb; border: 1px solid #fde68a; padding: .55rem .75rem; border-radius: 6px; font-size: .92rem; line-height: 1.5; white-space: pre-wrap; word-wrap: break-word; }
  .backtrans { background: #eff6ff; border: 1px solid #bfdbfe; padding: .55rem .75rem; border-radius: 6px; font-size: .92rem; line-height: 1.5; white-space: pre-wrap; word-wrap: break-word; }
  pre.lean { background: #0f172a; color: #e2e8f0; padding: .65rem .85rem; border-radius: 6px; font-family: ui-monospace, "SF Mono", Menlo, monospace; font-size: .82rem; line-height: 1.45; overflow-x: auto; white-space: pre; }
  pre.lean .keyword { color: #c084fc; }
  details.context-wrap { margin-top: .65rem; }
  details.context-wrap summary { cursor: pointer; font-size: .72rem; color: #64748b; font-weight: 600; text-transform: uppercase; letter-spacing: .04em; padding: .15rem 0; }
  details.context-wrap[open] summary { margin-bottom: .25rem; }
</style>
</head>
<body>
<header>
  <h1>Lean vs Butcher — Audit Sample</h1>
  <p>20 entities (10 judged faithful, 10 judged divergent). Compare the <b>textbook statement</b> (yellow) against the <b>blind Lean&rarr;NL back-translation</b> (blue): agreement &rArr; faithful; divergence &rArr; Lean says something different.</p>
  <div class="legend">
    <span class="ok">score 3 = judge says faithful</span>
    <span class="bad">score 1 = judge says divergent</span>
  </div>
</header>
<div class="grid">
  <section class="col ok"><h2>Judge said FAITHFUL (score 3)</h2><div id="ok-list"></div></section>
  <section class="col bad"><h2>Judge said DIVERGENT (score 1)</h2><div id="bad-list"></div></section>
</div>

<script>
const DATA = __DATA__;
function escapeHtml(s){ if(!s) return ''; return String(s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;'); }
function highlightLean(s){
  if(!s) return '';
  const kws=['theorem','lemma','def','abbrev','structure','class','instance','inductive','where','noncomputable','Prop','Type','fun','let','match','with'];
  let out=escapeHtml(s);
  for(const kw of kws){
    const re=new RegExp('(?<![A-Za-z_])('+kw.replace(/([\\^$.*+?()[\]{}|])/g,'\\$1')+')(?![A-Za-z_])','g');
    out=out.replace(re,'<span class="keyword">$1</span>');
  }
  return out;
}
function makeCard(e){
  const sc = e.judge_score===3 ? 'score-3':'score-1';
  return `
  <div class="card">
    <div class="card-head">
      <span class="id">${escapeHtml(e.id)}</span>
      <span class="kind">${escapeHtml(e.kind||'')}</span>
      <span class="name">${escapeHtml(e.name||'')}</span>
      <span class="score-tag ${sc}">score ${e.judge_score}</span>
    </div>
    <div class="judge-row">
      <div class="imp">L&rarr;NL = ${e.lean_implies_nl} &nbsp;|&nbsp; NL&rarr;L = ${e.nl_implies_lean}</div>
      <div class="reason">"${escapeHtml(e.judge_reason||'')}"</div>
    </div>
    <div class="field">
      <div class="field-label">① Textbook statement</div>
      <div class="nl-text">${escapeHtml(e.statement_text||'(none)')}</div>
    </div>
    <div class="field">
      <div class="field-label">② Blind back-translation of the Lean</div>
      <div class="backtrans">${escapeHtml(e.lean_back_translation||'(not yet generated)')}</div>
    </div>
    ${e.context_latex?`<details class="context-wrap"><summary>Surrounding context (textbook prose)</summary><div class="nl-text">${escapeHtml(e.context_latex)}</div></details>`:''}
    <div class="field">
      <div class="field-label">③ Lean statement <span style="font-weight:400;text-transform:none;color:#94a3b8;">${escapeHtml(e.lean_file||'')}</span></div>
      <pre class="lean">${highlightLean(e.lean_statement||'(none)')}</pre>
    </div>
  </div>`;
}
document.getElementById('ok-list').innerHTML = DATA['scored_correct (judge=3)'].map(makeCard).join('');
document.getElementById('bad-list').innerHTML = DATA['scored_incorrect (judge=1)'].map(makeCard).join('');
const wait=setInterval(()=>{ if(window.MathJax&&window.MathJax.typesetPromise){clearInterval(wait);MathJax.typesetPromise();} },100);
</script>
</body>
</html>
"""

OUT.write_text(HTML.replace("__DATA__", data_js), encoding="utf-8")
print(f"Wrote {OUT}  ({OUT.stat().st_size:,} bytes)")
