"""Offline HTML catalog with separately checked review and verification evidence."""
from __future__ import annotations

import base64
import hashlib
import html
import json
from pathlib import Path, PurePosixPath
import tomllib
from urllib.parse import quote


_STATUSES = ("pass", "fail", "error", "stale", "not_run")
_FILTER_SCRIPT = """(() => {
  const cards = Array.from(document.querySelectorAll('.card'));
  const query = document.getElementById('query');
  const domain = document.getElementById('domain');
  const status = document.getElementById('status');
  const count = document.getElementById('visible-count');
  const empty = document.getElementById('empty-results');
  function filter() {
    const words = query.value.trim().toLowerCase().split(/\\s+/).filter(Boolean);
    let visible = 0;
    for (const card of cards) {
      const matches = (!domain.value || card.dataset.domain === domain.value) &&
        (!status.value || card.dataset.status === status.value) &&
        words.every(word => card.dataset.search.toLowerCase().includes(word));
      card.hidden = !matches;
      if (matches) visible += 1;
    }
    count.textContent = `${visible} / ${cards.length} 件を表示`;
    empty.hidden = visible !== 0;
  }
  query.addEventListener('input', filter);
  domain.addEventListener('change', filter);
  status.addEventListener('change', filter);
  document.getElementById('reset-filters').addEventListener('click', () => {
    query.value = ''; domain.value = ''; status.value = ''; filter(); query.focus();
  });
  filter();
})();"""


def _escape(value: object) -> str:
    return html.escape(str(value), quote=True)


def _project_link(path: str, label: str) -> str:
    """Only emit project-relative links; URL-encode before HTML escaping."""
    if (not isinstance(path, str) or not path or path.startswith("/") or "\\" in path
            or ".." in PurePosixPath(path).parts or any(ord(c) < 32 for c in path)):
        return f'<span>{_escape(label)}（無効なパス）</span>'
    return f'<a href="../{_escape(quote(path, safe="/-._~"))}">{_escape(label)}</a>'


def _read_report(path: Path) -> dict:
    report = json.loads(path.read_text(encoding="utf-8"))
    if (not isinstance(report, dict) or not isinstance(report.get("target", {}), dict)
            or not isinstance(report.get("review", {}), dict)):
        raise ValueError("Malformed report")
    target, review = report.get("target", {}), report.get("review", {})
    axioms = target.get("axioms", [])
    if not isinstance(axioms, list) or any(not isinstance(a, str) for a in axioms):
        raise ValueError("Malformed axiom list")
    for value in (report.get("status", "not_run"), report.get("mechanical", "not_run"),
                  target.get("type", ""), review.get("status", "not_checked")):
        if not isinstance(value, str):
            raise ValueError("Malformed report status or target")
    for key in ("inputs", "verification_inputs"):
        if key in report and (not isinstance(report[key], dict)
                              or any(not isinstance(k, str) or not isinstance(v, str)
                                     for k, v in report[key].items())):
            raise ValueError("Malformed input fingerprint")
    return report


def render_dashboard(root: Path) -> Path:
    from tools.jonnylean import (capture_inputs, capture_verification_inputs, check_review,
                                OperationError, Rejected)

    config = tomllib.loads((root / "jonnylean.toml").read_text(encoding="utf-8"))
    tasks = config["tasks"]
    try:
        verification_inputs = capture_verification_inputs(root)
        verification_error = ""
    except (OSError, ValueError, OperationError) as error:
        verification_inputs = None
        verification_error = str(error)
    cards, passed, mechanical_passed, reviewed = [], 0, 0, 0
    domains = sorted({str(task.get("domain", "unclassified")) for task in tasks})
    for task in tasks:
        errors = []
        try:
            report = _read_report(root / "artifacts" / task["id"] / "report.json")
        except FileNotFoundError:
            report = {}
        except (OSError, ValueError) as error:
            report = {}
            errors.append(f"検証JSONを読み込めません: {error}")
        try:
            semantic_inputs = capture_inputs(root, task)
        except (OSError, ValueError, OperationError) as error:
            semantic_inputs = None
            errors.append(f"意味レビューの入力を確認できません: {error}")
        semantic_current = semantic_inputs is not None and report.get("inputs") == semantic_inputs
        verification_current = (verification_inputs is not None
                                and report.get("verification_inputs") == verification_inputs)
        current = semantic_current and verification_current
        # Evaluate the present review record independently of old report contents.
        # This can stay current while unrelated project changes stale a global run.
        probe = {"inputs": semantic_inputs, "review": {"status": "not_checked"}}
        review_ok = False
        if semantic_inputs is not None:
            try:
                check_review(root, task, probe)
                review_ok = True
            except (Rejected, OperationError, ValueError, OSError) as error:
                if probe["review"].get("status") in {"not_checked", "pending"}:
                    probe["review"]["status"] = "invalid"
                errors.append(str(error))
        else:
            probe["review"]["status"] = "unavailable"
        review = probe["review"]
        if review_ok:
            reviewed += 1
        status = report.get("status", "not_run") if current else "stale" if report else "not_run"
        if status not in _STATUSES:
            status = "error"
        # Never trust a cached approval after its record changes or disappears.
        if current and report.get("review", {}).get("status") == "approved_current" and not review_ok:
            status = "fail"
        mechanical = report.get("mechanical", "not_run") if current else "stale" if report else "not_run"
        passed += status == "pass"
        mechanical_passed += mechanical == "pass"
        target = report.get("target", {})
        domain = str(task.get("domain", "unclassified"))
        dependencies = task.get("depends_on", [])
        dependency_links = ", ".join(
            f'<a href="#{_escape(quote(dependency, safe="-._~"))}">{_escape(dependency)}</a>'
            for dependency in dependencies
        ) or "なし"
        search = " ".join(str(task.get(key, "")) for key in
                          ("id", "title", "domain", "description", "tags", "module", "declaration", "depends_on"))
        if report.get("error"):
            errors.insert(0, str(report["error"]))
        if verification_error:
            errors.append(f"全体検証の入力を確認できません: {verification_error}")
        links = [
            _project_link(task["spec"], "仕様"),
            _project_link(task["module"].replace(".", "/") + ".lean", "Lean証明"),
            _project_link(task["contract"], "契約"),
            _project_link(task["review"], "AIレビュー記録"),
            _project_link(f"artifacts/{task['id']}/report.json", "検証JSON"),
        ]
        cards.append(f'''<article class="card" id="{_escape(task['id'])}" data-domain="{_escape(domain)}" data-status="{_escape(status)}" data-search="{_escape(search)}">
<div class="row"><span class="id">{_escape(task['id'])}</span><span class="badge {_escape(status)}">{_escape(status.upper())}</span></div>
<p class="domain">{_escape(domain)}</p><h2>{_escape(task['title'])}</h2>
<p class="description">{_escape(task.get('description', ''))}</p><p class="mono">{_escape(task['declaration'])}</p>
<pre>{_escape(target.get('type', '検証を実行すると命題を表示します。'))}</pre>
<dl><dt>全体の機械検証</dt><dd>{_escape(mechanical)}</dd>
<dt>機械検証の鮮度</dt><dd>{'現在の全体入力と一致' if current else '全体検証の再実行が必要' if report else '未実行'}</dd>
<dt>意味レビューの現況</dt><dd>{_escape(review.get('status', 'not_checked'))}</dd>
<dt>レビューの範囲</dt><dd>この課題と依存する仕様・証明</dd>
<dt>依存タスク</dt><dd>{dependency_links}</dd>
<dt>公理依存</dt><dd>{_escape(', '.join(target.get('axioms', [])) or ('なし' if target else '未検査'))}</dd>
<dt>人間の承認</dt><dd>未記録</dd></dl>
<p class="error">{_escape(' / '.join(dict.fromkeys(errors)))}</p>
<nav aria-label="{_escape(task['id'])} の資料">{''.join(links)}</nav></article>''')
    domain_options = ''.join(f'<option value="{_escape(domain)}">{_escape(domain)}</option>' for domain in domains)
    status_options = ''.join(f'<option value="{status}">{status.upper()}</option>' for status in _STATUSES)
    script_hash = base64.b64encode(hashlib.sha256(_FILTER_SCRIPT.encode()).digest()).decode()
    csp = (f"default-src 'none'; script-src 'sha256-{script_hash}'; style-src 'unsafe-inline'; "
           "connect-src 'none'; base-uri 'none'; form-action 'none'")
    document = f'''<!doctype html><html lang="ja"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<meta http-equiv="Content-Security-Policy" content="{_escape(csp)}"><title>JonnyLean · Verification</title><style>
:root{{color-scheme:light;font-family:system-ui,sans-serif;background:#f3f5f7;color:#17232f}}*{{box-sizing:border-box}}
body{{margin:0}}header,main,footer,.controls{{max-width:1280px;margin:auto;padding:24px}}header{{padding-top:48px}}
.eyebrow,.id{{font-size:12px;letter-spacing:.1em;color:#536779;font-weight:700}}h1{{font-size:44px;margin:12px 0}}
.lead,.description{{color:#536779;line-height:1.8}}.grid{{display:grid;grid-template-columns:repeat(auto-fit,minmax(min(100%,350px),1fr));gap:20px}}
.card{{background:white;border:1px solid #dde3e8;border-radius:16px;padding:24px;min-width:0;scroll-margin-top:20px}}.card[hidden]{{display:none}}
.row{{display:flex;justify-content:space-between;align-items:center;gap:12px}}h2{{font-size:20px;line-height:1.6;margin-top:8px}}
.domain{{font-size:12px;color:#647383;margin-bottom:0}}.mono,pre{{font-family:ui-monospace,monospace;font-size:12px;overflow-wrap:anywhere}}
pre{{background:#f5f7f9;padding:16px;white-space:pre-wrap;line-height:1.7;border-radius:8px;min-height:96px}}
.badge{{font-size:11px;font-weight:700;padding:5px 10px;border-radius:20px;background:#edf0f3}}.pass{{background:#dcf2e8;color:#14583d}}
.fail,.error{{color:#9f342c}}.stale{{background:#fff2d7;color:#775211}}dl{{display:grid;grid-template-columns:130px 1fr;font-size:13px;gap:10px}}
dd{{margin:0;overflow-wrap:anywhere}}dt{{color:#647383}}nav{{display:flex;flex-wrap:wrap;gap:12px;font-size:13px}}a{{color:#175ca3}}
.filters{{display:flex;flex-wrap:wrap;align-items:end;gap:16px}}label{{display:grid;gap:8px;font-size:13px}}.search{{flex:1;min-width:220px}}
input,select,button{{font:inherit;padding:10px 12px;border:1px solid #bfcbd5;border-radius:8px;background:white;color:inherit}}
button{{cursor:pointer}}:focus-visible{{outline:3px solid #417bb6;outline-offset:3px}}#visible-count{{font-size:13px;color:#536779}}
.error{{font-size:12px;overflow-wrap:anywhere;line-height:1.7}}.error:empty,.description:empty{{display:none}}
footer{{color:#647383;font-size:12px;line-height:1.9}}
</style></head><body><header><div class="eyebrow">FORMAL MATHEMATICS / HUMAN DIRECTED · AI IMPLEMENTED</div>
<h1>JonnyLean</h1><p class="lead">数学ライブラリ・検証カタログ — 現在の入力に一致する合格結果 {passed} / {len(cards)} 件</p>
<p class="lead">全体の機械検証 PASS: {mechanical_passed} 件 · 現在の依存範囲に対する意味レビュー承認: {reviewed} 件</p>
<p class="lead">機械検証はプロジェクト全体、意味レビューは課題とその依存範囲に結び付いています。</p></header>
<section class="controls" aria-label="課題を絞り込む"><div class="filters">
<label class="search" for="query">課題・定理・タグを検索<input id="query" type="search" placeholder="例: JL-042、sorting、有限集合" autocomplete="off"></label>
<label for="domain">分野<select id="domain"><option value="">すべての分野</option>{domain_options}</select></label>
<label for="status">レポート状態<select id="status"><option value="">すべての状態</option>{status_options}</select></label>
<button type="button" id="reset-filters">絞り込みを解除</button></div>
<p id="visible-count" aria-live="polite">{len(cards)} / {len(cards)} 件を表示</p>
<p id="empty-results" hidden>条件に一致する課題はありません。</p><noscript>検索にはJavaScriptが必要です。すべての課題を表示しています。</noscript></section>
<main class="grid">{''.join(cards)}</main><footer>このページはローカルで生成され、検索・絞り込みも端末内で動作します。外部通信はありません。
AIレビュー記録は自己申告であり、人間の承認や自然言語との同値性証明ではありません。
STALE は記録された全体検証と現在の入力が一致しない状態です。意味レビューの現況は現在のレビュー記録を別に確認して表示します。</footer>
<script type="text/javascript">{_FILTER_SCRIPT}</script></body></html>'''
    destination = root / "artifacts" / "index.html"
    destination.parent.mkdir(exist_ok=True)
    destination.write_text(document, encoding="utf-8")
    return destination
