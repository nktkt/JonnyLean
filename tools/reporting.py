"""Offline, escaped HTML reports generated from recorded verification evidence."""
from __future__ import annotations

import html
import json
from pathlib import Path
import tomllib


def render_dashboard(root: Path) -> Path:
    from tools.jonnylean import capture_inputs, check_review, OperationError, Rejected
    config = tomllib.loads((root / "jonnylean.toml").read_text())
    esc = lambda value: html.escape(str(value), quote=True)
    cards = []
    passed = 0
    for task in config["tasks"]:
        try:
            report = json.loads((root / "artifacts" / task["id"] / "report.json").read_text())
            if (not isinstance(report, dict) or not isinstance(report.get("target", {}), dict)
                or not isinstance(report.get("review", {}), dict)):
                raise ValueError("Malformed report")
            axioms = report.get("target", {}).get("axioms", [])
            if not isinstance(axioms, list) or any(not isinstance(a, str) for a in axioms):
                raise ValueError("Malformed axiom list")
            current = report.get("inputs") == capture_inputs(root, task)
            if current and report.get("review", {}).get("status") == "approved_current":
                try:
                    check_review(root, task, report)
                except (Rejected, OperationError, ValueError, OSError) as error:
                    report["status"] = "fail"
                    report["error"] = str(error)
        except (OSError, ValueError, OperationError):
            report, current = {}, False
        status = report.get("status", "not_run") if current else "stale" if report else "not_run"
        if status == "pass":
            passed += 1
        target = report.get("target", {})
        review = report.get("review", {})
        cards.append(f'''<article class="card"><div class="row"><span class="id">{esc(task['id'])}</span>
<span class="badge {esc(status)}">{esc(status.upper())}</span></div>
<h2>{esc(task['title'])}</h2><p class="mono">{esc(task['declaration'])}</p>
<pre>{esc(target.get('type', '検証を実行すると命題を表示します。'))}</pre>
<dl><dt>公理依存</dt><dd>{esc(', '.join(target.get('axioms', [])) or 'なし / 未検査の場合はJSONを参照')}</dd>
<dt>機械検証</dt><dd>{esc(report.get('mechanical', 'not_run'))}</dd>
<dt>AIレビュー</dt><dd>{esc(review.get('status', 'not_checked'))}</dd>
<dt>人間の承認</dt><dd>未記録</dd></dl>
<p class="error">{esc(report.get('error', ''))}</p>
<nav><a href="../{esc(task['spec'])}">仕様</a><a href="{esc(task['id'])}/report.json">検証JSON</a>
<a href="../{esc(task['review'])}">AIレビュー記録</a></nav></article>''')
    document = f'''<!doctype html><html lang="ja"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>JonnyLean · Verification</title><style>
:root{{color-scheme:light;font-family:system-ui,sans-serif;background:#f3f5f7;color:#17232f}}*{{box-sizing:border-box}}
body{{margin:0}}header,main,footer{{max-width:1160px;margin:auto;padding:32px 24px}}header{{padding-top:56px}}
.eyebrow,.id{{font-size:12px;letter-spacing:.13em;color:#536779;font-weight:700}}h1{{font-size:44px;margin:12px 0}}
.lead{{color:#536779;line-height:1.8}}.grid{{display:grid;grid-template-columns:repeat(auto-fit,minmax(320px,1fr));gap:20px}}
.card{{background:white;border:1px solid #dde3e8;border-radius:16px;padding:24px;min-width:0}}.row{{display:flex;justify-content:space-between}}
h2{{font-size:20px;line-height:1.6}}.mono,pre{{font-family:ui-monospace,monospace;font-size:12px;overflow-wrap:anywhere}}
pre{{background:#f5f7f9;padding:16px;white-space:pre-wrap;line-height:1.7;border-radius:8px;min-height:96px}}
.badge{{font-size:11px;font-weight:700;padding:5px 10px;border-radius:20px;background:#edf0f3}}.pass{{background:#dcf2e8;color:#14583d}}
.fail,.error{{color:#9f342c}}.stale{{background:#fff2d7;color:#775211}}dl{{display:grid;grid-template-columns:110px 1fr;font-size:13px;gap:10px}}
dd{{margin:0;overflow-wrap:anywhere}}dt{{color:#647383}}nav{{display:flex;gap:16px;font-size:13px}}a{{color:#175ca3}}footer{{color:#647383;font-size:12px;line-height:1.9}}
</style><header><div class="eyebrow">FORMAL MATHEMATICS / HUMAN DIRECTED · AI IMPLEMENTED</div>
<h1>JonnyLean</h1><p class="lead">初等整数論・組合せ論 — 現在の入力に一致する合格結果 {passed} / {len(cards)} 件</p>
<p class="lead">仕様 → Leanの証明 → 公理監査 → 独立AIレビュー</p></header>
<main class="grid">{''.join(cards)}</main><footer>このページはローカルで生成された検証結果です。外部通信・JavaScriptはありません。
AIレビュー記録は自己申告であり、人間の承認や自然言語との同値性証明ではありません。入力が変わった結果は STALE と表示します。</footer></html>'''
    destination = root / "artifacts" / "index.html"
    destination.parent.mkdir(exist_ok=True)
    destination.write_text(document)
    return destination
