"""Keep adversarial regression copies small; the full catalog is checked separately."""
import json
from pathlib import Path


def core_only(root: Path) -> None:
    from tools.catalog import generated
    tasks = json.loads((root / 'catalog/fragments/core.json').read_text())
    keep = {t['module'].replace('.', '/') + '.lean' for t in tasks}
    for path in (root / 'JonnyLean').rglob('*.lean'):
        if str(path.relative_to(root)) not in keep:
            path.unlink()
    for path in (root / 'catalog/fragments').glob('*.json'):
        if path.name != 'core.json':
            path.unlink()
    for folder, field in [('contracts', 'contract'), ('specs', 'spec'), ('reviews', 'review')]:
        keep_paths = {t[field] for t in tasks}
        for path in (root / folder).glob('*'):
            if path.is_file() and (path.suffix in ('.lean', '.json') or (folder == 'specs' and path.suffix == '.md')):
                if str(path.relative_to(root)) not in keep_paths:
                    path.unlink()
    (root / 'JonnyLean.lean').write_text(''.join(f'import {t["module"]}\n' for t in tasks))
    manifest, imports, _ = generated(root)
    (root / 'jonnylean.toml').write_text(manifest)
    (root / 'JonnyLean.lean').write_text(imports)
