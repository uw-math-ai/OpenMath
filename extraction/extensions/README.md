# `extensions/` — hand-curated additions to the extraction data

This is the **only** place to add formal content that did not come from
the auto-extraction pipeline. Files here survive `extraction/raw_text/`
re-extraction. Everything else under `extraction/` is regenerated.

**Read the full guide before editing anything here:** [`../EXTENSIBILITY.md`](../EXTENSIBILITY.md).

## Files

| File | Holds | Recipe |
|---|---|---|
| `missing_statements.json` | Textbook entities the extractor missed | EXTENSIBILITY §2 |
| `helper_entities.json` | Lean-side helpers (NOT in Butcher), `aux:` IDs | EXTENSIBILITY §3 |
| `extra_references.json` | Manually-curated dependency edges | both recipes |

All three start as empty arrays `[]`. Append objects; do not rewrite
the file structure.

## After editing

```bash
cd extraction && python -m pipeline.build_formalization_data
```

This re-merges everything, re-runs cycle-breaking on the extended graph,
and refreshes `formalization_data/` with the new entities.
