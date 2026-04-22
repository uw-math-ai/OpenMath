"""Re-extract the 'introduces' field with peer-aware qualified names.

Two-pass design:
1. Pass 1 — per-entity DeepSeek call. Full statement + prompt asking for
   topically-qualified concept names ("convergent matrix", not "convergent").
2. Pass 2 — collision resolution. For any term still appearing in 2+
   entities after Pass 1, batch the colliders and ask DeepSeek for unique
   qualified names per member.

Both passes cache by content hash in raw_text/introduces_cache.json so
re-runs are free unless underlying statement text changes.

Usage:
    python -m pipeline.fix_introduces                  # cache-only (no API)
    python -m pipeline.fix_introduces --run-api        # full re-extraction
    python -m pipeline.fix_introduces --run-api --limit 10
    python -m pipeline.fix_introduces --dry-run        # cost estimate
"""
from __future__ import annotations

import argparse
import collections
import hashlib
import json
import os
import re
import time
from pathlib import Path

from pipeline.config import RAW_TEXT_DIR

try:
    from dotenv import load_dotenv
    load_dotenv(RAW_TEXT_DIR.parent / ".env")
except ImportError:
    pass


CACHE_PATH = RAW_TEXT_DIR / "introduces_cache.json"


# ── Prompts (also documented in deepseek_prompts.md) ───────────────────

PASS1_SYSTEM = """\
You are a mathematical terminology extractor for Butcher's "Numerical \
Methods for Ordinary Differential Equations". Given one statement, \
identify the named concepts it introduces, qualified by topic so each \
name is globally unambiguous within the textbook.\
"""

PASS1_USER = """\
Below is {kind} {number} from Butcher's textbook:

{latex_body}

Identify ONLY the concepts that this {kind} CREATES or FORMALLY DEFINES \
— meaning the term receives its meaning here for the first time. Mere \
mention or use of an existing concept is NOT introduction.

Strong evidence that a concept is introduced here:
- Term in single quotes (e.g., "A square matrix A is 'convergent' if …")
- Term in italic emphasis (\\emph{{X}} or \\textit{{X}})
- Phrases like "is called X", "is said to be X", "we define X to be …", \
"is termed X", "is known as X"

CRITICAL — kind matters:
- Definitions are the primary place where new concepts are introduced. \
Look hard for them.
- Theorems, lemmas, and corollaries USUALLY introduce no new concepts; \
they state properties of pre-existing concepts. If a theorem mentions \
"Lipschitz condition", "stepsize", "Runge–Kutta method", or any other \
term that is defined elsewhere in the textbook, do NOT include it. \
Return [] for theorems and lemmas unless they explicitly define a new \
named concept using the markers above (this is rare).

CRITICAL — qualify with topic:
The textbook reuses bare words like "convergent", "consistent", "stable", \
"order" across topics (matrices, Runge–Kutta methods, linear multistep \
methods, general linear methods). When you do include a concept, qualify \
it with topical context so the name is globally unambiguous.

Examples of good qualified names:
- A square matrix being 'convergent' → "convergent matrix"
- A linear multistep method being 'convergent' → "convergent linear multistep method"
- A general linear method being 'consistent' → "consistent general linear method"

Do NOT include:
- Variables or symbols used but not defined (f, y, A, h, etc.)
- References to other named theorems or lemmas
- Generic descriptive words ("method", "condition", "order", "property", \
"step", "approximation", "solution")
- Concepts the statement merely USES rather than DEFINES
- Bare ambiguous terms — always qualify by topic

Return a JSON array of qualified strings only. If none, return [].
Example: ["convergent matrix"]
"""

PASS2_SYSTEM = """\
You are a mathematical terminology disambiguator for Butcher's textbook. \
Multiple statements have been tagged with the same concept name even \
though they are about distinct topics. For each, propose a uniquely \
qualified name.\
"""

PASS2_USER = """\
The following {n} statements all currently list `"{term}"` as a concept \
they introduce, but they are about distinct topics. For each, propose a \
unique qualified name that distinguishes it from the others. Use natural \
topical qualifiers (matrix, linear multistep method, Runge–Kutta method, \
general linear method, etc.).

{members_block}

Return a JSON object mapping each statement id to its qualified name(s) \
as a list of strings. Every id must be present. Each name must differ \
from the others.

Example response format:
{{"def:142B": ["convergent matrix"], "def:402A": ["convergent linear multistep method"], "def:512A": ["convergent general linear method"]}}
"""


# ── Helpers ────────────────────────────────────────────────────────────

def _make_id(kind: str, number: str) -> str:
    prefix = {"theorem": "thm", "definition": "def", "lemma": "lem", "corollary": "cor"}
    return f"{prefix.get(kind, kind[:3])}:{number}"


def _hash_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()[:12]


def _extract_body(latex: str, kind: str) -> str:
    """Extract \\begin{kind}...\\end{kind} body (excluding proof)."""
    m = re.search(
        r"\\begin\{" + re.escape(kind) + r"\}(?:\[[^\]]*\])?(.*?)\\end\{" + re.escape(kind) + r"\}",
        latex,
        re.DOTALL,
    )
    return m.group(1) if m else ""


def _stmt_body(stmt: dict, latex_map: dict[str, str]) -> str:
    """Get the most informative body text for a statement."""
    key = f"{stmt['kind']}:{stmt['number']}"
    latex = latex_map.get(key, "")
    body = _extract_body(latex, stmt["kind"]) if latex else ""
    return (body or stmt.get("text", "")).strip()


def _dedupe(concepts: list[str]) -> list[str]:
    seen = set()
    result = []
    for c in concepts:
        c = c.strip()
        if not c:
            continue
        key = c.lower()
        if key not in seen:
            seen.add(key)
            result.append(c)
    return result


def _parse_json_array(response: str) -> list[str]:
    """Best-effort extraction of a JSON array of strings from a model reply."""
    response = response.strip()
    fenced = re.search(r"```(?:json)?\s*(.*?)\s*```", response, re.DOTALL)
    if fenced:
        response = fenced.group(1).strip()
    m = re.search(r"\[.*\]", response, re.DOTALL)
    if not m:
        return []
    try:
        arr = json.loads(m.group(0))
        return [str(x).strip() for x in arr if isinstance(x, (str, int, float)) and str(x).strip()]
    except json.JSONDecodeError:
        return []


def _parse_json_object(response: str) -> dict:
    response = response.strip()
    fenced = re.search(r"```(?:json)?\s*(.*?)\s*```", response, re.DOTALL)
    if fenced:
        response = fenced.group(1).strip()
    m = re.search(r"\{.*\}", response, re.DOTALL)
    if not m:
        return {}
    try:
        return json.loads(m.group(0))
    except json.JSONDecodeError:
        return {}


# ── DeepSeek client ────────────────────────────────────────────────────

def _call_deepseek(system: str, user: str, api_key: str, max_tokens: int = 400) -> str:
    from openai import OpenAI
    client = OpenAI(api_key=api_key, base_url="https://api.deepseek.com")
    response = client.chat.completions.create(
        model="deepseek-chat",
        messages=[
            {"role": "system", "content": system},
            {"role": "user", "content": user},
        ],
        temperature=0.1,
        max_tokens=max_tokens,
    )
    return response.choices[0].message.content


# ── Cache ──────────────────────────────────────────────────────────────

def _load_cache() -> dict:
    if CACHE_PATH.exists():
        try:
            return json.loads(CACHE_PATH.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            print(f"  WARNING: {CACHE_PATH.name} unreadable; starting fresh")
    return {"pass1": {}, "pass2": {}}


def _save_cache(cache: dict) -> None:
    CACHE_PATH.write_text(json.dumps(cache, indent=2, ensure_ascii=False), encoding="utf-8")


# ── Pass 1 ─────────────────────────────────────────────────────────────

def _pass1_key(stmt_id: str, body: str) -> str:
    return f"{stmt_id}:{_hash_text(body)}"


def _pass1_draft(
    stmt: dict,
    body: str,
    api_key: str | None,
    cache: dict,
) -> tuple[list[str], bool]:
    """Return (introduces_list, was_api_call). Cache hit if was_api_call=False."""
    sid = _make_id(stmt["kind"], stmt["number"])
    key = _pass1_key(sid, body)
    if key in cache["pass1"]:
        return list(cache["pass1"][key]), False

    if api_key is None:
        return [], False

    user = PASS1_USER.format(
        kind=stmt["kind"],
        number=stmt["number"],
        latex_body=body[:2000],
    )
    response = _call_deepseek(PASS1_SYSTEM, user, api_key, max_tokens=300)
    terms = _dedupe(_parse_json_array(response))
    terms = [t for t in terms if 2 < len(t) < 100]
    cache["pass1"][key] = terms
    return terms, True


# ── Pass 2 ─────────────────────────────────────────────────────────────

def _detect_collisions(statements: list[dict]) -> dict[str, list[str]]:
    """Find terms requiring Pass 2 disambiguation.

    Two kinds of collisions:
    1. Exact: the same lowercase term appears in 2+ entities' introduces.
    2. Substring: term T appears in entity A's introduces AND a longer term
       containing T as a word-bounded substring appears in entity B (B != A).
       This catches the case where Pass 1 qualified one entity (e.g.
       "reduced method (from DJ-reduction)") but left another bare
       ("reduced method"), since the regex matcher would still cross-link
       them via the bare form.

    Returns {bare_term: sorted_member_ids}. For substring collisions the key
    is the SHORTER bare term, since that's what the downstream matcher will
    search for.
    """
    by_term: dict[str, list[str]] = collections.defaultdict(list)
    for s in statements:
        sid = _make_id(s["kind"], s["number"])
        for term in s.get("introduces", []) or []:
            key = term.lower().strip()
            if key:
                by_term[key].append(sid)

    collisions: dict[str, list[str]] = {}

    # Exact collisions
    for t, ids in by_term.items():
        unique_ids = sorted(set(ids))
        if len(unique_ids) > 1:
            collisions[t] = unique_ids

    # Substring collisions: shorter term inside longer term (word-bounded)
    all_terms = sorted(by_term.keys(), key=len)
    for short in all_terms:
        if short in collisions:
            continue
        # Word-bounded match against any longer term
        pattern = re.compile(r"(?<!\w)" + re.escape(short) + r"(?!\w)")
        members = set(by_term[short])
        for long in by_term:
            if long != short and len(long) > len(short) and pattern.search(long):
                members.update(by_term[long])
        unique_members = sorted(members)
        if len(unique_members) > 1:
            collisions[short] = unique_members

    return collisions


def _pass2_key(term: str, members: list[str], bodies: dict[str, str]) -> str:
    sorted_ids = sorted(members)
    combined = term + "|" + "|".join(f"{i}:{_hash_text(bodies[i])}" for i in sorted_ids)
    return f"{_hash_text(combined)}"


def _pass2_resolve(
    term: str,
    member_ids: list[str],
    member_stmts: dict[str, dict],
    member_bodies: dict[str, str],
    api_key: str | None,
    cache: dict,
) -> tuple[dict[str, list[str]], bool]:
    """Return ({stmt_id: [qualified_names]}, was_api_call)."""
    key = _pass2_key(term, member_ids, member_bodies)
    if key in cache["pass2"]:
        return dict(cache["pass2"][key]), False

    if api_key is None:
        return {}, False

    blocks = []
    for sid in sorted(member_ids):
        body = member_bodies[sid][:1200]
        blocks.append(f"[{sid}]\n{body}")
    members_block = "\n\n---\n\n".join(blocks)

    user = PASS2_USER.format(
        n=len(member_ids),
        term=term,
        members_block=members_block,
    )
    response = _call_deepseek(PASS2_SYSTEM, user, api_key, max_tokens=600)
    obj = _parse_json_object(response)

    cleaned: dict[str, list[str]] = {}
    for sid in member_ids:
        raw = obj.get(sid)
        if isinstance(raw, str):
            cleaned[sid] = [raw.strip()] if raw.strip() else []
        elif isinstance(raw, list):
            cleaned[sid] = _dedupe([str(x) for x in raw if str(x).strip()])
        else:
            cleaned[sid] = []

    cache["pass2"][key] = cleaned
    return cleaned, True


# ── Main ───────────────────────────────────────────────────────────────

def main() -> None:
    parser = argparse.ArgumentParser(description="Re-extract qualified 'introduces' field")
    parser.add_argument("--run-api", action="store_true",
                        help="Use DeepSeek (otherwise cache-only)")
    parser.add_argument("--limit", type=int, default=None,
                        help="Pass 1: only process first N statements (testing)")
    parser.add_argument("--dry-run", action="store_true",
                        help="Print plan and estimate without calling API")
    parser.add_argument("--only", type=str, default=None,
                        help="Pass 1: only process this stmt id (e.g., 'def:142B')")
    args = parser.parse_args()

    print("Re-extracting 'introduces' with qualified names ...")

    stmts_path = RAW_TEXT_DIR / "formal_statements.json"
    latex_path = RAW_TEXT_DIR / "formal_statements_latex.json"
    statements = json.loads(stmts_path.read_text(encoding="utf-8"))
    latex_stmts = json.loads(latex_path.read_text(encoding="utf-8"))
    latex_map = {f"{s['kind']}:{s['number']}": s.get("latex", "") or "" for s in latex_stmts}

    api_key = None
    if args.run_api:
        api_key = os.getenv("DEEPSEEK_API_KEY")
        if not api_key:
            print("  ERROR: DEEPSEEK_API_KEY not set in environment / .env")
            return

    cache = _load_cache()
    bodies = {_make_id(s["kind"], s["number"]): _stmt_body(s, latex_map) for s in statements}

    # --- Cost estimate / dry run ---
    if args.dry_run:
        # Pass 1: every statement that's not already cached
        uncached_pass1 = [
            s for s in statements
            if _pass1_key(_make_id(s["kind"], s["number"]),
                          bodies[_make_id(s["kind"], s["number"])]) not in cache["pass1"]
        ]
        print(f"  Pass 1 uncached: {len(uncached_pass1)}/{len(statements)}")
        # Each ~1200 input + ~150 output tokens
        in_tok = len(uncached_pass1) * 1500
        out_tok = len(uncached_pass1) * 200
        cost = (in_tok / 1e6) * 0.27 + (out_tok / 1e6) * 1.10
        print(f"  Pass 1 est cost: ${cost:.4f}")
        print("  Pass 2 cost depends on collision count after Pass 1; usually <$0.01.")
        return

    # --- Pass 1: per-entity ---
    print(f"\n  Pass 1: drafting introduces for {len(statements)} entities ...")
    to_process = statements
    if args.only:
        to_process = [s for s in statements if _make_id(s["kind"], s["number"]) == args.only]
    elif args.limit:
        to_process = statements[:args.limit]

    pass1_results: dict[str, list[str]] = {}
    api_calls = 0
    for idx, stmt in enumerate(to_process):
        sid = _make_id(stmt["kind"], stmt["number"])
        body = bodies[sid]
        if not body:
            pass1_results[sid] = []
            continue

        try:
            terms, was_api = _pass1_draft(stmt, body, api_key, cache)
        except Exception as e:
            print(f"    [{idx+1}/{len(to_process)}] {sid} ERROR: {e}")
            time.sleep(1.0)
            continue

        pass1_results[sid] = terms
        if was_api:
            api_calls += 1
            if api_calls % 10 == 0:
                _save_cache(cache)
                print(f"    [{idx+1}/{len(to_process)}] {sid}: {terms}  (cache flushed)")
            else:
                print(f"    [{idx+1}/{len(to_process)}] {sid}: {terms}")
            time.sleep(0.3)
        # Quiet on cache hit unless --only
        elif args.only:
            print(f"    [cache] {sid}: {terms}")

    _save_cache(cache)
    print(f"  Pass 1 complete: {api_calls} API calls, {len(pass1_results)} entities updated")

    # Apply Pass 1 to statements (replace introduces wholesale for processed entities)
    processed_ids = set(pass1_results.keys())
    for s in statements:
        sid = _make_id(s["kind"], s["number"])
        if sid in processed_ids:
            s["introduces"] = pass1_results[sid]

    # --- Pass 2: collision resolution (iterate until convergence) ---
    pass2_api_calls = 0
    pass2_round = 0
    MAX_PASS2_ROUNDS = 5

    while True:
        pass2_round += 1
        collisions = _detect_collisions(statements)
        if not collisions:
            print(f"\n  Pass 2 round {pass2_round}: no collisions ✓")
            break
        if pass2_round > MAX_PASS2_ROUNDS:
            print(f"\n  Pass 2: hit {MAX_PASS2_ROUNDS}-round cap with collisions still present")
            break

        print(f"\n  Pass 2 round {pass2_round}: {len(collisions)} colliding terms")

        any_change = False
        for term, member_ids in sorted(collisions.items()):
            member_stmts = {sid: next(s for s in statements
                                      if _make_id(s["kind"], s["number"]) == sid)
                            for sid in member_ids}
            member_bodies = {sid: bodies[sid] for sid in member_ids}

            try:
                resolved, was_api = _pass2_resolve(
                    term, member_ids, member_stmts, member_bodies, api_key, cache,
                )
            except Exception as e:
                print(f"    [{term!r}] ERROR: {e}")
                time.sleep(1.0)
                continue

            if was_api:
                pass2_api_calls += 1
                time.sleep(0.3)

            if not resolved:
                print(f"    [{term!r}] no resolution (cache miss without --run-api?)")
                continue

            # Apply: replace ANY case-insensitive occurrence of `term` in each
            # member's introduces with the qualified replacement. If the term
            # is already absent (e.g. earlier round changed it), add the
            # qualified name anyway so the entity still has a concept entry.
            for sid in member_ids:
                qualified = resolved.get(sid, [])
                if not qualified:
                    continue
                stmt = member_stmts[sid]
                old_intros = list(stmt.get("introduces", []) or [])
                new_intros = []
                replaced = False
                for t in old_intros:
                    if t.lower().strip() == term:
                        if not replaced:
                            new_intros.extend(qualified)
                            replaced = True
                    else:
                        new_intros.append(t)
                if not replaced:
                    new_intros.extend(qualified)
                stmt["introduces"] = _dedupe(new_intros)
                if stmt["introduces"] != old_intros:
                    any_change = True
                print(f"    [{term!r}] {sid} → {qualified}")

        _save_cache(cache)

        if not any_change:
            print(f"  Pass 2: no changes this round; halting to avoid loop")
            break

    print(f"  Pass 2 complete: {pass2_api_calls} API calls across {pass2_round} round(s)")

    # --- Final collision check ---
    leftover = _detect_collisions(statements)
    if leftover:
        print(f"\n  WARNING: {len(leftover)} collisions remain after Pass 2:")
        for t, ids in leftover.items():
            print(f"    {t!r}: {ids}")
    else:
        print("\n  All concept names are now globally unique ✓")

    # --- Save ---
    stmts_path.write_text(
        json.dumps(statements, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )

    # --- Final summary ---
    with_intros = sum(1 for s in statements if s.get("introduces"))
    total_concepts = sum(len(s.get("introduces", []) or []) for s in statements)
    print(f"\n  Final: {with_intros}/{len(statements)} statements have introduces")
    print(f"  Total concepts: {total_concepts}")
    print(f"  Saved to {stmts_path}")
    print(f"  Cache: {CACHE_PATH}")


if __name__ == "__main__":
    main()
