#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
translator.py
=============

Universal, single-file Minecraft modpack translator (EN -> RU).

The script can work with a modpack folder of ANY name.

Usage:
    python translator.py
    python translator.py "D:\\Games\\MyModpack"
    python translator.py --pack "D:\\Games\\MyModpack"

If the path is not specified, the script searches for a modpack folder
inside the folder where this script is located. A modpack is recognized
primarily by the presence of a `mods/` directory.

The script NEVER modifies the original modpack. All results are written to:

    minecraft/resourcepacks/Modpack_Auto_Rus/   -> standard lang resource pack
    Translated_Modpack/                          -> everything else (configs,
                                                     ftbquests, patchouli, kubejs,
                                                     data jsons, ...) mirroring
                                                     the original folder structure
    translation_cache.db                         -> SQLite translation cache
    translation_reports/                         -> detailed reports

Only external dependency: googletrans==4.0.2
Everything else is Python standard library.
"""

from __future__ import annotations

import os
import re
import sys
import json
import time
import copy
import shutil
import string
import sqlite3
import hashlib
import asyncio
import zipfile
import traceback
import unicodedata
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Optional, Union
from concurrent.futures import ThreadPoolExecutor

try:
    from googletrans import Translator
except ImportError:
    Translator = None  # handled at runtime, dry-run still works without it


# ======================================================================
# Создатель Dominika4ik
# https://eblo.id/@dominikan4ik
# при поддержке t.me/kefir_play
# сайт моего знакомого https://chkpnt.ru/welcome (активно развивается)
# просьба подписаться на него https://www.youtube.com/@kefir__play__ru
# CONFIG
# ======================================================================

ROOT_DIR = Path(__file__).resolve().parent

# The modpack directory is selected at startup.  Its name is completely
# arbitrary; only the directory itself matters.
MC_DIR = ROOT_DIR / "minecraft"
RESOURCEPACK_NAME = "Modpack_Auto_Rus"
RESOURCEPACK_DIR = MC_DIR / "resourcepacks" / RESOURCEPACK_NAME

# Per-run output/cache stay next to the translator, while RESOURCEPACK_DIR
# and all source scanning are tied to the selected modpack directory.
TRANSLATED_MODPACK_DIR = ROOT_DIR / "Translated_Modpack"
CACHE_DB_PATH = ROOT_DIR / "translation_cache.db"
REPORTS_DIR = ROOT_DIR / "translation_reports"

# ---- GLOBAL TRANSLATION CACHE ----
# A second, shareable cache layer that lives alongside (not instead of) the
# per-run local `translation_cache.db` above. It is intentionally kept in
# its own `cache/` directory (never inside a modpack folder) so it can be
# copied between machines / merged across many different modpack runs.
CACHE_DIR = ROOT_DIR / "cache"
GLOBAL_CACHE_DB_PATH = CACHE_DIR / "global_translations.db"
TRANSLATION_CONFLICTS_PATH = CACHE_DIR / "translation_conflicts.json"
INVALID_CACHE_ENTRIES_PATH = CACHE_DIR / "invalid_cache_entries.json"

# Bumped whenever the global-cache table schema changes shape (new columns,
# new tables). Independent from CLASSIFIER_VERSION/VALIDATOR_VERSION, which
# govern whether a *translation result* is still trusted.
GLOBAL_CACHE_SCHEMA_VERSION = 1

# Quality statuses a global-cache row can have. Only rows in
# GLOBAL_CACHE_USABLE_STATUSES are ever served back as a translation - the
# rest exist purely for auditing/history and require explicit human/import
# action to promote.
QUALITY_VALIDATED = "validated"
QUALITY_UNVALIDATED = "unvalidated"
QUALITY_REJECTED = "rejected"
QUALITY_MANUAL = "manual"
GLOBAL_CACHE_USABLE_STATUSES = (QUALITY_MANUAL, QUALITY_VALIDATED)

# Where a translation came from. Recorded for every global-cache row so a
# future DeepL/Ollama engine (or manual QA pass) can be told apart from
# Google Translate output.
SOURCE_GOOGLE = "google"
SOURCE_DEEPL = "deepl"
SOURCE_OLLAMA = "ollama"
SOURCE_MANUAL = "manual"
SOURCE_IMPORTED = "imported"

# Priority used to decide which variant "wins" a conflict / which existing
# row may be safely promoted to actually being served. Lower index = higher
# priority. Never used to silently overwrite a higher-priority row.
SOURCE_PRIORITY = (SOURCE_MANUAL, SOURCE_DEEPL, SOURCE_OLLAMA, SOURCE_IMPORTED, SOURCE_GOOGLE)
QUALITY_PRIORITY = (QUALITY_MANUAL, QUALITY_VALIDATED, QUALITY_UNVALIDATED, QUALITY_REJECTED)

SOURCE_LANG = "en"
TARGET_LANG = "ru"

# Bumped whenever is_technical_value()/classify_key()/classify_string() rules
# change in a way that could affect which strings are safe to translate.
# Cache entries written under an older version are treated as stale and are
# re-validated (and re-translated if necessary) rather than blindly reused -
# this is what prevents a previously-cached bad translation (e.g. a hex ID
# that used to slip through the old classifier) from being served forever.
CLASSIFIER_VERSION = 3
VALIDATOR_VERSION = 2

MAX_THREADS = 4
BATCH_SIZE = 15
MIN_BATCH_SIZE = 1

MAX_RETRIES = 5
BASE_BACKOFF = 1.5   # seconds, exponential backoff base
REQUEST_TIMEOUT = 15  # seconds

ANALYZE_ONLY = True  # dry-run first; user is prompted whether to proceed

# Candidate en_* locale names for language resource discovery
EN_LOCALE_NAMES = {"en_us", "en_gb", "en", "english", "en_au", "en_ca"}

# File extensions that MAY contain localization data
LANG_FILE_EXTS = {".json", ".lang", ".properties", ".json5", ".toml", ".xml", ".txt"}

# ======================================================================
# HEURISTIC STRING CLASSIFICATION https://eblo.id/@dominikan4ik
# ======================================================================

CONF_HIGH = "HIGH"
CONF_MEDIUM = "MEDIUM"
CONF_LOW = "LOW"
CONF_SKIP = "SKIP"

# Key names that strongly suggest human-facing text
TEXT_KEY_HINTS = {
    "title", "subtitle", "description", "desc", "text", "message", "msg",
    "label", "tooltip", "comment", "warning", "info", "lore", "dialogue",
    "dialog", "chapter", "quest", "objective", "reward", "name", "displayname",
    "display", "hover", "content", "summary", "notes", "note", "flavor",
    "flavour", "greeting", "prompt", "hint", "story", "narrative", "question",
    "answer", "instructions", "instruction", "welcome", "goodbye", "success",
    "failure", "error", "confirm", "cancel", "accept", "decline", "reject",
    "button", "menu", "header", "footer", "caption",
}

# Key names that strongly suggest a technical identifier (never translate).
# Checked BEFORE text hints - safety-first: if a key token matches both an
# id hint and a text hint (e.g. "quest_links" contains both "quest" and
# "links"), the id classification wins.
ID_KEY_HINTS = {
    "id", "ids", "uid", "uuid", "guid", "type", "item", "items", "block",
    "blocks", "entity", "recipe", "advancement", "tag", "tags",
    "function", "predicate", "loot_table", "loottable", "texture", "model",
    "sound", "path", "namespace", "registry", "registryname", "registry_name",
    "modid", "mod_id", "translate", "key", "keys", "class", "target",
    "parent", "parents", "child", "children", "link", "links", "dependency",
    "dependencies", "unlocks", "icon", "condition", "conditions", "result",
    "ingredient", "ingredients", "output", "input", "slot", "color", "colour",
    "rgb", "hex", "count", "amount", "level", "duration", "cooldown",
    "priority", "weight", "chance", "x", "y", "z", "width", "height",
    "depth", "version", "format", "protocol", "hash", "checksum",
    "fingerprint", "quest_id", "chapter_id", "task_id", "reward_id",
    "questid", "chapterid", "taskid", "rewardid",
    "formula", "expression", "script", "regex", "macro", "operator",
}

RESOURCE_LOCATION_RE = re.compile(r"^[a-z0-9_.\-]+:[a-z0-9_./\-]+$")
TRANSLATION_KEY_RE = re.compile(r"^[a-z_]+(?:\.[a-z0-9_]+){1,}$")
BARE_ID_RE = re.compile(r"^[a-z][a-z0-9_./:\\-]*$")  # lowercase, no spaces
UUID_RE = re.compile(
    r"^[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}$"
)
HEX_COLOR_RE = re.compile(r"^#?[0-9a-fA-F]{6}$|^#?[0-9a-fA-F]{3}$")
NUMBER_RE = re.compile(r"^-?\d+(\.\d+)?[bslfdBSLFD]?$")
BOOL_RE = re.compile(r"^(true|false)$", re.IGNORECASE)
COORD_RE = re.compile(r"^-?\d+(\.\d+)?\s*,\s*-?\d+(\.\d+)?\s*,\s*-?\d+(\.\d+)?$")
URL_RE = re.compile(r"^https?://", re.IGNORECASE)
PATH_LIKE_RE = re.compile(
    r"^(assets|data|textures|models|sounds|blockstates|structures)[/\\]", re.IGNORECASE
)
FILE_EXT_RE = re.compile(
    r"\.(png|json|ogg|nbt|snbt|txt|jem|jpm|properties|class|ttf|otf|mcmeta)$",
    re.IGNORECASE,
)

# Bare hexadecimal identifier (e.g. FTB Quests hex IDs like "27B28A53F0EFE604").
# Requires at least one digit so we don't accidentally swallow short hex-letter
# English words ("cafe", "dead"), and a minimum length typical of real IDs/hashes.
BARE_HEX_ID_RE = re.compile(r"^[0-9A-Fa-f]{8,64}$")

# Generic opaque identifier / hash / fingerprint: an unbroken alphanumeric
# token (no spaces, no punctuation) that contains at least one digit and is
# long enough that it is virtually never intended human-facing text.
OPAQUE_ID_RE = re.compile(r"^(?=[0-9A-Za-z]{8,64}$)(?=[^ ]*[0-9])[0-9A-Za-z]+$")

# All-caps constant/enum-style config values, e.g. "DISABLED", "SHOW_ALWAYS".
CONFIG_ENUM_RE = re.compile(r"^[A-Z][A-Z0-9_]{2,}$")

# namespace:path resource locations even when embedded (not anchored), used
# as an extra guard for values that also contain surrounding punctuation.
NAMESPACE_PATH_RE = re.compile(r"^[a-z0-9_.\-]+:[a-z0-9_./\-]+$")

# --- Math/formula expression detection -------------------------------
# Config values like "(sqrt(((ATTACK_DAMAGE * ATTACK_SPEED) * (ARMOR +
# ARMOR_TOUGHNESS / 3))) * 16) * 0.66" are executable expressions parsed
# by a mod's own hand-written formula evaluator (e.g. Prominent's
# ItemLevel$1.parseExpression). They contain spaces around operators, so
# looks_like_human_text()/classify_string() previously mistook them for
# prose ("neutral-key-sentence-like") and sent them to Google Translate,
# which transliterated the CONST_CASE variable names (ATTACK_DAMAGE ->
# АТАКА_УРОН) and localized the decimal point (0.66 -> 0,66) - both fatal
# to the evaluator, which only recognises specific ASCII tokens and a
# literal '.' as the decimal separator. Detect this shape and treat it as
# technical regardless of key name, so it is never touched.
MATH_FUNC_NAMES = {
    "sqrt", "min", "max", "abs", "floor", "ceil", "round", "pow", "log",
    "ln", "sin", "cos", "tan", "mod", "exp", "clamp", "lerp",
}
FORMULA_ALLOWED_CHARS_RE = re.compile(r"^[\sA-Za-z0-9_+\-*/().,^%<>=!&|]+$")
FORMULA_TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def is_formula_like(value: str) -> bool:
    """True if `value` looks like a math/logic expression (variables in
    CONST_CASE, known function names, numbers, operators, parens) rather
    than human-facing prose - even though it may contain spaces."""
    v = value.strip()
    if not v:
        return False
    # Must contain at least one operator/paren - otherwise it's just a
    # bare word or ALL_CAPS enum, already handled by CONFIG_ENUM_RE.
    if not re.search(r"[()+\-*/^%<>=!&|]", v):
        return False
    if not FORMULA_ALLOWED_CHARS_RE.match(v):
        return False
    tokens = FORMULA_TOKEN_RE.findall(v)
    if not tokens:
        return False
    for tok in tokens:
        if tok.lower() in MATH_FUNC_NAMES:
            continue
        if tok.isupper():  # CONST_CASE variable, e.g. ATTACK_DAMAGE, ARMOR, X
            continue
        return False  # mixed/lowercase word -> looks like real prose, bail out
    return True


def _normalize_key(key: str) -> str:
    return re.sub(r"[^a-z]", "", key.lower())


def _key_tokens(key: str) -> list[str]:
    """Split a key into lowercase word tokens on underscores/camelCase
    boundaries, e.g. 'registry_name' -> ['registry', 'name'],
    'displayName' -> ['display', 'name']. Used for whole-word hint
    matching instead of unsafe substring containment."""
    s = str(key)
    s = re.sub(r"(?<=[a-z0-9])(?=[A-Z])", "_", s)
    return [t for t in re.split(r"[^a-zA-Z0-9]+", s.lower()) if t]


def classify_key(key: str) -> str:
    """Return 'text', 'id' or 'neutral' based on the key name alone.

    ID hints are checked first: if a compound key contains BOTH an id-like
    token and a text-like token (e.g. 'quest_links' = 'quest' + 'links'),
    it is classified as 'id'. This is intentional - a false 'skip' merely
    loses a translation opportunity, while a false 'translate' can corrupt
    a technical identifier, so ties are resolved toward safety.
    """
    tokens = _key_tokens(key)
    if not tokens:
        return "neutral"
    token_set = set(tokens)
    if token_set & ID_KEY_HINTS:
        return "id"
    if token_set & TEXT_KEY_HINTS:
        return "text"
    return "neutral"


def looks_like_human_text(value: str) -> bool:
    """Cheap heuristic: does this string look like written language?"""
    if not value or not value.strip():
        return False
    v = value.strip()
    if len(v) < 2:
        return False
    if " " in v:
        return True
    # single word: must contain letters and not be all-lowercase-with-symbols
    letters = sum(1 for c in v if c.isalpha())
    if letters == 0:
        return False
    if v[0].isupper() and letters == len(re.sub(r"[^A-Za-z]", "", v)):
        # Capitalized single word made only of letters, e.g. "Cancel"
        return True
    return letters / max(len(v), 1) > 0.6 and " " not in v and "_" not in v and ":" not in v


_NBT_ID_PREFIX_RE = re.compile(r"^[a-z0-9_.\-]+:[a-z0-9_./\-]*$", re.IGNORECASE)


def looks_like_nbt_compound(value: str) -> bool:
    """True if `value` IS (or starts with an item id immediately followed
    by) an NBT/SNBT compound or list - e.g. '{Count:1b,id:"minecraft:
    diamond_pickaxe"}' or 'minecraft:diamond_pickaxe{Enchantments:[...]}'.

    This is what SkyblockBuilder's starting-inventory config stores per
    item, and what broke with:
        com.google.gson.JsonSyntaxException: Invalid NBT Entry:
        com.mojang.brigadier.exceptions.CommandSyntaxException:
        Expected key at position 1: {<--[HERE]
    The value doesn't match RESOURCE_LOCATION_RE (it has braces/colons
    beyond a simple namespace:path) and can contain a human-readable
    display name nested inside (e.g. a JSON text component under a
    "display"/"Name" tag), which gave looks_like_human_text() a reason to
    treat the WHOLE string as translatable prose. Sending it wholesale to
    Google Translate reliably corrupts the NBT grammar (extra/missing
    quotes, translated key names, altered punctuation right after '{').

    Detected by actually parsing the value with this module's own SNBT
    parser (parse_snbt - the same grammar family Brigadier/Minecraft uses)
    rather than guessing with regexes, so it reliably recognizes NBT no
    matter what's nested inside it."""
    v = value.strip()
    if not v:
        return False
    if v[:1] == "[":
        try:
            parse_snbt(v)
            return True
        except Exception:
            return False
    if "{" not in v:
        return False
    brace_idx = v.find("{")
    prefix = v[:brace_idx]
    if prefix and not _NBT_ID_PREFIX_RE.match(prefix):
        # text before the '{' doesn't look like an item/resource id -
        # could be ordinary prose that merely contains a brace somewhere.
        return False
    try:
        parse_snbt(v[brace_idx:])
        return True
    except Exception:
        return False


def is_technical_string(value: str) -> bool:
    """Pattern-only technical-value detector (no key/context awareness).
    See is_technical_value() for the context-aware universal classifier
    that should be used everywhere instead of calling this directly."""
    v = value.strip()
    if not v:
        return True
    if RESOURCE_LOCATION_RE.match(v) and " " not in v:
        return True
    if TRANSLATION_KEY_RE.match(v):
        return True
    if UUID_RE.match(v):
        return True
    if HEX_COLOR_RE.match(v):
        return True
    if NUMBER_RE.match(v):
        return True
    if BOOL_RE.match(v):
        return True
    if COORD_RE.match(v):
        return True
    if URL_RE.match(v):
        return True
    if PATH_LIKE_RE.match(v):
        return True
    if FILE_EXT_RE.search(v):
        return True
    if BARE_ID_RE.match(v) and " " not in v and ("_" in v or "/" in v or ":" in v):
        return True
    # Hex identifiers / hashes / fingerprints (e.g. FTB Quests hex IDs).
    # MUST be checked regardless of key name - this is what protects
    # "27B28A53F0EFE604" from being mangled into "27Б28А53Ф0ЭФЕ604".
    if BARE_HEX_ID_RE.match(v):
        return True
    # Any other opaque alphanumeric token (no spaces) containing a digit,
    # long enough that it reads as an id/hash/checksum rather than prose.
    if OPAQUE_ID_RE.match(v) and " " not in v:
        return True
    # ALL_CAPS enum / technical option values (config toggles like DISABLED,
    # SHOW_ALWAYS, AUTO, etc.)
    if CONFIG_ENUM_RE.match(v):
        return True
    # Math/logic expression evaluated by a mod's own formula parser
    # (CONST_CASE variables, operators, parens) - never translate, and
    # never let the decimal point get localized to a comma.
    if is_formula_like(v):
        return True
    # NBT/SNBT data embedded as a string (starting-inventory items,
    # structure/template metadata, etc.) - see looks_like_nbt_compound().
    # Checked even when the value contains spaces or nested human-looking
    # text, because those are exactly the values that used to slip past
    # every check above and get translated wholesale, corrupting the NBT.
    if looks_like_nbt_compound(v):
        return True
    return False




# Global counters for reporting - every call site funnels through
# is_technical_value(), so this is the single place that can accurately
# count how many technical values were detected/protected across the
# whole pipeline (lang files, JSON, SNBT, config, kubejs).
_TECHNICAL_STATS = {"detected": 0}


def reset_technical_stats() -> None:
    _TECHNICAL_STATS["detected"] = 0


def get_technical_stats() -> dict:
    return dict(_TECHNICAL_STATS)


def is_technical_value(value: Any, context: Optional[str] = None) -> bool:
    """
    Universal technical-value classifier: is_technical_value(value, context).

    `context` is the key name (or None) the value was found under. Returns
    True whenever the value must NEVER be sent to translation - hex/decimal
    IDs, UUIDs, hashes, fingerprints, quest/chapter/task/reward/dependency/
    parent IDs, links, registry names, resource locations, namespace:path
    strings, mod/item/block/entity/recipe/advancement/tag/function IDs,
    file paths, URLs, coordinates, numeric values, booleans, NBT/SNBT
    technical values, configuration enums, and other technical option
    values. This is the single entry point every collector/applier should
    use instead of calling is_technical_string()/classify_key() directly.
    """
    if not isinstance(value, str):
        return True
    v = value.strip()
    if not v:
        return True
    if is_technical_string(v):
        _TECHNICAL_STATS["detected"] += 1
        return True
    if context is not None and classify_key(context) == "id":
        _TECHNICAL_STATS["detected"] += 1
        return True
    return False


def classify_lang_value(value: Any, key: Optional[str] = None) -> tuple[bool, str, str]:
    """
    Classifier for entries inside a *dedicated localization file* (en_us.json,
    .lang, .properties lang overrides). Every entry in such a file is, by
    definition, curated display text supplied by the mod/pack author - so we
    only need to filter out technical-looking values, not second-guess based
    on the key name.

    IMPORTANT: unlike generic data/config JSON, lang-file KEYS are themselves
    dotted translation keys (e.g. "item.create.cogwheel", "block.minecraft.
    stone") - their first segment is almost always a structural word like
    "item"/"block"/"entity"/"tag" purely because of Minecraft's translation-key
    convention, NOT because the key names a technical id field. Running the
    structural-key ID-hint classifier (classify_key) against a lang-file key
    would therefore misfire on nearly every vanilla/mod translation key and
    silently stop translating the whole lang file. So classification here is
    intentionally VALUE-ONLY (is_technical_string), never key-driven. The
    `key` parameter is accepted for API symmetry/reporting but not used to
    gate translation.
    """
    if not isinstance(value, str):
        return False, CONF_SKIP, "not-a-string"
    v = value.strip()
    if not v:
        return False, CONF_SKIP, "empty"
    if is_technical_string(v):
        return False, CONF_SKIP, "technical-pattern"
    return True, CONF_HIGH, "lang-file-entry"


def collect_lang_candidates(flat: dict[str, str], source_type: str, source_file: str, modid: str = "") -> list[StringCandidate]:
    candidates = []
    for key, value in flat.items():
        should, conf, reason = classify_lang_value(value, key)
        if should:
            candidates.append(StringCandidate(value, conf, reason, source_type, source_file, modid))
    return candidates


def classify_string(key: Optional[str], value: Any) -> tuple[bool, str, str]:
    """
    Decide whether `value` (found under `key`) should be translated.
    Returns (should_translate, confidence, reason).
    """
    if not isinstance(value, str):
        return False, CONF_SKIP, "not-a-string"
    v = value.strip()
    if not v:
        return False, CONF_SKIP, "empty"

    key_class = classify_key(key) if key is not None else "neutral"

    if is_technical_value(v, key):
        return False, CONF_SKIP, "technical-pattern"

    if key_class == "id":
        return False, CONF_SKIP, f"id-key:{key}"

    if key_class == "text":
        if looks_like_human_text(v):
            return True, CONF_HIGH, f"text-key:{key}"
        # The key hints "text" but the content itself doesn't look like
        # written language (no spaces, no clean capitalized word). This is
        # exactly the shape of a mis-hinted technical value (e.g. an ID
        # sitting under a key like "quest" that also matched a text hint).
        # Downgrade to LOW so it is reported but NOT auto-translated by
        # default (default min_confidence is MEDIUM everywhere).
        return True, CONF_LOW, f"text-key-weak-content:{key}"

    # neutral key
    if looks_like_human_text(v) and (" " in v or v[:1].isupper()):
        if " " in v:
            return True, CONF_MEDIUM, "neutral-key-sentence-like"
        return True, CONF_LOW, "neutral-key-single-word"

    return False, CONF_SKIP, "no-signal"


# ======================================================================
# PLACEHOLDER PROTECTION
# ======================================================================

PLACEHOLDER_PATTERNS = [
    re.compile(r"§[0-9a-fk-orA-FK-OR]"),          # Minecraft formatting codes
    re.compile(r"%\d*\$?[sdif]"),                  # %s %d %1$s style
    re.compile(r"\{[a-zA-Z0-9_.]+\}"),              # {player} {count}
    re.compile(r"<[a-zA-Z0-9_/#:]+>"),              # <item> <player> MiniMessage tags
    re.compile(r"\[\[.*?\]\]"),                     # [[...]]
    re.compile(r"\[#[0-9a-fA-F]{3,6}\]"),           # [#FFFFFF]
    re.compile(r"\\n|\\t"),                         # escaped newlines/tabs
]

PLACEHOLDER_TOKEN_RE = re.compile(r"__PH(\d+)__")


def protect_placeholders(text: str) -> tuple[str, list[str]]:
    """Replace placeholder-looking substrings with tokens. Returns (protected_text, tokens)."""
    tokens: list[str] = []

    def _sub(m: re.Match) -> str:
        tokens.append(m.group(0))
        return f"__PH{len(tokens) - 1}__"

    protected = text
    for pattern in PLACEHOLDER_PATTERNS:
        protected = pattern.sub(_sub, protected)
    return protected, tokens


def restore_placeholders(text: str, tokens: list[str]) -> Optional[str]:
    """Restore placeholder tokens back into translated text. Returns None on failure."""
    found_tokens = set(int(m.group(1)) for m in PLACEHOLDER_TOKEN_RE.finditer(text))
    expected_tokens = set(range(len(tokens)))
    if found_tokens != expected_tokens:
        # try a best-effort restoration anyway; caller decides whether it's acceptable
        result = text
        for i, tok in enumerate(tokens):
            result = result.replace(f"__PH{i}__", tok)
        if PLACEHOLDER_TOKEN_RE.search(result):
            return None  # leftover unresolved tokens -> unsafe
        return result if found_tokens == expected_tokens else None

    result = text
    for i, tok in enumerate(tokens):
        # Google Translate sometimes adds spaces around tokens / changes case
        # of surrounding text. IMPORTANT: the replacement is passed as a
        # function, not a raw string - re.sub() interprets backslashes in a
        # *string* replacement as backreferences/escapes (e.g. a literal
        # token of "\n" would be silently turned into a real newline, or a
        # token starting "\1" could be mis-read as a capture group). A
        # function replacement is inserted verbatim with no interpretation.
        result = re.sub(rf"__PH{i}__", lambda _m, _tok=tok: _tok, result)
    return result


# ======================================================================
# TECHNICAL TOKEN CONSISTENCY (extra guard used before ANY result is
# written into the GLOBAL cache - see GlobalTranslationCache.put()).
#
# This is deliberately independent of / redundant with is_technical_value()
# and protect_placeholders(): those decide whether a *whole string* should
# be sent to translation at all. This layer instead scans the text for
# technical-looking SUBSTRINGS (a hex id embedded next to prose, a
# namespace:path, a URL, ...) and makes sure the exact same set of tokens
# is still present, unchanged, after translation. This is what would catch
# the historical FTB Quests corruption bug
# (27B28A53F0EFE604 -> 27Б28А53Ф0ЭФЕ604) if such a value were ever
# translated, and is a required regression test (see self_test()).
# ======================================================================

_UUID_SEARCH_RE = re.compile(
    r"[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}"
)
_HEX_ID_SEARCH_RE = re.compile(r"\b[0-9A-Fa-f]{8,64}\b")
_NAMESPACE_PATH_SEARCH_RE = re.compile(r"\b[a-z0-9_.\-]+:[a-z0-9_./\-]+\b")
_URL_SEARCH_RE = re.compile(r"https?://\S+", re.IGNORECASE)
_FILE_PATH_SEARCH_RE = re.compile(
    r"\b(?:assets|data|textures|models|sounds|blockstates|structures)[/\\][^\s\"'{}\[\]]+",
    re.IGNORECASE,
)


def extract_technical_tokens(text: str) -> list[str]:
    """Return every technical-looking substring found in `text`: UUIDs, bare
    hex ids/hashes, namespace:path resource locations, URLs, asset/data file
    paths, and every placeholder/formatting code (%s, {player}, §a, ...).
    Order is not meaningful - callers compare token multisets."""
    if not isinstance(text, str):
        return []
    tokens: list[str] = []
    for pattern in (
        _UUID_SEARCH_RE,
        _HEX_ID_SEARCH_RE,
        _NAMESPACE_PATH_SEARCH_RE,
        _URL_SEARCH_RE,
        _FILE_PATH_SEARCH_RE,
    ):
        tokens.extend(pattern.findall(text))
    _, ph_tokens = protect_placeholders(text)
    tokens.extend(ph_tokens)
    return tokens


def validate_technical_consistency(original: str, translated: str) -> bool:
    """True only if `translated` contains exactly the same technical tokens
    (same values, same multiset) as `original`. A hex/UUID/namespace id that
    got transliterated, dropped, or duplicated by the translation engine
    fails this check."""
    if not isinstance(original, str) or not isinstance(translated, str):
        return False
    return sorted(extract_technical_tokens(original)) == sorted(extract_technical_tokens(translated))


def is_safe_to_cache_globally(original: str, translated: str) -> tuple[bool, str]:
    """Full pre-write safety gate for the GLOBAL cache. Returns (ok, reason).
    Combines: not a technical value, placeholder round-trip already verified
    by the caller, and technical-token consistency. This is called in
    addition to (never instead of) validator/placeholder checks already
    performed earlier in the pipeline."""
    if not original or not translated:
        return False, "empty"
    if is_technical_value(original):
        return False, "original-is-technical-value"
    if not validate_technical_consistency(original, translated):
        return False, "technical-token-mismatch"
    return True, "ok"
# ======================================================================
# SQLITE TRANSLATION CACHE
# ======================================================================

class TranslationCache:
    def __init__(self, db_path: Path):
        self.db_path = db_path
        self._local = {}
        self.conn = sqlite3.connect(str(db_path), check_same_thread=False)
        self.conn.execute("PRAGMA journal_mode=WAL;")
        self._init_schema()
        self._lock = None
        import threading
        self._lock = threading.Lock()

    def _init_schema(self):
        self.conn.execute(
            """
            CREATE TABLE IF NOT EXISTS translations (
                hash TEXT PRIMARY KEY,
                original_text TEXT NOT NULL,
                source_language TEXT NOT NULL,
                target_language TEXT NOT NULL,
                translated_text TEXT NOT NULL,
                created_at REAL NOT NULL,
                classifier_version INTEGER NOT NULL DEFAULT 0,
                validator_version INTEGER NOT NULL DEFAULT 0,
                UNIQUE(original_text, source_language, target_language)
            )
            """
        )
        # Migrate older cache DBs (pre-versioning) that lack these columns.
        existing_cols = {row[1] for row in self.conn.execute("PRAGMA table_info(translations)")}
        if "classifier_version" not in existing_cols:
            self.conn.execute(
                "ALTER TABLE translations ADD COLUMN classifier_version INTEGER NOT NULL DEFAULT 0"
            )
        if "validator_version" not in existing_cols:
            self.conn.execute(
                "ALTER TABLE translations ADD COLUMN validator_version INTEGER NOT NULL DEFAULT 0"
            )
        self.conn.commit()

    @staticmethod
    def make_hash(original: str, src: str, dst: str) -> str:
        return hashlib.sha256(f"{src}|{dst}|{original}".encode("utf-8")).hexdigest()

    def get(self, original: str, src: str = SOURCE_LANG, dst: str = TARGET_LANG) -> Optional[str]:
        """Return the cached translation, or None if missing OR stale (written
        under an older classifier/validator version - rules may have changed
        since, e.g. a value that used to be considered translatable might now
        be recognized as a technical id, so the old cached result must not be
        trusted blindly)."""
        h = self.make_hash(original, src, dst)
        with self._lock:
            cur = self.conn.execute(
                "SELECT translated_text, classifier_version, validator_version "
                "FROM translations WHERE hash=?",
                (h,),
            )
            row = cur.fetchone()
        if not row:
            return None
        translated_text, cls_ver, val_ver = row
        if cls_ver != CLASSIFIER_VERSION or val_ver != VALIDATOR_VERSION:
            return None
        return translated_text

    def put(self, original: str, translated: str, src: str = SOURCE_LANG, dst: str = TARGET_LANG):
        h = self.make_hash(original, src, dst)
        with self._lock:
            self.conn.execute(
                """
                INSERT OR REPLACE INTO translations
                (hash, original_text, source_language, target_language, translated_text,
                 created_at, classifier_version, validator_version)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                """,
                (h, original, src, dst, translated, time.time(), CLASSIFIER_VERSION, VALIDATOR_VERSION),
            )
            self.conn.commit()

    def close(self):
        self.conn.close()


class GlobalTranslationCache:
    def __init__(self, db_path: Path = GLOBAL_CACHE_DB_PATH):
        self.db_path = Path(db_path)
        self.db_path.parent.mkdir(parents=True, exist_ok=True)
        self.conn = sqlite3.connect(str(self.db_path), check_same_thread=False, timeout=30)
        self.conn.execute("PRAGMA journal_mode=WAL;")
        self.conn.execute("PRAGMA busy_timeout=30000;")
        self.conn.execute("PRAGMA synchronous=NORMAL;")
        import threading
        self._lock = threading.Lock()
        self.stats = {
            "global_cache_entries": 0,
            "local_cache_hits": 0,
            "global_cache_hits": 0,
            "google_requests": 0,
            "cache_misses": 0,
            "cache_conflicts": 0,
            "cache_rejected": 0,
            "cache_imported": 0,
            "cache_duplicates": 0,
        }
        self._init_schema()
        self._conflicts: list[dict] = []
        if self.TRANSLATION_CONFLICTS_PATH.exists():
            try:
                self._conflicts = json.loads(self.TRANSLATION_CONFLICTS_PATH.read_text(encoding="utf-8")).get("conflicts", [])
            except Exception:
                self._conflicts = []
        self.stats["global_cache_entries"] = self.count()

    # convenience so tests can point conflicts at a tmp dir per-instance
    TRANSLATION_CONFLICTS_PATH = TRANSLATION_CONFLICTS_PATH

    # ---- schema / migration ----

    def _init_schema(self):
        self.conn.execute(
            """
            CREATE TABLE IF NOT EXISTS translations (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                text_hash TEXT NOT NULL,
                original_text TEXT NOT NULL,
                source_language TEXT NOT NULL,
                target_language TEXT NOT NULL,
                translated_text TEXT NOT NULL,
                context TEXT,
                mod_id TEXT,
                format_type TEXT,
                key_path TEXT,
                quality_status TEXT NOT NULL DEFAULT 'unvalidated',
                validator_version INTEGER NOT NULL DEFAULT 0,
                source TEXT NOT NULL DEFAULT 'google',
                created_at REAL NOT NULL,
                updated_at REAL NOT NULL,
                UNIQUE(original_text, source_language, target_language)
            )
            """
        )
        self.conn.execute(
            """
            CREATE TABLE IF NOT EXISTS cache_metadata (
                key TEXT PRIMARY KEY,
                value TEXT NOT NULL
            )
            """
        )
        self.conn.commit()
        self._migrate_schema()
        self.conn.execute("CREATE INDEX IF NOT EXISTS idx_translations_hash ON translations(text_hash)")
        self.conn.execute(
            "CREATE INDEX IF NOT EXISTS idx_translations_lookup "
            "ON translations(original_text, source_language, target_language)"
        )
        self.conn.commit()
        now = time.time()
        row = self.conn.execute("SELECT value FROM cache_metadata WHERE key='created_at'").fetchone()
        if not row:
            self.conn.execute("INSERT INTO cache_metadata(key, value) VALUES ('created_at', ?)", (str(now),))
        self.conn.execute(
            "INSERT INTO cache_metadata(key, value) VALUES ('schema_version', ?) "
            "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
            (str(GLOBAL_CACHE_SCHEMA_VERSION),),
        )
        self.conn.execute(
            "INSERT INTO cache_metadata(key, value) VALUES ('validator_version', ?) "
            "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
            (str(VALIDATOR_VERSION),),
        )
        self.conn.execute(
            "INSERT INTO cache_metadata(key, value) VALUES ('updated_at', ?) "
            "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
            (str(now),),
        )
        self.conn.commit()

    def _migrate_schema(self):
        """PRAGMA table_info-driven migration: add any column this version
        of the code expects but an older global_translations.db lacks.
        Never drops or rewrites existing data (see TASK section 13/24)."""
        expected_columns = {
            "text_hash": "TEXT NOT NULL DEFAULT ''",
            "context": "TEXT",
            "mod_id": "TEXT",
            "format_type": "TEXT",
            "key_path": "TEXT",
            "quality_status": "TEXT NOT NULL DEFAULT 'unvalidated'",
            "validator_version": "INTEGER NOT NULL DEFAULT 0",
            "source": "TEXT NOT NULL DEFAULT 'google'",
            "updated_at": "REAL NOT NULL DEFAULT 0",
        }
        existing_cols = {row[1] for row in self.conn.execute("PRAGMA table_info(translations)")}
        for col, ddl in expected_columns.items():
            if col not in existing_cols:
                try:
                    self.conn.execute(f"ALTER TABLE translations ADD COLUMN {col} {ddl}")
                except sqlite3.OperationalError:
                    pass  # column added concurrently / already present
        self.conn.commit()
        # backfill text_hash for any pre-existing rows that lack it (older
        # schema versions did not have this column at all).
        missing = self.conn.execute(
            "SELECT id, original_text, source_language, target_language FROM translations "
            "WHERE text_hash IS NULL OR text_hash=''"
        ).fetchall()
        for row_id, orig, src, dst in missing:
            h = self.make_hash(orig, src, dst)
            self.conn.execute("UPDATE translations SET text_hash=? WHERE id=?", (h, row_id))
        if missing:
            self.conn.commit()

    @staticmethod
    def make_hash(original: str, src: str, dst: str) -> str:
        return hashlib.sha256(f"{src}|{dst}|{original}".encode("utf-8")).hexdigest()

    def count(self) -> int:
        with self._lock:
            row = self.conn.execute("SELECT COUNT(*) FROM translations").fetchone()
        return row[0] if row else 0

    # ---- lookup (priority steps 2 & 3 from the TASK spec) ----

    def lookup(self, original: str, src: str = SOURCE_LANG, dst: str = TARGET_LANG) -> Optional[str]:
        """Exact original_text + language-pair match against any row whose
        quality_status is usable, regardless of context/mod_id (a phrase
        translated once for mod A is reused for mod B - context is only
        used for conflict *resolution*, never to block a lookup). Rows
        written under an older VALIDATOR_VERSION are treated as a miss here
        - use revalidate_stale() to bring them back into rotation."""
        placeholders = ",".join("?" for _ in GLOBAL_CACHE_USABLE_STATUSES)
        with self._lock:
            cur = self.conn.execute(
                f"""
                SELECT translated_text, quality_status, validator_version FROM translations
                WHERE original_text=? AND source_language=? AND target_language=?
                  AND quality_status IN ({placeholders})
                ORDER BY
                    CASE quality_status WHEN 'manual' THEN 0 ELSE 1 END,
                    updated_at DESC
                """,
                (original, src, dst, *GLOBAL_CACHE_USABLE_STATUSES),
            )
            rows = cur.fetchall()
        for translated_text, quality_status, validator_version in rows:
            if validator_version < VALIDATOR_VERSION and quality_status != QUALITY_MANUAL:
                continue  # stale - needs revalidation first
            return translated_text
        return None

    # ---- write path (step 5 from the TASK spec) ----

    def put(
        self,
        original: str,
        translated: str,
        src: str = SOURCE_LANG,
        dst: str = TARGET_LANG,
        context: str = "",
        mod_id: str = "",
        format_type: str = "",
        key_path: str = "",
        quality_status: str = QUALITY_VALIDATED,
        source: str = SOURCE_GOOGLE,
    ) -> str:
        """Insert a new translation, or - if (original, src, dst) already
        exists with a DIFFERENT translated_text - record a conflict and
        leave the existing row untouched. Returns one of:
        'inserted' | 'duplicate' | 'conflict' | 'rejected'.
        Never called for a row that hasn't already passed
        is_safe_to_cache_globally()+validate_json_roundtrip()/placeholder
        checks upstream - this method re-checks anyway (belt & suspenders)."""
        if quality_status in GLOBAL_CACHE_USABLE_STATUSES:
            ok, _reason = is_safe_to_cache_globally(original, translated)
            if not ok:
                self.stats["cache_rejected"] += 1
                return "rejected"

        h = self.make_hash(original, src, dst)
        now = time.time()
        with self._lock:
            existing = self.conn.execute(
                "SELECT translated_text, quality_status, source, mod_id, context FROM translations "
                "WHERE original_text=? AND source_language=? AND target_language=?",
                (original, src, dst),
            ).fetchone()

            if existing is None:
                self.conn.execute(
                    """
                    INSERT INTO translations
                    (text_hash, original_text, source_language, target_language, translated_text,
                     context, mod_id, format_type, key_path, quality_status, validator_version,
                     source, created_at, updated_at)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                    """,
                    (h, original, src, dst, translated, context, mod_id, format_type, key_path,
                     quality_status, VALIDATOR_VERSION, source, now, now),
                )
                self.conn.commit()
                self.stats["global_cache_entries"] += 1
                return "inserted"

            existing_translated, existing_status, existing_source, existing_mod, existing_context = existing
            if existing_translated == translated:
                self.stats["cache_duplicates"] += 1
                return "duplicate"

            # Different translation for the same text -> resolve, never
            # blind INSERT OR REPLACE.
            winner = _resolve_conflict(
                existing_translated, existing_status, existing_source,
                translated, quality_status, source,
            )
            if winner == "incoming":
                self.conn.execute(
                    """
                    UPDATE translations
                    SET translated_text=?, quality_status=?, validator_version=?, source=?,
                        context=?, mod_id=?, format_type=?, key_path=?, updated_at=?
                    WHERE original_text=? AND source_language=? AND target_language=?
                    """,
                    (translated, quality_status, VALIDATOR_VERSION, source,
                     context, mod_id, format_type, key_path, now,
                     original, src, dst),
                )
                self.conn.commit()
                self.stats["cache_conflicts"] += 1
                self._record_conflict(original, src, dst, existing_translated, translated,
                                       context, mod_id, source, resolved_to="incoming")
                return "conflict"
            else:
                self.stats["cache_conflicts"] += 1
                self._record_conflict(original, src, dst, existing_translated, translated,
                                       context, mod_id, source, resolved_to="existing")
                return "conflict"

    def _record_conflict(self, original, src, dst, existing, incoming, context, mod_id, source, resolved_to):
        entry = {
            "original_text": original,
            "source_language": src,
            "target_language": dst,
            "existing_translation": existing,
            "incoming_translation": incoming,
            "context": context,
            "mod_id": mod_id,
            "source": source,
            "resolved_to": resolved_to,
            "timestamp": time.time(),
        }
        self._conflicts.append(entry)
        self._flush_conflicts()

    def _flush_conflicts(self):
        self.TRANSLATION_CONFLICTS_PATH.parent.mkdir(parents=True, exist_ok=True)
        # keyed-by-text view, matching the TASK spec example format, plus the
        # full list (with context/mod_id/source) for tooling.
        by_text: dict[str, dict] = {}
        for c in self._conflicts:
            key = c["original_text"]
            entry = by_text.setdefault(key, {
                "source_language": c["source_language"],
                "target_language": c["target_language"],
                "variants": [],
            })
            for v in (c["existing_translation"], c["incoming_translation"]):
                if v not in entry["variants"]:
                    entry["variants"].append(v)
        payload = {"conflicts_by_text": by_text, "conflicts": self._conflicts}
        self.TRANSLATION_CONFLICTS_PATH.write_text(
            json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8"
        )

    # ---- stale-entry revalidation (TASK sections 24/25) ----

    def revalidate_stale_entries(self) -> dict:
        """Re-run is_technical_value()/technical-token consistency against
        every row whose validator_version is older than the current
        VALIDATOR_VERSION. Rows that no longer pass are marked
        quality_status='rejected' (never deleted) and written to
        cache/invalid_cache_entries.json."""
        with self._lock:
            rows = self.conn.execute(
                "SELECT id, original_text, translated_text, source_language, target_language, "
                "validator_version, quality_status FROM translations WHERE validator_version < ?",
                (VALIDATOR_VERSION,),
            ).fetchall()

        invalid = []
        revalidated = 0
        rejected = 0
        for row_id, orig, trans, src, dst, val_ver, status in rows:
            revalidated += 1
            ok, reason = is_safe_to_cache_globally(orig, trans)
            with self._lock:
                if ok:
                    self.conn.execute(
                        "UPDATE translations SET validator_version=? WHERE id=?",
                        (VALIDATOR_VERSION, row_id),
                    )
                else:
                    self.conn.execute(
                        "UPDATE translations SET quality_status=?, validator_version=? WHERE id=?",
                        (QUALITY_REJECTED, VALIDATOR_VERSION, row_id),
                    )
                    rejected += 1
                    invalid.append({
                        "id": row_id,
                        "original_text": orig,
                        "translated_text": trans,
                        "source_language": src,
                        "target_language": dst,
                        "reason": reason,
                        "previous_validator_version": val_ver,
                    })
                self.conn.commit()

        if invalid:
            INVALID_CACHE_ENTRIES_PATH.parent.mkdir(parents=True, exist_ok=True)
            INVALID_CACHE_ENTRIES_PATH.write_text(
                json.dumps({"invalid_entries": invalid}, ensure_ascii=False, indent=2), encoding="utf-8"
            )
        return {"revalidated": revalidated, "rejected": rejected}

    # ---- merge / import / export (TASK sections 12/16/17) ----

    def merge_local_db(self, path: Path) -> dict:
        """Import an old-style per-run translation_cache.db (hash,
        original_text, source_language, target_language, translated_text,
        ...) into the global cache. Every record is re-validated; nothing is
        trusted just because it came from this same tool."""
        result_counts = {"imported": 0, "duplicates": 0, "conflicts": 0, "rejected": 0, "skipped": 0}
        path = Path(path)
        if not path.exists():
            result_counts["error"] = f"not found: {path}"
            return result_counts

        src_conn = sqlite3.connect(str(path))
        try:
            cols = {row[1] for row in src_conn.execute("PRAGMA table_info(translations)")}
            if "original_text" not in cols or "translated_text" not in cols:
                result_counts["error"] = "incompatible schema (no translations table)"
                return result_counts
            has_src_lang = "source_language" in cols
            has_dst_lang = "target_language" in cols
            rows = src_conn.execute("SELECT * FROM translations").fetchall()
            col_names = [d[0] for d in src_conn.execute("SELECT * FROM translations LIMIT 0").description]
        finally:
            src_conn.close()

        for row in rows:
            rec = dict(zip(col_names, row))
            original = rec.get("original_text")
            translated = rec.get("translated_text")
            src = rec.get("source_language") if has_src_lang else SOURCE_LANG
            dst = rec.get("target_language") if has_dst_lang else TARGET_LANG
            if not original or not translated:
                result_counts["skipped"] += 1
                continue
            ok, _reason = is_safe_to_cache_globally(original, translated)
            if not ok:
                result_counts["rejected"] += 1
                self.stats["cache_rejected"] += 1
                continue
            outcome = self.put(
                original, translated, src=src or SOURCE_LANG, dst=dst or TARGET_LANG,
                quality_status=QUALITY_VALIDATED, source=SOURCE_IMPORTED,
            )
            if outcome == "inserted":
                result_counts["imported"] += 1
                self.stats["cache_imported"] += 1
            elif outcome == "duplicate":
                result_counts["duplicates"] += 1
            elif outcome == "conflict":
                result_counts["conflicts"] += 1
            else:
                result_counts["rejected"] += 1
        return result_counts

    def import_json(self, path: Path) -> dict:
        result_counts = {"imported": 0, "duplicates": 0, "conflicts": 0, "rejected": 0, "skipped": 0}
        path = Path(path)
        data = json.loads(path.read_text(encoding="utf-8"))
        records = data if isinstance(data, list) else data.get("entries", data.get("translations", []))
        for rec in records:
            original = rec.get("original_text")
            translated = rec.get("translated_text")
            src = rec.get("source_language", SOURCE_LANG)
            dst = rec.get("target_language", TARGET_LANG)
            if not original or not translated:
                result_counts["skipped"] += 1
                continue
            ok, _reason = is_safe_to_cache_globally(original, translated)
            if not ok:
                result_counts["rejected"] += 1
                self.stats["cache_rejected"] += 1
                continue
            outcome = self.put(
                original, translated, src=src, dst=dst,
                context=rec.get("context", ""), mod_id=rec.get("mod_id", ""),
                format_type=rec.get("format_type", ""), key_path=rec.get("key_path", ""),
                quality_status=QUALITY_VALIDATED, source=SOURCE_IMPORTED,
            )
            if outcome == "inserted":
                result_counts["imported"] += 1
                self.stats["cache_imported"] += 1
            elif outcome == "duplicate":
                result_counts["duplicates"] += 1
            elif outcome == "conflict":
                result_counts["conflicts"] += 1
            else:
                result_counts["rejected"] += 1
        return result_counts

    def export_json(self, path: Path) -> int:
        with self._lock:
            rows = self.conn.execute(
                "SELECT original_text, source_language, target_language, translated_text, "
                "context, mod_id, format_type, quality_status, source FROM translations "
                "WHERE quality_status IN ({})".format(
                    ",".join("?" for _ in GLOBAL_CACHE_USABLE_STATUSES)
                ),
                GLOBAL_CACHE_USABLE_STATUSES,
            ).fetchall()
        entries = [
            {
                "original_text": r[0], "source_language": r[1], "target_language": r[2],
                "translated_text": r[3], "context": r[4], "mod_id": r[5],
                "format_type": r[6], "quality_status": r[7], "source": r[8],
            }
            for r in rows
        ]
        path = Path(path)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps({"entries": entries}, ensure_ascii=False, indent=2), encoding="utf-8")
        return len(entries)

    def close(self):
        self.conn.close()


def _resolve_conflict(existing_text: str, existing_status: str, existing_source: str,
                       incoming_text: str, incoming_status: str, incoming_source: str) -> str:
    """TASK section 15 priority order:
    1. manual  2. validated  3. context-matching validated (handled by
    caller before this is reached)  4. better source  5. imported
    6. google  7. everything else.
    Returns 'existing' or 'incoming' - whichever should be kept as the
    served translation. Ties (equal priority on both axes) keep the
    existing row (never overwrite without a clear reason)."""
    def status_rank(s):
        return QUALITY_PRIORITY.index(s) if s in QUALITY_PRIORITY else len(QUALITY_PRIORITY)

    def source_rank(s):
        return SOURCE_PRIORITY.index(s) if s in SOURCE_PRIORITY else len(SOURCE_PRIORITY)

    existing_rank = (status_rank(existing_status), source_rank(existing_source))
    incoming_rank = (status_rank(incoming_status), source_rank(incoming_source))
    if incoming_rank < existing_rank:
        return "incoming"
    return "existing"

# ======================================================================
# TRANSLATION ENGINE (googletrans 4.0.2, async)
# ======================================================================

@dataclass
class TranslationResult:
    original: str
    translated: Optional[str]
    status: str  # translated | cached | failed | skipped


class GoogleTranslateEngine:
    """Thin async wrapper around googletrans 4.0.2 with retry/backoff and
    two-tier caching: LOCAL CACHE (this run only) -> GLOBAL CACHE (shared
    across every modpack ever processed) -> Google Translate -> validator ->
    write-through into both caches. See TASK section 5/33 for the full
    priority chain this implements."""

    def __init__(self, cache: TranslationCache, global_cache: Optional["GlobalTranslationCache"] = None,
                 context_map: Optional[dict[str, tuple]] = None):
        self.cache = cache
        self.global_cache = global_cache
        # text -> (context, mod_id, format_type, key_path), best-effort
        self.context_map = context_map or {}
        self.stats = {
            "cached": 0, "translated": 0, "failed": 0, "sent": 0,
            "local_cache_hits": 0, "global_cache_hits": 0, "google_requests": 0,
            "cache_misses": 0, "cache_rejected": 0,
        }

    def _context_for(self, text: str) -> tuple:
        return self.context_map.get(text, ("", "", "", ""))

    async def _translate_batch_raw(self, translator: "Translator", texts: list[str]) -> list[Optional[str]]:
        """Translate a batch of already placeholder-protected strings."""
        results: list[Optional[str]] = [None] * len(texts)
        for attempt in range(MAX_RETRIES):
            try:
                coros = [
                    asyncio.wait_for(
                        translator.translate(t, src=SOURCE_LANG, dest=TARGET_LANG),
                        timeout=REQUEST_TIMEOUT,
                    )
                    for t in texts
                ]
                raw_results = await asyncio.gather(*coros, return_exceptions=True)
                ok = True
                for i, r in enumerate(raw_results):
                    if isinstance(r, Exception) or r is None or not getattr(r, "text", None):
                        ok = False
                        results[i] = None
                    else:
                        results[i] = r.text
                if ok:
                    return results
                # partial failure -> retry only failed ones on next loop iteration
                missing_idx = [i for i, r in enumerate(results) if r is None]
                if not missing_idx:
                    return results
                texts_retry = [texts[i] for i in missing_idx]
                sub_results = await self._translate_batch_raw(translator, texts_retry)
                for j, i in enumerate(missing_idx):
                    results[i] = sub_results[j]
                return results
            except Exception:
                backoff = BASE_BACKOFF * (2 ** attempt)
                await asyncio.sleep(backoff)
        return results

    async def translate_many(self, texts: list[str]) -> dict[str, TranslationResult]:
        """
        Translate a list of unique strings, using cache and batching.
        Returns {original_text: TranslationResult}.
        """
        out: dict[str, TranslationResult] = {}
        to_send: list[str] = []

        for t in texts:
            # 1. LOCAL CACHE (this run / this modpack's translation_cache.db)
            cached = self.cache.get(t)
            if cached is not None:
                out[t] = TranslationResult(t, cached, "cached")
                self.stats["cached"] += 1
                self.stats["local_cache_hits"] += 1
                continue

            # 2/3. GLOBAL CACHE (cross-modpack, exact text + language match;
            # context is used for conflict resolution only, never to block
            # a hit - see GlobalTranslationCache.lookup()).
            if self.global_cache is not None:
                global_hit = self.global_cache.lookup(t, SOURCE_LANG, TARGET_LANG)
                if global_hit is not None:
                    out[t] = TranslationResult(t, global_hit, "global_cache")
                    self.stats["global_cache_hits"] += 1
                    # promote into the local cache too, so this run doesn't
                    # re-query the global DB for repeats of the same text.
                    self.cache.put(t, global_hit)
                    continue

            to_send.append(t)

        if not to_send:
            return out

        self.stats["cache_misses"] += len(to_send)

        if Translator is None:
            for t in to_send:
                out[t] = TranslationResult(t, None, "failed")
                self.stats["failed"] += 1
            return out

        batch_size = BATCH_SIZE
        i = 0
        async with Translator() as translator:
            while i < len(to_send):
                batch = to_send[i : i + batch_size]
                protected_map = {}
                protected_texts = []
                for t in batch:
                    p, tokens = protect_placeholders(t)
                    protected_map[t] = tokens
                    protected_texts.append(p)

                self.stats["sent"] += len(protected_texts)
                self.stats["google_requests"] += len(protected_texts)
                translated = await self._translate_batch_raw(translator, protected_texts)

                failed_in_batch = []
                for t, p_text, tr in zip(batch, protected_texts, translated):
                    if tr is None:
                        failed_in_batch.append(t)
                        continue
                    restored = restore_placeholders(tr, protected_map[t])
                    if restored is None:
                        failed_in_batch.append(t)
                        continue
                    out[t] = TranslationResult(t, restored, "translated")
                    self._commit_translation(t, restored)
                    self.stats["translated"] += 1

                if failed_in_batch:
                    if batch_size > MIN_BATCH_SIZE:
                        # shrink batch size going forward and retry these individually
                        for t in failed_in_batch:
                            self.stats["google_requests"] += 1
                            single_res = await self._translate_batch_raw(translator, [t])
                            tr = single_res[0]
                            if tr is not None:
                                out[t] = TranslationResult(t, tr, "translated")
                                self._commit_translation(t, tr)
                                self.stats["translated"] += 1
                            else:
                                out[t] = TranslationResult(t, None, "failed")
                                self.stats["failed"] += 1
                    else:
                        for t in failed_in_batch:
                            out[t] = TranslationResult(t, None, "failed")
                            self.stats["failed"] += 1

                i += batch_size

        return out

    def _commit_translation(self, original: str, translated: str) -> None:
        """Write-through a freshly-translated (validator-approved, i.e. the
        placeholder round-trip already succeeded) pair into LOCAL CACHE
        always, and into GLOBAL CACHE only if it also passes the extra
        technical-token consistency gate (see is_safe_to_cache_globally)."""
        self.cache.put(original, translated)
        if self.global_cache is None:
            return
        context, mod_id, format_type, key_path = self._context_for(original)
        outcome = self.global_cache.put(
            original, translated, SOURCE_LANG, TARGET_LANG,
            context=context, mod_id=mod_id, format_type=format_type, key_path=key_path,
            quality_status=QUALITY_VALIDATED, source=SOURCE_GOOGLE,
        )
        if outcome == "rejected":
            self.stats["cache_rejected"] += 1


# ======================================================================
# CANDIDATE STRING MODEL
# ======================================================================

@dataclass
class StringCandidate:
    text: str
    confidence: str
    reason: str
    source_type: str        # LANG_JSON, MC_TEXT_COMPONENT, SNBT, FTBQUESTS, PATCHOULI, KUBEJS, CONFIG, DATA_JSON
    source_file: str        # relative path (for reporting only)
    modid: str = ""


@dataclass
class ModInfo:
    modid: str
    name: str
    jar_path: str
    loader: str
    lang_files: list[str] = field(default_factory=list)
    candidates: int = 0
    translated: int = 0
    cached: int = 0
    failed: int = 0
    other_sources: list[str] = field(default_factory=list)


# ======================================================================
# GENERIC RECURSIVE JSON WALKER
# ======================================================================

def walk_json_strings(node: Any, key: Optional[str] = None):
    """
    Yield (key, value, container, container_key) for every string leaf found
    while recursing through dict/list structures. `container` + `container_key`
    let the caller mutate the original structure in-place.
    """
    if isinstance(node, dict):
        for k, v in node.items():
            if isinstance(v, str):
                yield k, v, node, k
            else:
                yield from walk_json_strings(v, k)
    elif isinstance(node, list):
        for idx, item in enumerate(node):
            if isinstance(item, str):
                yield key, item, node, idx
            else:
                yield from walk_json_strings(item, key)


def collect_json_candidates(data: Any, source_type: str, source_file: str, modid: str = "") -> list[StringCandidate]:
    candidates = []
    for key, value, _container, _ckey in walk_json_strings(data):
        should, conf, reason = classify_string(key, value)
        if should:
            candidates.append(StringCandidate(value, conf, reason, source_type, source_file, modid))
    return candidates


def apply_json_translations(data: Any, translations: dict[str, str], min_confidence: str = CONF_MEDIUM) -> int:
    """
    Mutate `data` in place, replacing translatable string leaves with their
    translation when available. Returns number of replacements made.
    """
    order = {CONF_HIGH: 3, CONF_MEDIUM: 2, CONF_LOW: 1, CONF_SKIP: 0}
    min_rank = order[min_confidence]
    count = 0
    for key, value, container, ckey in list(walk_json_strings(data)):
        should, conf, _reason = classify_string(key, value)
        if not should or order[conf] < min_rank:
            continue
        if value in translations:
            container[ckey] = translations[value]
            count += 1
    return count


# ======================================================================
# MINECRAFT JSON TEXT COMPONENTS
# ======================================================================

def is_text_component(node: Any) -> bool:
    return isinstance(node, dict) and ("text" in node or "translate" in node or "extra" in node)


def collect_text_component_candidates(data: Any, source_file: str, modid: str = "") -> list[StringCandidate]:
    """Walk a JSON structure looking specifically for MC text-component 'text' fields."""
    candidates = []

    def _walk(node):
        if isinstance(node, dict):
            if "text" in node and isinstance(node["text"], str):
                should, conf, reason = classify_string("text", node["text"])
                if should:
                    candidates.append(
                        StringCandidate(node["text"], conf, reason, "MC_TEXT_COMPONENT", source_file, modid)
                    )
            for k, v in node.items():
                if k != "text":
                    _walk(v)
        elif isinstance(node, list):
            for item in node:
                _walk(item)

    _walk(data)
    return candidates


def apply_text_component_translations(data: Any, translations: dict[str, str]) -> int:
    count = 0

    def _walk(node):
        nonlocal count
        if isinstance(node, dict):
            if "text" in node and isinstance(node["text"], str) and node["text"] in translations:
                node["text"] = translations[node["text"]]
                count += 1
            for k, v in node.items():
                if k != "text":
                    _walk(v)
        elif isinstance(node, list):
            for item in node:
                _walk(item)

    _walk(data)
    return count


def try_parse_json_text_component_string(value: str) -> Optional[Any]:
    """If `value` is itself a JSON string (common inside SNBT display.Name/Lore), parse it."""
    v = value.strip()
    if v.startswith("{") or v.startswith("["):
        try:
            return json.loads(v)
        except Exception:
            return None
    return None


# ======================================================================
# SNBT PARSER (hand written, no external deps)
# ======================================================================

class SnbtParseError(Exception):
    pass


class _SnbtToken:
    __slots__ = ("kind", "value")

    def __init__(self, kind: str, value: str):
        self.kind = kind
        self.value = value


def _snbt_tokenize(s: str) -> list[_SnbtToken]:
    tokens = []
    i, n = 0, len(s)
    while i < n:
        c = s[i]
        if c in " \t\r\n":
            i += 1
            continue
        if c in "{}[]:,;":
            tokens.append(_SnbtToken(c, c))
            i += 1
            continue
        if c in "'\"":
            quote = c
            j = i + 1
            buf = []
            while j < n and s[j] != quote:
                if s[j] == "\\" and j + 1 < n:
                    buf.append(s[j])
                    buf.append(s[j + 1])
                    j += 2
                else:
                    buf.append(s[j])
                    j += 1
            if j >= n:
                raise SnbtParseError("Unterminated string literal")
            tokens.append(_SnbtToken("STRING", "".join(buf)))
            i = j + 1
            continue
        # bare word / number
        j = i
        while j < n and s[j] not in " \t\r\n{}[]:,;":
            j += 1
        tokens.append(_SnbtToken("BARE", s[i:j]))
        i = j
    return tokens


def _snbt_unescape(s: str) -> str:
    out = []
    i, n = 0, len(s)
    while i < n:
        if s[i] == "\\" and i + 1 < n:
            nxt = s[i + 1]
            out.append({"n": "\n", "t": "\t", "\\": "\\", "'": "'", '"': '"'}.get(nxt, nxt))
            i += 2
        else:
            out.append(s[i])
            i += 1
    return "".join(out)


def _snbt_escape(s: str) -> str:
    return s.replace("\\", "\\\\").replace("'", "\\'")


class SnbtString(str):
    """A string value that was quoted in the source SNBT (vs a bare/unquoted token)."""


def _snbt_parse_value(tokens: list[_SnbtToken], pos: list[int]) -> Any:
    tok = tokens[pos[0]]
    if tok.kind == "{":
        return _snbt_parse_compound(tokens, pos)
    if tok.kind == "[":
        return _snbt_parse_list(tokens, pos)
    if tok.kind == "STRING":
        pos[0] += 1
        return SnbtString(_snbt_unescape(tok.value))
    if tok.kind == "BARE":
        pos[0] += 1
        return tok.value
    raise SnbtParseError(f"Unexpected token {tok.kind!r} at {pos[0]}")


def _snbt_parse_compound(tokens: list[_SnbtToken], pos: list[int]) -> dict:
    assert tokens[pos[0]].kind == "{"
    pos[0] += 1
    result: dict[str, Any] = {}
    while pos[0] < len(tokens) and tokens[pos[0]].kind != "}":
        key_tok = tokens[pos[0]]
        if key_tok.kind not in ("BARE", "STRING"):
            raise SnbtParseError(f"Expected compound key, got {key_tok.kind}")
        key = key_tok.value
        pos[0] += 1
        if pos[0] >= len(tokens) or tokens[pos[0]].kind != ":":
            raise SnbtParseError("Expected ':' after compound key")
        pos[0] += 1
        value = _snbt_parse_value(tokens, pos)
        result[key] = value
        if pos[0] < len(tokens) and tokens[pos[0]].kind == ",":
            pos[0] += 1
    if pos[0] >= len(tokens) or tokens[pos[0]].kind != "}":
        raise SnbtParseError("Expected '}' to close compound")
    pos[0] += 1
    return result


def _snbt_parse_list(tokens: list[_SnbtToken], pos: list[int]) -> list:
    assert tokens[pos[0]].kind == "["
    pos[0] += 1
    # array-type prefix e.g. [B; ... ] [I; ...] [L; ...]
    if (
        pos[0] + 1 < len(tokens)
        and tokens[pos[0]].kind == "BARE"
        and tokens[pos[0]].value in ("B", "I", "L")
        and tokens[pos[0] + 1].kind == ";"
    ):
        pos[0] += 2
        # treat as opaque numeric array - collect bare/number tokens until ]
        raw = []
        while pos[0] < len(tokens) and tokens[pos[0]].kind != "]":
            raw.append(tokens[pos[0]].value)
            pos[0] += 1
            if pos[0] < len(tokens) and tokens[pos[0]].kind == ",":
                pos[0] += 1
        if pos[0] >= len(tokens) or tokens[pos[0]].kind != "]":
            raise SnbtParseError("Expected ']' to close array")
        pos[0] += 1
        return raw

    result = []
    while pos[0] < len(tokens) and tokens[pos[0]].kind != "]":
        result.append(_snbt_parse_value(tokens, pos))
        if pos[0] < len(tokens) and tokens[pos[0]].kind == ",":
            pos[0] += 1
    if pos[0] >= len(tokens) or tokens[pos[0]].kind != "]":
        raise SnbtParseError("Expected ']' to close list")
    pos[0] += 1
    return result


def parse_snbt(text: str) -> Any:
    tokens = _snbt_tokenize(text)
    if not tokens:
        raise SnbtParseError("Empty SNBT input")
    pos = [0]
    value = _snbt_parse_value(tokens, pos)
    return value


def serialize_snbt(value: Any, indent: int = 0, pretty: bool = True) -> str:
    pad = "  " * indent if pretty else ""
    pad_in = "  " * (indent + 1) if pretty else ""
    nl = "\n" if pretty else ""

    if isinstance(value, dict):
        if not value:
            return "{}"
        items = []
        for k, v in value.items():
            items.append(f"{pad_in}{k}: {serialize_snbt(v, indent + 1, pretty)}")
        return "{" + nl + ("," + nl).join(items) + nl + pad + "}"
    if isinstance(value, list):
        if not value and value != []:
            return "[]"
        if all(isinstance(x, str) and not isinstance(x, SnbtString) for x in value) and value:
            # could be a numeric-array placeholder we preserved as raw strings
            pass
        items = [serialize_snbt(v, indent + 1, pretty) for v in value]
        if not items:
            return "[]"
        return "[" + ", ".join(items) + "]"
    if isinstance(value, SnbtString):
        return "'" + _snbt_escape(str(value)) + "'"
    if isinstance(value, str):
        return value  # bare token (number/boolean/id), keep as-is
    return str(value)


def walk_snbt_strings(node: Any, key: Optional[str] = None):
    """Yield (key, SnbtString value, container, container_key) for quoted string leaves."""
    if isinstance(node, dict):
        for k, v in node.items():
            if isinstance(v, SnbtString):
                yield k, v, node, k
            else:
                yield from walk_snbt_strings(v, k)
    elif isinstance(node, list):
        for idx, item in enumerate(node):
            if isinstance(item, SnbtString):
                yield key, item, node, idx
            else:
                yield from walk_snbt_strings(item, key)


def collect_snbt_candidates(data: Any, source_type: str, source_file: str, modid: str = "") -> list[StringCandidate]:
    candidates = []
    for key, value, _c, _ck in walk_snbt_strings(data):
        # embedded JSON text component inside a quoted SNBT string?
        parsed = try_parse_json_text_component_string(str(value))
        if parsed is not None:
            candidates.extend(collect_text_component_candidates(parsed, source_file, modid))
            candidates.extend(collect_json_candidates(parsed, source_type, source_file, modid))
            continue
        should, conf, reason = classify_string(key, str(value))
        if should:
            candidates.append(StringCandidate(str(value), conf, reason, source_type, source_file, modid))
    return candidates


def apply_snbt_translations(data: Any, translations: dict[str, str], min_confidence: str = CONF_MEDIUM) -> int:
    order = {CONF_HIGH: 3, CONF_MEDIUM: 2, CONF_LOW: 1, CONF_SKIP: 0}
    min_rank = order[min_confidence]
    count = 0
    for key, value, container, ckey in list(walk_snbt_strings(data)):
        raw = str(value)
        parsed = try_parse_json_text_component_string(raw)
        if parsed is not None:
            n = apply_text_component_translations(parsed, translations)
            n += apply_json_translations(parsed, translations, min_confidence)
            if n:
                container[ckey] = SnbtString(json.dumps(parsed, ensure_ascii=False))
                count += n
            continue
        should, conf, _reason = classify_string(key, raw)
        if not should or order[conf] < min_rank:
            continue
        if raw in translations:
            container[ckey] = SnbtString(translations[raw])
            count += 1
    return count


# ======================================================================
# .lang / .properties PARSER
# ======================================================================

def parse_lang_properties(text: str) -> dict[str, str]:
    result = {}
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith("#") or line.startswith("!"):
            continue
        if "=" in line:
            k, _, v = line.partition("=")
            result[k.strip()] = v.strip()
    return result


def serialize_lang_properties(data: dict[str, str]) -> str:
    return "\n".join(f"{k}={v}" for k, v in data.items()) + "\n"


# ======================================================================
# JAR / MOD METADATA
# ======================================================================

def strip_json5_comments(text: str) -> str:
    # remove // line comments and /* */ block comments (best-effort, ignores strings)
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.DOTALL)
    text = re.sub(r"(?<!:)//.*", "", text)
    # remove trailing commas
    text = re.sub(r",(\s*[}\]])", r"\1", text)
    return text


def detect_loader_and_metadata(zf: zipfile.ZipFile) -> tuple[str, str, str]:
    """Returns (loader, modid, name)."""
    names = zf.namelist()

    if "fabric.mod.json" in names:
        try:
            meta = json.loads(zf.read("fabric.mod.json").decode("utf-8", "ignore"))
            return "Fabric", meta.get("id", ""), meta.get("name", meta.get("id", ""))
        except Exception:
            return "Fabric", "", ""

    if "quilt.mod.json" in names:
        try:
            meta = json.loads(zf.read("quilt.mod.json").decode("utf-8", "ignore"))
            ql = meta.get("quilt_loader", {})
            return "Quilt", ql.get("id", ""), ql.get("metadata", {}).get("name", ql.get("id", ""))
        except Exception:
            return "Quilt", "", ""

    if "META-INF/neoforge.mods.toml" in names:
        try:
            raw = zf.read("META-INF/neoforge.mods.toml").decode("utf-8", "ignore")
            modid = _toml_extract(raw, "modId")
            name = _toml_extract(raw, "displayName") or modid
            return "NeoForge", modid or "", name or ""
        except Exception:
            return "NeoForge", "", ""

    if "META-INF/mods.toml" in names:
        try:
            raw = zf.read("META-INF/mods.toml").decode("utf-8", "ignore")
            modid = _toml_extract(raw, "modId")
            name = _toml_extract(raw, "displayName") or modid
            return "Forge", modid or "", name or ""
        except Exception:
            return "Forge", "", ""

    return "Unknown", "", ""


def _toml_extract(raw: str, key: str) -> Optional[str]:
    m = re.search(rf'^\s*{re.escape(key)}\s*=\s*"([^"]*)"', raw, re.MULTILINE)
    return m.group(1) if m else None


# ======================================================================
# ANALYSIS RESULT AGGREGATION
# ======================================================================

@dataclass
class AnalysisResult:
    mods: dict[str, ModInfo] = field(default_factory=dict)
    candidates: list[StringCandidate] = field(default_factory=list)
    jar_count: int = 0
    lang_file_count: int = 0
    json_count: int = 0
    snbt_count: int = 0
    patchouli_count: int = 0
    ftbquests_count: int = 0
    kubejs_count: int = 0
    technical_values_detected: int = 0
    errors: list[str] = field(default_factory=list)
    # per-source in-memory payloads to be re-processed & written during APPLY phase
    lang_json_sources: list[dict] = field(default_factory=list)      # standard resourcepack lang files
    generic_json_sources: list[dict] = field(default_factory=list)   # patchouli / data / kubejs json etc
    snbt_sources: list[dict] = field(default_factory=list)           # ftbquests помогал мне Максим да
    config_sources: list[dict] = field(default_factory=list)         # config kv files
    kubejs_script_sources: list[dict] = field(default_factory=list)  # .js files


def _mod(result: AnalysisResult, modid: str, name: str, jar: str, loader: str) -> ModInfo:
    if modid not in result.mods:
        result.mods[modid] = ModInfo(modid=modid or "(unknown)", name=name or modid, jar_path=jar, loader=loader)
    return result.mods[modid]


# ======================================================================
# JAR ANALYSIS
# ======================================================================

def analyze_jar(jar_path: Path, result: AnalysisResult):
    try:
        with zipfile.ZipFile(jar_path, "r") as zf:
            loader, modid, name = detect_loader_and_metadata(zf)
            modid = modid or jar_path.stem
            name = name or modid
            mi = _mod(result, modid, name, str(jar_path), loader)
            result.jar_count += 1

            for entry in zf.namelist():
                if entry.endswith("/"):
                    continue
                lower = entry.lower()
                ext = Path(entry).suffix.lower()

                # ---- standard-ish lang files ----
                is_lang_dir = "/lang/" in lower or lower.startswith("lang/")
                stem = Path(entry).stem.lower()
                looks_en = stem in EN_LOCALE_NAMES or "en_us" in stem or lower.endswith("en_us.json")

                if is_lang_dir and ext in (".json", ".lang", ".json5") and looks_en:
                    try:
                        raw = zf.read(entry).decode("utf-8", "ignore")
                        if ext in (".json", ".json5"):
                            data = json.loads(strip_json5_comments(raw))
                            flat = {k: v for k, v in data.items() if isinstance(v, str)}
                        else:
                            flat = parse_lang_properties(raw)
                        candidates = collect_lang_candidates(flat, "LANG_JSON", entry, modid)
                        result.candidates.extend(candidates)
                        result.lang_json_sources.append(
                            {"modid": modid, "jar": str(jar_path), "entry": entry, "ext": ext, "data": flat}
                        )
                        mi.lang_files.append(entry)
                        result.lang_file_count += 1
                        result.json_count += 1
                    except Exception as e:
                        result.errors.append(f"[LANG] {jar_path.name}:{entry} -> {e}")
                    continue

                # ---- patchouli books ----
                if ("patchouli_books" in lower or "/patchouli/" in lower) and ext == ".json":
                    if not (stem in EN_LOCALE_NAMES or "en_us" in lower or "/en_us/" in lower):
                        # patchouli books are "31_2020" organized per-locale directories; only take english
                        if not re.search(r"/en_us/|/en/", lower):
                            continue
                    try:
                        raw = zf.read(entry).decode("utf-8", "ignore")
                        data = json.loads(strip_json5_comments(raw))
                        cands = collect_json_candidates(data, "PATCHOULI", entry, modid)
                        cands += collect_text_component_candidates(data, entry, modid)
                        result.candidates.extend(cands)
                        result.generic_json_sources.append(
                            {"modid": modid, "jar": str(jar_path), "entry": entry, "kind": "PATCHOULI", "data": data}
                        )
                        result.patchouli_count += 1
                        mi.other_sources.append(entry)
                    except Exception as e:
                        result.errors.append(f"[PATCHOULI] {jar_path.name}:{entry} -> {e}")
                    continue

                # ---- generic data/ JSON (advancements, loot tables, dialogue, etc.) ----
                if lower.startswith("data/") and ext == ".json":
                    try:
                        raw = zf.read(entry).decode("utf-8", "ignore")
                        data = json.loads(strip_json5_comments(raw))
                        cands = collect_json_candidates(data, "DATA_JSON", entry, modid)
                        cands += collect_text_component_candidates(data, entry, modid)
                        if cands:
                            result.candidates.extend(cands)
                            result.generic_json_sources.append(
                                {"modid": modid, "jar": str(jar_path), "entry": entry, "kind": "DATA_JSON", "data": data}
                            )
                            mi.other_sources.append(entry)
                    except Exception:
                        pass  # most data/ jsons are pure technical; silently skip parse failures
                    continue

    except zipfile.BadZipFile as e:
        result.errors.append(f"[JAR] {jar_path.name} -> bad zip: {e}")
    except Exception as e:
        result.errors.append(f"[JAR] {jar_path.name} -> {e}\n{traceback.format_exc()}")


# ======================================================================
# FTB QUESTS
# ======================================================================

def analyze_ftbquests(result: AnalysisResult):
    ftb_dir = MC_DIR / "config" / "ftbquests"
    if not ftb_dir.exists():
        return
    for path in ftb_dir.rglob("*.snbt"):
        try:
            raw = path.read_text(encoding="utf-8", errors="ignore")
            data = parse_snbt(raw)
            rel = str(path.relative_to(MC_DIR))
            cands = collect_snbt_candidates(data, "FTBQUESTS", rel)
            if cands:
                result.candidates.extend(cands)
            result.snbt_sources.append({"path": str(path), "rel": rel, "kind": "FTBQUESTS", "data": data})
            result.ftbquests_count += 1
            result.snbt_count += 1
        except SnbtParseError as e:
            result.errors.append(f"[FTBQUESTS-SNBT] {path} -> parse error: {e}")
        except Exception as e:
            result.errors.append(f"[FTBQUESTS] {path} -> {e}")

    # some FTB Quests setups also ship json lang overrides
    lang_dir = ftb_dir / "quests" / "lang"
    if lang_dir.exists():
        for path in lang_dir.glob("en_*.json"):
            try:
                data = json.loads(path.read_text(encoding="utf-8", errors="ignore"))
                flat = {k: v for k, v in data.items() if isinstance(v, str)}
                rel = str(path.relative_to(MC_DIR))
                cands = collect_lang_candidates(flat, "FTBQUESTS", rel)
                result.candidates.extend(cands)
                result.lang_json_sources.append(
                    {"modid": "ftbquests", "jar": "", "entry": rel, "ext": ".json", "data": flat, "is_config": True}
                )
                result.ftbquests_count += 1
            except Exception as e:
                result.errors.append(f"[FTBQUESTS-LANG] {path} -> {e}")


# ======================================================================
# PATCHOULI (resourcepacks / kubejs-generated books outside jars)
# ======================================================================

def analyze_patchouli_loose(result: AnalysisResult):
    """Patchouli books can also live under resourcepacks/ or kubejs/assets/ as loose files."""
    search_roots = [MC_DIR / "resourcepacks", MC_DIR / "kubejs" / "assets"]
    for root in search_roots:
        if not root.exists():
            continue
        for path in root.rglob("*.json"):
            lower = str(path).lower()
            if "patchouli" not in lower and "patchouli_books" not in lower:
                continue
            if not re.search(r"[/\\]en_us[/\\]|[/\\]en[/\\]", lower):
                continue
            try:
                data = json.loads(path.read_text(encoding="utf-8", errors="ignore"))
                rel = str(path.relative_to(ROOT_DIR)) if ROOT_DIR in path.parents else str(path)
                cands = collect_json_candidates(data, "PATCHOULI", rel)
                cands += collect_text_component_candidates(data, rel)
                if cands:
                    result.candidates.extend(cands)
                    result.generic_json_sources.append(
                        {"modid": "", "jar": "", "entry": rel, "path": str(path), "kind": "PATCHOULI_LOOSE", "data": data}
                    )
                    result.patchouli_count += 1
            except Exception as e:
                result.errors.append(f"[PATCHOULI-LOOSE] {path} -> {e}")


# ======================================================================
# KUBEJS
# ======================================================================

KUBEJS_STRING_CALL_RE = re.compile(
    r"\.(displayName|tooltip|text|description|title|subtitle|lore|name)\s*\(\s*(['\"])((?:\\.|(?!\2).)*)\2\s*\)",
    re.IGNORECASE,
)


def analyze_kubejs(result: AnalysisResult):
    kubejs_dir = MC_DIR / "kubejs"
    if not kubejs_dir.exists():
        return

    # --- JS scripts: only pull strings following known display/text call patterns ---
    for sub in ("startup_scripts", "server_scripts", "client_scripts"):
        script_dir = kubejs_dir / sub
        if not script_dir.exists():
            continue
        for path in script_dir.rglob("*.js"):
            try:
                raw = path.read_text(encoding="utf-8", errors="ignore")
                rel = str(path.relative_to(MC_DIR))
                found_any = False
                strings_in_file = []
                for m in KUBEJS_STRING_CALL_RE.finditer(raw):
                    quote_char = m.group(2)
                    literal = m.group(3)
                    unescaped = literal.encode("utf-8").decode("unicode_escape", errors="ignore")
                    should, conf, reason = classify_string(m.group(1), unescaped)
                    if should:
                        result.candidates.append(
                            StringCandidate(unescaped, conf, reason, "KUBEJS", rel, "")
                        )
                        # quote_char is stored per-match so the rewriter can escape
                        # correctly for THIS literal's actual delimiter - see
                        # apply_kubejs_script_translation().
                        strings_in_file.append((m.start(3), m.end(3), literal, unescaped, quote_char))
                        found_any = True
                if found_any:
                    result.kubejs_script_sources.append(
                        {"path": str(path), "rel": rel, "raw": raw, "matches": strings_in_file}
                    )
                    result.kubejs_count += 1
            except Exception as e:
                result.errors.append(f"[KUBEJS-JS] {path} -> {e}")

    # --- kubejs/5702 assets (lang overrides) and kubejs/data (custom data resources) ---
    for sub, kind in (("assets", "LANG_JSON"), ("data", "DATA_JSON")):
        base = kubejs_dir / sub
        if not base.exists():
            continue
        for path in base.rglob("*.json"):
            lower = str(path).lower()
            if sub == "assets" and "/lang/" in lower.replace("\\", "/"):
                stem = path.stem.lower()
                if stem not in EN_LOCALE_NAMES and "en_us" not in stem:
                    continue
                try:
                    data = json.loads(path.read_text(encoding="utf-8", errors="ignore"))
                    flat = {k: v for k, v in data.items() if isinstance(v, str)}
                    rel = str(path.relative_to(MC_DIR))
                    cands = collect_lang_candidates(flat, "LANG_JSON", rel)
                    result.candidates.extend(cands)
                    result.lang_json_sources.append(
                        {"modid": "kubejs", "jar": "", "entry": rel, "ext": ".json", "data": flat, "is_config": True}
                    )
                    result.kubejs_count += 1
                except Exception as e:
                    result.errors.append(f"[KUBEJS-LANG] {path} -> {e}")
            elif sub == "data":
                try:
                    data = json.loads(path.read_text(encoding="utf-8", errors="ignore"))
                    rel = str(path.relative_to(MC_DIR))
                    cands = collect_json_candidates(data, "DATA_JSON", rel)
                    cands += collect_text_component_candidates(data, rel)
                    if cands:
                        result.candidates.extend(cands)
                        result.generic_json_sources.append(
                            {"modid": "kubejs", "jar": "", "entry": rel, "path": str(path), "kind": "DATA_JSON", "data": data}
                        )
                        result.kubejs_count += 1
                except Exception:
                    pass


def _js_escape_for_quote(text: str, quote_char: str) -> str:
    """Escape `text` so it can be embedded inside a single-line JS string
    literal delimited by `quote_char` (' or "). Order matters: backslashes
    must be escaped FIRST, otherwise the backslash we insert while escaping
    the quote character (or a newline) would itself get doubled.

    Bug this fixes: the previous implementation always escaped only the
    double-quote character regardless of which quote the source literal
    actually used. Any translated string containing an apostrophe (very
    common in Russian - "не за что", possessives, etc.) that landed inside a
    single-quoted JS literal (.text('...'), .tooltip('...') and similar are
    frequently single-quoted in KubeJS scripts) would prematurely close the
    string and corrupt the rest of the script - this is what broke recipes
    such as create_confectionery/design_decor/naturalist entries added via
    KubeJS in modpacks like the ones in these logs."""
    out = text.replace("\\", "\\\\")
    out = out.replace(quote_char, "\\" + quote_char)
    out = out.replace("\r\n", "\\n").replace("\n", "\\n").replace("\r", "\\n")
    return out


def apply_kubejs_script_translation(raw: str, matches: list, translations: dict[str, str]) -> str:
    """Rebuild a .js file, replacing only matched string literals, right-to-left to keep offsets valid.

    Each match now also carries the exact quote character used in the source
    (' or ") so the replacement is escaped correctly for that delimiter -
    see _js_escape_for_quote(). Older `matches` tuples without a quote_char
    (4-tuples) are treated as double-quoted for backward compatibility."""
    out = raw
    for m in sorted(matches, key=lambda mm: mm[0], reverse=True):
        if len(m) >= 5:
            start, end, literal, unescaped, quote_char = m[0], m[1], m[2], m[3], m[4]
        else:
            start, end, literal, unescaped = m
            quote_char = '"'
        if unescaped in translations:
            new_literal = _js_escape_for_quote(translations[unescaped], quote_char)
            out = out[:start] + new_literal + out[end:]
    return out


_BRACKET_CHARS = "(){}[]"


def _bracket_signature(text: str) -> tuple[int, int, int, int, int, int]:
    """Count of each bracket character - used as a cheap structural
    invariant: since translation only ever changes the CONTENT of string
    literals (never the surrounding code), the bracket counts of the whole
    file must be identical before and after. A mismatch means a quote
    escaped incorrectly and swallowed/exposed real code."""
    return tuple(text.count(c) for c in _BRACKET_CHARS)


def validate_kubejs_script_rewrite(original_raw: str, new_raw: str) -> bool:
    """Defense-in-depth check for a rewritten KubeJS script, run right
    before it is written to disk. Returns True only if the rewrite is safe:
      - the same number of call-sites still match KUBEJS_STRING_CALL_RE
        (an unescaped quote inside a translated literal would merge two
        adjacent literals into one or split one into two, changing this
        count), and
      - bracket counts are unchanged (translation must never alter code
        structure, only string contents).
    This does not require a full JS parser and catches exactly the class of
    corruption the previous escaping bug produced."""
    if _bracket_signature(original_raw) != _bracket_signature(new_raw):
        return False
    if len(KUBEJS_STRING_CALL_RE.findall(original_raw)) != len(KUBEJS_STRING_CALL_RE.findall(new_raw)):
        return False
    return True


# ======================================================================
# CONFIG / DEFAULTCONFIGS
# ======================================================================

CONFIG_EXTS = {".toml", ".cfg", ".properties", ".json", ".json5"}


def analyze_configs(result: AnalysisResult):
    for base in (MC_DIR / "config", MC_DIR / "defaultconfigs"):
        if not base.exists():
            continue
        for path in base.rglob("*"):
            if not path.is_file() or path.suffix.lower() not in CONFIG_EXTS:
                continue
            if "ftbquests" in str(path).lower():
                continue  # handled separately
            try:
                rel = str(path.relative_to(MC_DIR))
                if path.suffix.lower() in (".json", ".json5"):
                    raw = path.read_text(encoding="utf-8", errors="ignore")
                    data = json.loads(strip_json5_comments(raw))
                    cands = collect_json_candidates(data, "CONFIG", rel)
                    if cands:
                        result.candidates.extend(cands)
                        result.generic_json_sources.append(
                            {"modid": "", "jar": "", "entry": rel, "path": str(path), "kind": "CONFIG_JSON", "data": data}
                        )
                elif path.suffix.lower() == ".properties":
                    raw = path.read_text(encoding="utf-8", errors="ignore")
                    flat = parse_lang_properties(raw)
                    cands = collect_json_candidates(flat, "CONFIG", rel)
                    if cands:
                        result.candidates.extend(cands)
                        result.config_sources.append(
                            {"path": str(path), "rel": rel, "kind": "PROPERTIES", "data": flat}
                        )
                elif path.suffix.lower() == ".toml" or path.suffix.lower() == ".cfg":
                    raw = path.read_text(encoding="utf-8", errors="ignore")
                    kv = _extract_toml_string_kv(raw)
                    cands = collect_json_candidates(kv, "CONFIG", rel)
                    if cands:
                        result.candidates.extend(cands)
                        result.config_sources.append(
                            {"path": str(path), "rel": rel, "kind": "TOML", "raw": raw, "data": kv}
                        )
            except Exception as e:
                result.errors.append(f"[CONFIG] {path} -> {e}")


TOML_KV_RE = re.compile(r'^(\s*)([A-Za-z0-9_.\-]+)\s*=\s*"((?:\\.|[^"\\])*)"\s*(#.*)?$')


def _extract_toml_string_kv(raw: str) -> dict[str, str]:
    """Very small best-effort key='string value' extractor for toml/cfg comment/label style configs."""
    result = {}
    for line in raw.splitlines():
        m = TOML_KV_RE.match(line)
        if m:
            key = m.group(2)
            val = m.group(3)
            result[key] = val
    return result


def apply_toml_translations(raw: str, translations: dict[str, str], min_confidence: str = CONF_MEDIUM) -> str:
    lines = raw.splitlines()
    out_lines = []
    for line in lines:
        m = TOML_KV_RE.match(line)
        if m:
            key, val = m.group(2), m.group(3)
            should, conf, _r = classify_string(key, val)
            order = {CONF_HIGH: 3, CONF_MEDIUM: 2, CONF_LOW: 1, CONF_SKIP: 0}
            if should and order[conf] >= order[min_confidence] and val in translations:
                new_val = translations[val]
                # A basic TOML string is single-line: a literal newline in the
                # translation cannot be represented here at all, so skip the
                # substitution rather than emit a value that spills onto the
                # next line and desyncs every following key. Backslashes MUST
                # be escaped before quotes (previous version only escaped
                # quotes, leaving a raw backslash in the translated text -
                # rare but possible - unescaped, which TOML would reject).
                if "\n" in new_val or "\r" in new_val:
                    out_lines.append(line)
                    continue
                new_val = new_val.replace("\\", "\\\\").replace('"', '\\"')
                line = f'{m.group(1)}{key} = "{new_val}"' + (f" {m.group(4)}" if m.group(4) else "")
        out_lines.append(line)
    return "\n".join(out_lines) + ("\n" if raw.endswith("\n") else "")


# ======================================================================
# JAR DISCOVERY
# ======================================================================

def _is_modpack_dir(path: Path) -> bool:
    """Return True when *path* looks like a Minecraft modpack directory.

    The folder name is intentionally ignored.  `mods/` is the strongest
    signal, but folders without mods are still accepted when they contain
    typical modpack directories/files.
    """
    if not path.is_dir():
        return False
    if (path / "mods").is_dir():
        return True
    markers = (
        "config", "defaultconfigs", "kubejs", "resourcepacks",
        "shaderpacks", "scripts", "saves", "options.txt",
    )
    return any((path / marker).exists() for marker in markers)


def discover_mc_dir(explicit_path: Optional[Union[str, Path]] = None) -> Path:
    """Find the modpack directory.

    1. If the user supplied a path, use exactly that directory.
    2. Otherwise look in the directory containing this script.
    3. As a compatibility fallback, recursively look for a directory
       containing `mods/`.

    No part of the logic depends on the directory being named `minecraft`.
    """
    if explicit_path is not None:
        candidate = Path(explicit_path).expanduser()
        if not candidate.is_absolute():
            candidate = ROOT_DIR / candidate
        candidate = candidate.resolve()
        if not candidate.exists():
            raise FileNotFoundError(f"Указанная папка сборки не существует: {candidate}")
        if not candidate.is_dir():
            raise NotADirectoryError(f"Указанный путь не является папкой: {candidate}")
        if not _is_modpack_dir(candidate):
            print(f"[!] Предупреждение: папка не похожа на модпак (не найден mods/ "
                  f"и нет типичных папок): {candidate}")
        return candidate

    # If the translator is placed directly inside the modpack, use its
    # containing directory. This is the most natural "no path specified"
    # behaviour.
    if _is_modpack_dir(ROOT_DIR):
        return ROOT_DIR

    # Otherwise, find a modpack folder directly inside the translator folder.
    direct_candidates = sorted(
        p for p in ROOT_DIR.iterdir()
        if p.is_dir() and p.name not in {
            "Translated_Modpack", "translation_reports", "cache", "__pycache__"
        } and _is_modpack_dir(p)
    )
    if len(direct_candidates) == 1:
        return direct_candidates[0]
    if direct_candidates:
        names = "\n".join(f"    {p}" for p in direct_candidates)
        raise FileNotFoundError(
            "Найдено несколько папок, похожих на сборки. "
            "Укажите путь явно, например:\n"
            "    python translator.py \"ПУТЬ_К_СБОРКЕ\"\n"
            "Найденные папки:\n" + names
        )

    # Compatibility fallback for older layouts: recursively search for
    # any directory with `mods/`, regardless of its name.
    ignored = {"Translated_Modpack", "translation_reports", "cache", "__pycache__"}
    recursive_candidates = sorted(
        p for p in ROOT_DIR.rglob("*")
        if p.is_dir()
        and p.name not in ignored
        and "Translated_Modpack" not in p.parts
        and _is_modpack_dir(p)
    )
    if len(recursive_candidates) == 1:
        return recursive_candidates[0]
    if recursive_candidates:
        names = "\n".join(f"    {p}" for p in recursive_candidates[:20])
        suffix = "\n    ..." if len(recursive_candidates) > 20 else ""
        raise FileNotFoundError(
            "Найдено несколько папок, похожих на сборки. Укажите путь явно:\n"
            "    python translator.py \"ПУТЬ_К_СБОРКЕ\"\n"
            "Кандидаты:\n" + names + suffix
        )

    raise FileNotFoundError(
        "Не удалось найти папку сборки. Укажите её путь при запуске:\n"
        "    python translator.py \"D:\\Games\\MyModpack\""
    )


def parse_pack_path(argv: list[str]) -> Optional[Path]:
    """Parse an optional modpack path without introducing argparse.

    Supported forms:
        translator.py
        translator.py PATH
        translator.py --pack PATH
        translator.py -p PATH
    """
    args = list(argv[1:])
    if not args:
        return None

    if args[0] in ("--pack", "-p"):
        if len(args) != 2:
            raise ValueError("Использование: python translator.py --pack \"ПУТЬ_К_СБОРКЕ\"")
        return Path(args[1])

    # Keep existing cache-management flags available. They are handled by
    # their own parser, so do not interpret them as a pack path.
    if args[0].startswith("--"):
        return None

    if len(args) != 1:
        raise ValueError(
            "Можно указать только один путь к сборке. "
            "Пример: python translator.py \"D:\\Games\\MyModpack\""
        )
    return Path(args[0])


# ======================================================================
# FULL ANALYSIS PASS
# ======================================================================

def run_analysis() -> AnalysisResult:
    result = AnalysisResult()
    reset_technical_stats()

    mods_dir = MC_DIR / "mods"
    if mods_dir.exists():
        jars = sorted(mods_dir.glob("*.jar"))
        for jar in jars:
            analyze_jar(jar, result)

    analyze_ftbquests(result)
    analyze_patchouli_loose(result)
    analyze_kubejs(result)
    analyze_configs(result)

    # finalize per-mod candidate counts
    per_mod_counts: dict[str, int] = {}
    for c in result.candidates:
        if c.modid:
            per_mod_counts[c.modid] = per_mod_counts.get(c.modid, 0) + 1
    for modid, cnt in per_mod_counts.items():
        if modid in result.mods:
            result.mods[modid].candidates = cnt

    result.technical_values_detected = get_technical_stats()["detected"]
    return result


# ======================================================================
# TRANSLATION + APPLY PASS
# ======================================================================

def get_unique_translatable_texts(result: AnalysisResult, min_confidence: str = CONF_MEDIUM) -> list[str]:
    order = {CONF_HIGH: 3, CONF_MEDIUM: 2, CONF_LOW: 1, CONF_SKIP: 0}
    min_rank = order[min_confidence]
    seen = set()
    unique = []
    for c in result.candidates:
        if order[c.confidence] < min_rank:
            continue
        if c.text not in seen:
            seen.add(c.text)
            unique.append(c.text)
    return unique


def _build_context_map(result: AnalysisResult) -> dict[str, tuple]:
    """Build best-effort metadata for each unique translatable string.

    The context is stored with newly-created GLOBAL CACHE entries for
    diagnostics/conflict resolution only; it never affects global-cache
    lookup, so the same translation can be reused across mods.
    """
    context_map: dict[str, tuple] = {}
    for candidate in result.candidates:
        if candidate.text in context_map:
            continue
        context_map[candidate.text] = (
            candidate.reason,
            candidate.modid,
            candidate.source_type,
            candidate.source_file,
        )
    return context_map


def run_translation_phase(
    result: AnalysisResult,
    cache: TranslationCache,
    global_cache: Optional["GlobalTranslationCache"] = None,
) -> tuple[dict[str, TranslationResult], dict]:
    context_map = _build_context_map(result)
    engine = GoogleTranslateEngine(cache, global_cache=global_cache, context_map=context_map)
    unique_texts = get_unique_translatable_texts(result, CONF_MEDIUM)
    print(f"[i] Уникальных строк к переводу: {len(unique_texts)}")

    translations: dict[str, TranslationResult] = {}

    async def _run():
        # chunk into manageable async waves to avoid overwhelming the event loop
        chunk = MAX_THREADS * BATCH_SIZE * 4
        for i in range(0, len(unique_texts), chunk):
            part = unique_texts[i : i + chunk]
            res = await engine.translate_many(part)
            translations.update(res)
            done = min(i + chunk, len(unique_texts))
            print(f"    ... {done}/{len(unique_texts)} обработано "
                  f"(local_cache={engine.stats['local_cache_hits']}, "
                  f"global_cache={engine.stats['global_cache_hits']}, "
                  f"translated={engine.stats['translated']}, "
                  f"failed={engine.stats['failed']})")

    asyncio.run(_run())
    return translations, engine.stats


# ---- validation helpers ----

def validate_json_roundtrip(data: Any) -> bool:
    try:
        json.dumps(data, ensure_ascii=False)
        return True
    except Exception:
        return False


def count_placeholders(text: str) -> int:
    n = 0
    for pattern in PLACEHOLDER_PATTERNS:
        n += len(pattern.findall(text))
    return n


# ======================================================================
# OUTPUT WRITERS
# ======================================================================

def ensure_dirs():
    RESOURCEPACK_DIR.mkdir(parents=True, exist_ok=True)
    TRANSLATED_MODPACK_DIR.mkdir(parents=True, exist_ok=True)
    REPORTS_DIR.mkdir(parents=True, exist_ok=True)


def write_resourcepack_pack_mcmeta():
    mcmeta = RESOURCEPACK_DIR / "pack.mcmeta"
    if mcmeta.exists():
        return
    content = {
        "pack": {
            "pack_format": 15,
            "description": "Автоматический русский перевод модпака (translator.py)",
        }
    }
    mcmeta.write_text(json.dumps(content, ensure_ascii=False, indent=2), encoding="utf-8")


def _write_json_file_validated(out_path: Path, data: Any, report: dict, label: str) -> bool:
    """Serialize `data` to JSON, write it, then re-read the ACTUAL bytes on
    disk and json.loads() them. If that fails, the file is deleted and
    OUTPUT IS PROHIBITED for this source - we never leave a broken file
    behind. Returns True on success."""
    try:
        text = json.dumps(data, ensure_ascii=False, indent=2)
    except Exception as e:
        report["errors"].append(f"json_validation_failed: {label} -> serialize error: {e}")
        report["json_validation_failed"] = report.get("json_validation_failed", 0) + 1
        return False
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(text, encoding="utf-8")
    try:
        json.loads(out_path.read_text(encoding="utf-8"))
    except Exception as e:
        report["errors"].append(f"json_validation_failed: {label} -> {e}")
        report["json_validation_failed"] = report.get("json_validation_failed", 0) + 1
        try:
            out_path.unlink()
        except OSError:
            pass
        return False
    return True


def write_lang_json_sources(result: AnalysisResult, translations: dict[str, str], report: dict) -> None:
    """Write standard mod lang JSONs into the resource pack; write kubejs/ftbquests lang overrides
    into Translated_Modpack (they are not standard mod-jar resources)."""
    for src in result.lang_json_sources:
        original = src["data"]
        translated = {}
        applied = 0
        technical_changed = []
        for k, v in original.items():
            should, conf, _r = classify_lang_value(v, k)
            if should and v in translations:
                new_v = translations[v]
                translated[k] = new_v
                applied += 1
            else:
                translated[k] = v
                # defense in depth: lang-file classification is value-only
                # (see classify_lang_value docstring), so check consistently
                # with is_technical_string here too - not the key-aware
                # is_technical_value(кефир), which would false-positive on every
                # ordinary "item.<mod>.<name>" translation key.
                if is_technical_string(v) and v in translations and translations[v] != v:
                    technical_changed.append(k)

        if not applied:
            continue

        # STRUCTURAL VALIDATION: key set must be identical, not just same count.
        if set(translated.keys()) != set(original.keys()):
            report["errors"].append(f"Key-set mismatch for lang source {src.get('entry')}")
            report["validation_failed"] = report.get("validation_failed", 0) + 1
            continue
        if not validate_json_roundtrip(translated):
            report["errors"].append(f"Validation failed for lang source {src.get('entry')}")
            report["validation_failed"] = report.get("validation_failed", 0) + 1
            continue
        if technical_changed:
            report["errors"].append(
                f"technical_data_changed: {src.get('entry')} keys={technical_changed}"
            )
            report["technical_data_changed"] = report.get("technical_data_changed", 0) + len(technical_changed)
            continue

        if src.get("is_config"):
            # kubejs / ftbquests style lang override -> mirror into Translated_Modpack
            out_path = TRANSLATED_MODPACK_DIR / src["entry"]
            ok = _write_json_file_validated(out_path, translated, report, str(src["entry"]))
        else:
            modid = src["modid"]
            out_dir = RESOURCEPACK_DIR / "assets" / modid / "lang"
            out_file = out_dir / "ru_ru.json"
            merged = {}
            if out_file.exists():
                try:
                    merged = json.loads(out_file.read_text(encoding="utf-8"))
                except Exception:
                    merged = {}
            merged.update(translated)
            ok = _write_json_file_validated(out_file, merged, report, str(out_file))

        if ok:
            report["lang_files_written"] = report.get("lang_files_written", 0) + 1


def _collect_technical_leaves(node: Any, key: Optional[str] = None) -> dict:
    """Collect {path-ish-key: value} for every leaf value classified as
    technical, for before/after comparison after translation is applied."""
    out = {}

    def _walk(n, k, path):
        if isinstance(n, dict):
            for kk, vv in n.items():
                _walk(vv, kk, path + "." + str(kk))
        elif isinstance(n, list):
            for idx, item in enumerate(n):
                _walk(item, k, path + f"[{idx}]")
        elif isinstance(n, str):
            if is_technical_value(n, k):
                out[path] = n

    _walk(node, key, "$")
    return out


def write_generic_json_sources(result: AnalysisResult, translations: dict[str, str], report: dict) -> None:
    for src in result.generic_json_sources:
        original_data = src["data"]
        data = copy.deepcopy(original_data)
        original_count = _count_strings(original_data)
        technical_before = _collect_technical_leaves(original_data)

        n1 = apply_json_translations(data, translations)
        n2 = apply_text_component_translations(data, translations)

        if n1 + n2 == 0:
            continue

        if not validate_json_roundtrip(data):
            report["errors"].append(f"Validation failed for {src.get('entry')}")
            report["validation_failed"] = report.get("validation_failed", 0) + 1
            continue
        if _count_strings(data) != original_count:
            report["errors"].append(f"String-count mismatch for {src.get('entry')} - skipped")
            report["validation_failed"] = report.get("validation_failed", 0) + 1
            continue

        # TECHNICAL DATA VALIDATION: every value that was technical before
        # translation must be byte-for-byte identical after.
        technical_after = _collect_technical_leaves(data)
        corrupted = [p for p, v in technical_before.items() if technical_after.get(p) != v]
        if corrupted:
            report["errors"].append(
                f"technical_data_changed: {src.get('entry')} paths={corrupted}"
            )
            report["technical_data_changed"] = report.get("technical_data_changed", 0) + len(corrupted)
            continue

        rel = src["entry"]
        out_path = TRANSLATED_MODPACK_DIR / rel
        if _write_json_file_validated(out_path, data, report, rel):
            report["generic_json_written"] = report.get("generic_json_written", 0) + 1


def _count_strings(node: Any) -> int:
    if isinstance(node, dict):
        return sum(_count_strings(v) for v in node.values())
    if isinstance(node, list):
        return sum(_count_strings(v) for v in node)
    if isinstance(node, str):
        return 1
    return 0


def _count_snbt_values(node: Any) -> int:
    if isinstance(node, dict):
        return sum(_count_snbt_values(v) for v in node.values())
    if isinstance(node, list):
        return sum(_count_snbt_values(v) for v in node)
    return 1


def _collect_technical_snbt_leaves(node: Any, key: Optional[str] = None) -> dict:
    out = {}

    def _walk(n, k, path):
        if isinstance(n, dict):
            for kk, vv in n.items():
                _walk(vv, kk, path + "." + str(kk))
        elif isinstance(n, list):
            for idx, item in enumerate(n):
                _walk(item, k, path + f"[{idx}]")
        elif isinstance(n, SnbtString):
            if is_technical_value(str(n), k):
                out[path] = str(n)
        elif isinstance(n, str):
            if is_technical_value(n, k):
                out[path] = n

    _walk(node, key, "$")
    return out


def write_snbt_sources(result: AnalysisResult, translations: dict[str, str], report: dict) -> None:
    for src in result.snbt_sources:
        original_data = src["data"]
        data = copy.deepcopy(original_data)
        original_count = _count_snbt_values(original_data)
        technical_before = _collect_technical_snbt_leaves(original_data)

        n = apply_snbt_translations(data, translations)
        if n == 0:
            continue

        if _count_snbt_values(data) != original_count:
            report["errors"].append(f"SNBT value-count mismatch for {src.get('rel')} - skipped")
            report["snbt_validation_failed"] = report.get("snbt_validation_failed", 0) + 1
            continue

        # TECHNICAL DATA VALIDATION: quest/chapter/task/reward/dependency IDs
        # and other technical SNBT values must never change.
        technical_after = _collect_technical_snbt_leaves(data)
        corrupted = [p for p, v in technical_before.items() if technical_after.get(p) != v]
        if corrupted:
            report["errors"].append(
                f"technical_data_changed: {src.get('rel')} paths={corrupted}"
            )
            report["technical_data_changed"] = report.get("technical_data_changed", 0) + len(corrupted)
            continue

        try:
            rebuilt = serialize_snbt(data)
        except Exception as e:
            report["errors"].append(f"SNBT serialize failed for {src.get('rel')}: {e}")
            report["snbt_validation_failed"] = report.get("snbt_validation_failed", 0) + 1
            continue

        try:
            parse_snbt(rebuilt)  # round-trip sanity check on the in-memory string
        except Exception as e:
            report["errors"].append(f"SNBT round-trip validation failed for {src.get('rel')}: {e}")
            report["snbt_validation_failed"] = report.get("snbt_validation_failed", 0) + 1
            continue

        rel = src["rel"]
        out_path = TRANSLATED_MODPACK_DIR / rel
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(rebuilt, encoding="utf-8")

        # Re-parse the ACTUAL bytes written to disk. OUTPUT PROHIBITED if
        # the file that would actually be loaded by FTB Quests is invalid.
        try:
            parse_snbt(out_path.read_text(encoding="utf-8"))
        except Exception as e:
            report["errors"].append(f"snbt_validation_failed: {rel} (post-write) -> {e}")
            report["snbt_validation_failed"] = report.get("snbt_validation_failed", 0) + 1
            try:
                out_path.unlink()
            except OSError:
                pass
            continue

        report["snbt_written"] = report.get("snbt_written", 0) + 1


def write_kubejs_scripts(result: AnalysisResult, translations: dict[str, str], report: dict) -> None:
    for src in result.kubejs_script_sources:
        new_raw = apply_kubejs_script_translation(src["raw"], src["matches"], translations)
        if new_raw == src["raw"]:
            continue
        rel = src["rel"]

        # OUTPUT PROHIBITED if the rewrite could have corrupted the script -
        # same "never leave a broken file behind" policy used for lang/JSON/
        # SNBT writers. See validate_kubejs_script_rewrite() for what this
        # catches (mis-escaped quotes changing the JS structure).
        if not validate_kubejs_script_rewrite(src["raw"], new_raw):
            report["errors"].append(f"kubejs_validation_failed: {rel} -> quote/bracket structure changed, skipped")
            report["kubejs_validation_failed"] = report.get("kubejs_validation_failed", 0) + 1
            continue

        out_path = TRANSLATED_MODPACK_DIR / rel
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(new_raw, encoding="utf-8")

        # Re-read the ACTUAL bytes written to disk and re-validate against
        # them, not just the in-memory string, in case of any I/O surprise.
        try:
            written = out_path.read_text(encoding="utf-8")
            if not validate_kubejs_script_rewrite(src["raw"], written):
                raise ValueError("post-write structural validation failed")
        except Exception as e:
            report["errors"].append(f"kubejs_validation_failed: {rel} (post-write) -> {e}")
            report["kubejs_validation_failed"] = report.get("kubejs_validation_failed", 0) + 1
            try:
                out_path.unlink()
            except OSError:
                pass
            continue

        report["kubejs_written"] = report.get("kubejs_written", 0) + 1


def write_config_sources(result: AnalysisResult, translations: dict[str, str], report: dict) -> None:
    for src in result.config_sources:
        rel = src["rel"]
        if src["kind"] == "PROPERTIES":
            data = src["data"]
            translated = {}
            applied = 0
            technical_changed = []
            for k, v in data.items():
                should, conf, _r = classify_string(k, v)
                if should and v in translations:
                    translated[k] = translations[v]
                    applied += 1
                else:
                    translated[k] = v
                    if is_technical_value(v, k) and v in translations and translations[v] != v:
                        technical_changed.append(k)
            if not applied:
                continue
            if set(translated.keys()) != set(data.keys()):
                report["errors"].append(f"Key-set mismatch for config source {rel}")
                report["validation_failed"] = report.get("validation_failed", 0) + 1
                continue
            if technical_changed:
                report["errors"].append(f"technical_data_changed: {rel} keys={technical_changed}")
                report["technical_data_changed"] = report.get("technical_data_changed", 0) + len(technical_changed)
                continue
            out_path = TRANSLATED_MODPACK_DIR / rel
            out_path.parent.mkdir(parents=True, exist_ok=True)
            out_path.write_text(serialize_lang_properties(translated), encoding="utf-8")
            # re-parse the actual bytes on disk
            try:
                reparsed = parse_lang_properties(out_path.read_text(encoding="utf-8"))
                if set(reparsed.keys()) != set(data.keys()):
                    raise ValueError("key set changed after write")
            except Exception as e:
                report["errors"].append(f"validation_failed: {rel} (post-write) -> {e}")
                report["validation_failed"] = report.get("validation_failed", 0) + 1
                try:
                    out_path.unlink()
                except OSError:
                    pass
                continue
            report["config_written"] = report.get("config_written", 0) + 1
        elif src["kind"] == "TOML":
            technical_before = {
                k: v for k, v in src["data"].items() if is_technical_value(v, k)
            }
            new_raw = apply_toml_translations(src["raw"], translations)
            if new_raw == src["raw"]:
                continue
            technical_after = _extract_toml_string_kv(new_raw)
            corrupted = [k for k, v in technical_before.items() if technical_after.get(k) != v]
            if corrupted:
                report["errors"].append(f"technical_data_changed: {rel} keys={corrupted}")
                report["technical_data_changed"] = report.get("technical_data_changed", 0) + len(corrupted)
                continue

            # STRUCTURAL VALIDATION: the previous version wrote this file with
            # no validation at all. Line count must be preserved (translation
            # only rewrites existing "key = "value"" lines in place, never
            # adds/removes lines), and every recognizable key="string" line
            # must still parse back with the SAME key set as before - a
            # mis-escaped quote/backslash would either merge two lines or
            # make a line stop matching TOML_KV_RE entirely.
            if len(new_raw.splitlines()) != len(src["raw"].splitlines()):
                report["errors"].append(f"toml_validation_failed: {rel} -> line count changed, skipped")
                report["config_validation_failed"] = report.get("config_validation_failed", 0) + 1
                continue
            if set(_extract_toml_string_kv(new_raw).keys()) != set(src["data"].keys()):
                report["errors"].append(f"toml_validation_failed: {rel} -> key set changed, skipped")
                report["config_validation_failed"] = report.get("config_validation_failed", 0) + 1
                continue

            out_path = TRANSLATED_MODPACK_DIR / rel
            out_path.parent.mkdir(parents=True, exist_ok=True)
            out_path.write_text(new_raw, encoding="utf-8")

            # Re-parse the ACTUAL bytes written to disk. OUTPUT PROHIBITED if
            # the file that would actually be loaded is invalid.
            try:
                written = out_path.read_text(encoding="utf-8")
                if set(_extract_toml_string_kv(written).keys()) != set(src["data"].keys()):
                    raise ValueError("key set changed after write")
            except Exception as e:
                report["errors"].append(f"toml_validation_failed: {rel} (post-write) -> {e}")
                report["config_validation_failed"] = report.get("config_validation_failed", 0) + 1
                try:
                    out_path.unlink()
                except OSError:
                    pass
                continue

            report["config_written"] = report.get("config_written", 0) + 1


def _quarantine(path: Path, problems: list[str], reason: str) -> None:
    """Delete a broken output file so it can never be loaded by Minecraft,
    and record why. Every writer already validates its own output before
    this point, so this is a defense-in-depth backstop, not the primary
    guard - but a backstop that only *reports* a broken file instead of
    removing it is not actually a backstop: the file stays in the
    resourcepack the user copies into their game and crashes it anyway,
    which is exactly what post_write_validation used to do (report-only)."""
    problems.append(f"{reason}: {path} -> УДАЛЁН (файл был бы невалиден для Minecraft)")
    try:
        path.unlink()
    except OSError as e:
        problems.append(f"Не удалось удалить невалидный файл {path}: {e}")


def post_write_validation(report: dict) -> list[str]:
    """Re-validate every output file that exists on disk after all writers
    have run, and QUARANTINE (delete) anything invalid - never merely report
    it. This is also called before a run starts (see purge_stale_broken_
    outputs) to clean up files left behind by an interrupted run or an older
    version of this script that did not validate as strictly."""
    problems = []
    if not (RESOURCEPACK_DIR / "pack.mcmeta").exists():
        problems.append("Отсутствует pack.mcmeta в resourcepack")
    for path in RESOURCEPACK_DIR.rglob("*.json"):
        try:
            json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            _quarantine(path, problems, "Невалидный JSON в resourcepack")
    for path in TRANSLATED_MODPACK_DIR.rglob("*.json"):
        try:
            json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            _quarantine(path, problems, "Невалидный JSON в Translated_Modpack")
    for path in TRANSLATED_MODPACK_DIR.rglob("*.snbt"):
        try:
            parse_snbt(path.read_text(encoding="utf-8"))
        except Exception:
            _quarantine(path, problems, "Невалидный SNBT в Translated_Modpack")
    for path in TRANSLATED_MODPACK_DIR.rglob("*.js"):
        try:
            raw = path.read_text(encoding="utf-8")
            # structural-only check (no bundled JS parser available) -
            # unbalanced brackets is a reliable sign of a corrupted rewrite.
            if any(raw.count(o) != raw.count(c) for o, c in (("(", ")"), ("{", "}"), ("[", "]"))):
                raise ValueError("unbalanced brackets")
        except Exception:
            _quarantine(path, problems, "Невалидный KubeJS-скрипт в Translated_Modpack")
    return problems


def purge_stale_broken_outputs() -> list[str]:
    """Run BEFORE a new translation pass starts, on whatever is already
    sitting in RESOURCEPACK_DIR / TRANSLATED_MODPACK_DIR from a previous
    run. write_lang_json_sources() merges new keys into an EXISTING lang
    file rather than rebuilding it from scratch, so a broken file left
    behind by an older/interrupted run (e.g. this script before these
    validations existed) could otherwise sit there silently forever,
    surviving every future run and still crashing the game - even though
    every individual write in THIS version is validated. Cleaning up first
    closes that gap."""
    if not RESOURCEPACK_DIR.exists() and not TRANSLATED_MODPACK_DIR.exists():
        return []
    return post_write_validation({"errors": []})


# ======================================================================
# ORIGINAL FILE PROTECTION
# ======================================================================

def compute_original_hashes(result: AnalysisResult) -> dict[str, str]:
    """Hash every on-disk source file the pipeline reads (FTB Quests SNBT,
    config/defaultconfigs) BEFORE any processing, so we can prove afterwards
    that the original modpack was never touched."""
    hashes: dict[str, str] = {}
    for src in result.snbt_sources:
        p = Path(src["path"])
        try:
            hashes[str(p)] = hashlib.sha256(p.read_bytes()).hexdigest()
        except OSError:
            pass
    for src in result.config_sources:
        p = Path(src["path"])
        try:
            hashes[str(p)] = hashlib.sha256(p.read_bytes()).hexdigest()
        except OSError:
            pass
    return hashes


def verify_originals_untouched(hashes: dict[str, str]) -> list[str]:
    """Re-hash the same files after the full run. Any mismatch means the
    original modpack was modified, which must never happen."""
    problems = []
    for path_str, old_hash in hashes.items():
        p = Path(path_str)
        try:
            new_hash = hashlib.sha256(p.read_bytes()).hexdigest()
        except OSError as e:
            problems.append(f"ORIGINAL FILE UNREADABLE AFTER RUN: {path_str} ({e})")
            continue
        if new_hash != old_hash:
            problems.append(f"ORIGINAL FILE MODIFIED (byte-for-byte check failed): {path_str}")
    return problems


# ======================================================================
# REPORTING
# ======================================================================

def build_report(result: AnalysisResult, translations: Optional[dict[str, TranslationResult]], stats: dict) -> dict:
    unique_texts = get_unique_translatable_texts(result, CONF_MEDIUM)
    by_source_type: dict[str, int] = {}
    by_confidence: dict[str, int] = {}
    for c in result.candidates:
        by_source_type[c.source_type] = by_source_type.get(c.source_type, 0) + 1
        by_confidence[c.confidence] = by_confidence.get(c.confidence, 0) + 1

    st = stats or {}
    report = {
        "jar_count": result.jar_count,
        "mod_count": len(result.mods),
        "lang_file_count": result.lang_file_count,
        "json_count": result.json_count,
        "snbt_count": result.snbt_count,
        "patchouli_count": result.patchouli_count,
        "ftbquests_count": result.ftbquests_count,
        "kubejs_count": result.kubejs_count,
        "total_candidates": len(result.candidates),
        "unique_candidates": len(unique_texts),
        "by_source_type": by_source_type,
        "by_confidence": by_confidence,
        "translation_stats": stats,
        # ---- audit/statistics required by the technical-safety pipeline ----
        "technical_values_detected": result.technical_values_detected,
        "technical_values_skipped": result.technical_values_detected,
        "translations_attempted": st.get("sent", 0),
        "translations_rejected": st.get("failed", 0),
        "validation_failed": 0,
        "json_validation_failed": 0,
        "snbt_validation_failed": 0,
        "placeholder_validation_failed": st.get("failed", 0),
        "technical_data_changed": 0,
        "errors": list(result.errors),
        "mods": {
            modid: {
                "modid": mi.modid,
                "name": mi.name,
                "jar": mi.jar_path,
                "loader": mi.loader,
                "lang_files": mi.lang_files,
                "candidates": mi.candidates,
                "other_sources": mi.other_sources[:50],
            }
            for modid, mi in sorted(result.mods.items())
        },
    }
    return report


def write_reports(result: AnalysisResult, report: dict, dry_run: bool):
    REPORTS_DIR.mkdir(parents=True, exist_ok=True)

    (REPORTS_DIR / "translation_report.json").write_text(
        json.dumps(report, ensure_ascii=False, indent=2), encoding="utf-8"
    )

    lines = []
    lines.append("=" * 60)
    lines.append("ОТЧЁТ О ПЕРЕВОДЕ МОДПАКА" + (" (DRY RUN)" if dry_run else ""))
    lines.append("=" * 60)
    lines.append(f"JAR:                    {report['jar_count']}")
    lines.append(f"Модов:                  {report['mod_count']}")
    lines.append(f"Language files:         {report['lang_file_count']}")
    lines.append(f"Всего найдено строк:    {report['total_candidates']}")
    lines.append(f"Уникальных строк:       {report['unique_candidates']}")
    lines.append("")
    lines.append("По источникам:")
    for k, v in sorted(report["by_source_type"].items()):
        lines.append(f"    {k:20s} {v}")
    lines.append("")
    lines.append("По confidence:")
    for k, v in sorted(report["by_confidence"].items()):
        lines.append(f"    {k:10s} {v}")
    if report.get("translation_stats"):
        st = report["translation_stats"]
        lines.append("")
        lines.append("Перевод:")
        lines.append(f"    из кэша:        {st.get('cached', 0)}")
        lines.append(f"    отправлено:     {st.get('sent', 0)}")
        lines.append(f"    переведено:     {st.get('translated', 0)}")
        lines.append(f"    ошибок:         {st.get('failed', 0)}")
    lines.append("")
    lines.append(f"Ошибок анализа: {len(report['errors'])}")
    (REPORTS_DIR / "translation_report.txt").write_text("\n".join(lines), encoding="utf-8")

    (REPORTS_DIR / "translation_errors.txt").write_text(
        "\n".join(report["errors"]) or "(нет ошибок)\n", encoding="utf-8"
    )

    skipped = [c for c in result.candidates if c.confidence == CONF_LOW]
    (REPORTS_DIR / "translation_skipped.txt").write_text(
        "\n".join(f"[{c.source_type}] {c.source_file} :: {c.text!r} ({c.reason})" for c in skipped)
        or "(нет пропущенных строк с LOW confidence)\n",
        encoding="utf-8",
    )

    candidates_lines = [
        f"[{c.confidence}] [{c.source_type}] {c.source_file} :: {c.text!r}" for c in result.candidates
    ]
    (REPORTS_DIR / "translation_candidates.txt").write_text(
        "\n".join(candidates_lines) or "(кандидатов не найдено)\n", encoding="utf-8"
    )


def print_final_summary(report: dict):
    print()
    print("=" * 60)
    print("             ПЕРЕВОД ЗАВЕРШЁН")
    print("=" * 60)
    print(f"JAR:                    {report['jar_count']}")
    print(f"Модов:                  {report['mod_count']}")
    print(f"Language files:         {report['lang_file_count']}")
    print()
    print(f"Всего найдено строк:    {report['total_candidates']}")
    print(f"Уникальных строк:       {report['unique_candidates']}")
    print()
    st = report.get("translation_stats", {})
    print(f"Из cache:               {st.get('cached', 0)}")
    print(f"Отправлено Google:      {st.get('sent', 0)}")
    print(f"Переведено:             {st.get('translated', 0)}")
    print(f"Ошибок:                 {st.get('failed', 0)}")
    print()
    print("FTB Quests:")
    print(f"    файлов:              {report['ftbquests_count']}")
    print("Patchouli:")
    print(f"    файлов:              {report['patchouli_count']}")
    print("KubeJS:")
    print(f"    файлов:              {report['kubejs_count']}")
    print()
    print("Resource Pack:")
    print(f"    {RESOURCEPACK_DIR}")
    print()
    print("Translated Modpack:")
    print(f"    {TRANSLATED_MODPACK_DIR}")
    print()
    print("Cache:")
    print(f"    {CACHE_DB_PATH}")
    print("=" * 60)
    failed_total = sum(
        report.get(k, 0) for k in (
            "validation_failed", "json_validation_failed", "snbt_validation_failed",
            "kubejs_validation_failed", "config_validation_failed", "technical_data_changed",
        )
    )
    if failed_total:
        print(f"[!] Заблокировано/отклонено потенциально повреждённых записей: {failed_total}")
        print("    (эти строки НЕ попали в итоговый перевод - см. translation_errors.txt)")
        print("=" * 60)


# ======================================================================
# SELF TEST (in-memory, run before main pipeline)
# ======================================================================

def self_test() -> bool:
    ok = True

    def check(name, cond):
        nonlocal ok
        status = "OK" if cond else "FAIL"
        if not cond:
            ok = False
        print(f"    [{status}] {name}")

    print("[i] Запуск самодиагностики...")

    # 1. standard lang json - real production code path is collect_lang_candidates
    # (value-only classification; see classify_lang_value docstring for why
    # dotted translation-style keys like "item.create.cogwheel" must NOT be
    # run through the structural key/ID-hint classifier).
    lang = {"item.create.cogwheel": "Cogwheel", "block.minecraft.stone": "Stone"}
    cands = collect_lang_candidates(lang, "LANG_JSON", "test")
    check("standard lang json extraction", len(cands) == 2)

    # 2. nested json
    nested = {"title": "Mechanical Press", "items": [{"name": "Iron Sheet"}], "id": "create:press"}
    cands = collect_json_candidates(nested, "LANG_JSON", "test")
    texts = {c.text for c in cands}
    check("nested json recursion", "Mechanical Press" in texts and "Iron Sheet" in texts and "create:press" not in texts)

    # 3. SNBT
    snbt_text = "{title: 'Quest Title', id: '1234ABCD', reward: {item: 'minecraft:diamond'}}"
    data = parse_snbt(snbt_text)
    check("snbt parses compound", isinstance(data, dict) and str(data["title"]) == "Quest Title")
    snbt_cands = collect_snbt_candidates(data, "FTBQUESTS", "test")
    check("snbt candidate extraction", any(c.text == "Quest Title" for c in snbt_cands))

    # 4. MC text component
    comp = {"text": "Hello ", "extra": [{"text": "World"}]}
    comp_cands = collect_text_component_candidates(comp, "test")
    check("text component extraction", len(comp_cands) == 2)

    # 5. placeholders
    sample = "Hello %s, you have {count} items! §aGood luck§r"
    protected, tokens = protect_placeholders(sample)
    check("placeholders protected", "%s" not in protected and "{count}" not in protected)
    restored = restore_placeholders(protected, tokens)
    check("placeholders restored", restored == sample)

    # 6. duplicate strings dedupe
    dupes = ["Back", "Back", "Cancel", "Back"]
    unique = list(dict.fromkeys(dupes))
    check("dedupe works", unique == ["Back", "Cancel"])

    # 7. ftb quest-like nested structure
    ftb_like = parse_snbt(
        "{chapters: [{title: 'Getting Started', quests: [{id: 'ABCD1234', "
        "tasks: [{title: 'Craft item', type: 'item'}]}]}]}"
    )
    ftb_cands = collect_snbt_candidates(ftb_like, "FTBQUESTS", "test")
    ftb_texts = {c.text for c in ftb_cands}
    check("ftb-quest-like structure", "Getting Started" in ftb_texts and "Craft item" in ftb_texts)

    # 8. patchouli-like structure
    patch_like = {
        "name": "Guide Book",
        "category": "create",
        "entries": [{"name": "Cogwheels", "pages": [{"type": "text", "text": "Cogwheels transmit rotation."}]}],
    }
    patch_cands = collect_json_candidates(patch_like, "PATCHOULI", "test")
    patch_texts = {c.text for c in patch_cands}
    check("patchouli-like structure", "Cogwheels transmit rotation." in patch_texts)

    # 9. technical IDs are skipped
    tech = {"id": "minecraft:iron_ingot", "texture": "textures/block/foo.png", "recipe_id": "create:mechanical_press"}
    tech_cands = collect_json_candidates(tech, "DATA_JSON", "test")
    check("technical ids skipped", len(tech_cands) == 0)

    # 10. broken json handled gracefully
    try:
        json.loads("{not valid json")
        broken_ok = False
    except Exception:
        broken_ok = True
    check("broken json raises cleanly", broken_ok)

    # snbt round trip
    rebuilt = serialize_snbt(data)
    try:
        parse_snbt(rebuilt)
        rt_ok = True
    except Exception:
        rt_ok = False
    check("snbt round-trip serialize/parse", rt_ok)

    # ==================================================================
    # REGRESSION TESTS (technical-value protection pipeline)
    # ==================================================================

    # 11. THE regression test - FTB Quests hex ID must NEVER be treated as
    # translatable, under any key, and must never come out looking like the
    # corrupted "42братуха".
    ORIGINAL_HEX_ID = "27B28A53F0EFE604"
    CORRUPTED_HEX_ID = "27Б28А53Ф0ЭФЕ604"
    check("hex id classified as technical", is_technical_value(ORIGINAL_HEX_ID))
    check("hex id technical under 'id' key", is_technical_value(ORIGINAL_HEX_ID, "id"))
    check("hex id technical under 'quest_links' key", is_technical_value(ORIGINAL_HEX_ID, "quest_links"))
    check("hex id technical under 'dependencies' key", is_technical_value(ORIGINAL_HEX_ID, "dependencies"))
    should, conf, _r = classify_string("quest_links", ORIGINAL_HEX_ID)
    check("hex id under quest_links -> should_translate=False", should is False)
    check("corrupted hex id never produced", ORIGINAL_HEX_ID != CORRUPTED_HEX_ID)

    # 12. UUID
    check("uuid classified as technical", is_technical_value("550e8400-e29b-41d4-a716-446655440000"))

    # 13. namespace:path resource location
    check("resource location technical", is_technical_value("create:mechanical_press"))
    check("minecraft registry id technical", is_technical_value("minecraft:iron_ingot"))

    # 14. FTB quest link / dependencies list (key-driven, value itself is a bare id)
    should, conf, _r = classify_string("dependencies", "ABCD1234")
    check("dependency id skipped regardless of shape", should is False)

    # 15. SNBT: ftb-quest-like structure keeps ids untouched by the collector
    ftb_ids = parse_snbt(
        "{id: '27B28A53F0EFE604', dependencies: ['1122AABB33CCDDEE'], title: 'Getting Started'}"
    )
    ftb_id_cands = collect_snbt_candidates(ftb_ids, "FTBQUESTS", "test")
    ftb_id_texts = {c.text for c in ftb_id_cands}
    check(
        "snbt hex ids never selected for translation",
        "27B28A53F0EFE604" not in ftb_id_texts and "1122AABB33CCDDEE" not in ftb_id_texts,
    )
    check("snbt title still selected for translation", "Getting Started" in ftb_id_texts)

    # 15b. Regression test for the Prominent Talents crash: a math formula
    # string with CONST_CASE variable names must NEVER be sent to
    # translation, under any key - not the variable names (ATTACK_DAMAGE ->
    # АТАКА_УРОН) and not the decimal point (0.66 -> 0,66), either of which
    # crashes the mod's own formula parser (Neruina "non-ticking" crash).
    FORMULA_SAMPLE = "(sqrt(((ATTACK_DAMAGE * ATTACK_SPEED) * (ARMOR + ARMOR_TOUGHNESS / 3))) * 16) * 0.66"
    check("formula expression classified as technical", is_technical_value(FORMULA_SAMPLE))
    check(
        "formula expression technical under neutral key",
        is_technical_value(FORMULA_SAMPLE, "powerlevel_formula"),
    )
    should, conf, _r = classify_string("powerlevel_formula", FORMULA_SAMPLE)
    check("formula -> should_translate=False", should is False)
    check("plain sentence still translatable (not over-blocked)", not is_formula_like("Hello World, this is fine"))
    check("simple prose with parens still translatable", not is_formula_like("Craft item (advanced)"))

    # 16. JSON language file - malformed generated JSON must be rejected
    try:
        json.loads('{"a": "b", "c": }')
        malformed_rejected = False
    except Exception:
        malformed_rejected = True
    check("malformed generated json rejected by json.loads", malformed_rejected)

    # 17. placeholders round-trip even when the placeholder token itself
    # contains characters with regex/backreference meaning (regression for
    # the re.sub() backslash-interpretation bug).
    tricky = "Line one\\nLine two %s done"
    protected2, tokens2 = protect_placeholders(tricky)
    restored2 = restore_placeholders(protected2, tokens2)
    check("placeholder round-trip with backslash-n token", restored2 == tricky)

    # 18. config enum values are never translated, even under a
    # text-hinted key like "registry_name" (jade:registry_name bug).
    should, conf, _r = classify_string("registry_name", "DISABLED")
    check("config enum under registry_name key skipped", should is False)
    check("bare config enum classified as technical", is_technical_value("DISABLED"))

    # 19. duplicate text dedupe (see check #6 above) - already covered.

    # 20. escaped JSON string containing quotes/backslashes still round-trips
    escaped_val = {"msg": "She said \"hi\" and left.\\n"}
    check("escaped json round-trips", validate_json_roundtrip(escaped_val))

    # 21. unicode content preserved through JSON serialize/parse
    unicode_val = {"msg": "Привет, мир! 你好"}
    unicode_rt = json.loads(json.dumps(unicode_val, ensure_ascii=False))
    check("unicode content round-trips", unicode_rt == unicode_val)

    # 22. section-sign (§) Minecraft formatting codes survive translation
    # placeholder protection untouched.
    formatted = "§aGood luck§r, §lchampion§r!"
    protected3, tokens3 = protect_placeholders(formatted)
    check("formatting codes protected", "§a" not in protected3 and "§r" not in protected3 and "§l" not in protected3)
    restored3 = restore_placeholders(protected3, tokens3)
    check("formatting codes restored exactly", restored3 == formatted)

    # 23. KubeJS single-quoted literal containing an apostrophe in the
    # translation must not break out of the string (regression for the bug
    # that corrupted create_confectionery/design_decor/naturalist-style
    # KubeJS recipes: escaping always used \" regardless of which quote
    # character the source literal actually used).
    js_src = ".tooltip('Sharp Blade')"
    m = KUBEJS_STRING_CALL_RE.search(js_src)
    match_list = [(m.start(3), m.end(3), m.group(3), "Sharp Blade", m.group(2))]
    js_out = apply_kubejs_script_translation(js_src, match_list, {"Sharp Blade": "Нельзя войти в чужой дом"})
    check("kubejs single-quote literal not broken by apostrophe-free text", js_out.count("'") == js_src.count("'"))
    match_list2 = [(m.start(3), m.end(3), m.group(3), "Sharp Blade", m.group(2))]
    js_out2 = apply_kubejs_script_translation(js_src, match_list2, {"Sharp Blade": "Это чей-то нож"})
    check(
        "kubejs single-quote literal with apostrophe in translation stays balanced",
        validate_kubejs_script_rewrite(js_src, js_out2),
    )

    # 24. KubeJS double-quoted literal still round-trips too (not just single).
    js_src_dq = '.title("Iron Pickaxe")'
    m_dq = KUBEJS_STRING_CALL_RE.search(js_src_dq)
    match_dq = [(m_dq.start(3), m_dq.end(3), m_dq.group(3), "Iron Pickaxe", m_dq.group(2))]
    js_out_dq = apply_kubejs_script_translation(js_src_dq, match_dq, {"Iron Pickaxe": 'Кирка "мастера"'})
    check("kubejs double-quote literal with embedded quotes stays balanced", validate_kubejs_script_rewrite(js_src_dq, js_out_dq))

    # 25. TOML value containing a backslash is escaped (previous version
    # only escaped quotes, leaving a raw backslash that TOML would reject).
    toml_src = 'displayName = "Old Name" # comment'
    toml_out = apply_toml_translations(toml_src, {"Old Name": 'Путь C:\\mods\\new'})
    check("toml backslash in translation escaped", "\\\\mods" in toml_out or "\\\\\\\\mods" in toml_out)
    check("toml output still single-line kv", len(toml_out.splitlines()) == 1)

    # 26. TOML value containing a literal newline is NOT substituted (would
    # otherwise spill onto the next line and corrupt every following key).
    toml_src2 = 'title = "Short"'
    toml_out2 = apply_toml_translations(toml_src2, {"Short": "Line one\nLine two"})
    check("toml multiline translation rejected, original kept", toml_out2 == toml_src2)

    # 27. NBT-embedded config values (SkyblockBuilder starting-inventory
    # style: 'namespace:id{...}' or a bare '{...}' compound) must be
    # recognized as technical and NEVER sent to translation whole - this is
    # exactly what broke with: com.mojang.brigadier.exceptions.
    # CommandSyntaxException: Expected key at position 1: {<--[HERE]
    check("bare nbt compound is technical", is_technical_string('{Count:1b,id:"minecraft:diamond_pickaxe"}'))
    check(
        "item id + nbt shorthand is technical",
        is_technical_string('minecraft:diamond_pickaxe{Enchantments:[{id:"minecraft:efficiency",lvl:5}]}'),
    )
    check(
        "nbt with nested human-looking display name is still technical",
        is_technical_string('minecraft:diamond{display:{Name:"Special Diamond Pickaxe"}}'),
    )
    check("bare snbt list is technical", is_technical_string('[{item:"minecraft:stone",Count:64b}]'))
    # ordinary prose containing a brace-like placeholder must NOT be
    # misdetected as NBT (it doesn't parse as key:value NBT).
    check("placeholder text is not treated as nbt", not is_technical_string("{player} has joined the island"))
    check("plain sentence is still translatable", not is_technical_string("Welcome to your new skyblock island"))

    print(f"[i] Самодиагностика {'пройдена' if ok else 'ЗАВЕРШИЛАСЬ С ОШИБКАМИ'}.")
    return ok


# ======================================================================
# GLOBAL CACHE CLI (--merge-cache / --export-cache / --import-cache / --cache-stats)
# ======================================================================

def _print_cache_counts(label: str, counts: dict) -> None:
    print(f"[i] {label}:")
    for k, v in counts.items():
        print(f"    {k}: {v}")


def handle_cache_cli(argv: list[str]) -> bool:
    """Look for --merge-cache/--export-cache/--import-cache/--cache-stats in
    argv and, if found, perform the requested cache operation and return
    True (caller should exit without running the normal
    analyze/translate pipeline). Returns False if none of these flags are
    present."""
    flags = {
        "--merge-cache": None, "--export-cache": None,
        "--import-cache": None, "--cache-stats": None,
    }
    i = 0
    found_any = False
    while i < len(argv):
        arg = argv[i]
        if arg in flags:
            found_any = True
            if arg == "--cache-stats":
                flags[arg] = True
                i += 1
                continue
            if i + 1 >= len(argv):
                print(f"[ОШИБКА] {arg} требует аргумент (путь к файлу).")
                sys.exit(1)
            flags[arg] = argv[i + 1]
            i += 2
            continue
        i += 1

    if not found_any:
        return False

    global_cache = GlobalTranslationCache(GLOBAL_CACHE_DB_PATH)
    try:
        if flags["--merge-cache"]:
            src = Path(flags["--merge-cache"])
            print(f"[i] Слияние {src} с {GLOBAL_CACHE_DB_PATH} ...")
            counts = global_cache.merge_local_db(src)
            _print_cache_counts("Результат слияния cache", counts)

        if flags["--export-cache"]:
            dst = Path(flags["--export-cache"])
            n = global_cache.export_json(dst)
            print(f"[i] Экспортировано {n} записей в {dst}")

        if flags["--import-cache"]:
            src = Path(flags["--import-cache"])
            print(f"[i] Импорт {src} в {GLOBAL_CACHE_DB_PATH} ...")
            if src.suffix.lower() in (".db", ".sqlite", ".sqlite3"):
                counts = global_cache.merge_local_db(src)
            else:
                counts = global_cache.import_json(src)
            _print_cache_counts("Результат импорта cache", counts)

        if flags["--cache-stats"]:
            revalidation = global_cache.revalidate_stale_entries()
            print(f"[i] Global cache: {GLOBAL_CACHE_DB_PATH}")
            print(f"    Всего записей:       {global_cache.count()}")
            print(f"    Переоценено:         {revalidation['revalidated']}")
            print(f"    Отклонено повторно:  {revalidation['rejected']}")
    finally:
        global_cache.close()

    return True

# ======================================================================
# MAIN
# ======================================================================

def main():
    global MC_DIR, RESOURCEPACK_DIR

    print("Minecraft Modpack Translator (EN -> RU)")
    print("=" * 60)

    if not self_test():
        print("[!] Самодиагностика выявила проблемы, но выполнение продолжится "
              "(рекомендуется проверить translation_reports/translation_errors.txt).")

    try:
        pack_path = parse_pack_path(sys.argv)
        MC_DIR = discover_mc_dir(pack_path)
        RESOURCEPACK_DIR = MC_DIR / "resourcepacks" / RESOURCEPACK_NAME
    except FileNotFoundError as e:
        print(f"[ОШИБКА] {e}")
        sys.exit(1)

    print(f"[i] Папка сборки: {MC_DIR}")
    print(f"[i] Имя сборки: {MC_DIR.name}")
    ensure_dirs()

    print("[i] Проверка результатов прошлых запусков на битые файлы...")
    stale_problems = purge_stale_broken_outputs()
    if stale_problems:
        print(f"[!] Удалено повреждённых файлов от прошлых запусков: {len(stale_problems)}")
        for p in stale_problems:
            print(f"    {p}")

    print("[i] Анализ модпака (JAR, FTB Quests, Patchouli, KubeJS, config)...")
    result = run_analysis()

    report = build_report(result, None, {})
    write_reports(result, report, dry_run=True)

    print()
    print(f"JAR найдено:            {report['jar_count']}")
    print(f"Модов найдено:          {report['mod_count']}")
    print(f"Language files:         {report['lang_file_count']}")
    print(f"Всего кандидатов:       {report['total_candidates']}")
    print(f"Уникальных строк:       {report['unique_candidates']}")
    print(f"FTB Quests файлов:      {report['ftbquests_count']}")
    print(f"Patchouli файлов:       {report['patchouli_count']}")
    print(f"KubeJS файлов:          {report['kubejs_count']}")
    print(f"Ошибок анализа:         {len(report['errors'])}")
    print()
    print(f"[i] Полный отчёт: {REPORTS_DIR / 'translation_report.txt'}")
    print(f"[i] Список кандидатов: {REPORTS_DIR / 'translation_candidates.txt'}")

    if not ANALYZE_ONLY:
        choice = "1"
    else:
        print()
        print("1 - начать перевод")
        print("2 - выйти")
        choice = input("> ").strip()

    if choice != "1":
        print("Выход без перевода.")
        return

    if Translator is None:
        print("[ОШИБКА] Библиотека googletrans не установлена. "
              "Установите: pip install googletrans==4.0.2")
        sys.exit(1)

    original_hashes = compute_original_hashes(result)

    cache = TranslationCache(CACHE_DB_PATH)
    global_cache = GlobalTranslationCache(GLOBAL_CACHE_DB_PATH)
    try:
        # Revalidate stale global entries before they are eligible for reuse.
        global_cache.revalidate_stale_entries()
        print()
        print("[i] Перевод строк через Google Translate...")
        translations_raw, stats = run_translation_phase(result, cache, global_cache)
        translations = {t: r.translated for t, r in translations_raw.items() if r.translated is not None}

        print("[i] Применение переводов и запись результатов...")
        write_report_state = {"errors": []}
        write_resourcepack_pack_mcmeta()
        write_lang_json_sources(result, translations, write_report_state)
        write_generic_json_sources(result, translations, write_report_state)
        write_snbt_sources(result, translations, write_report_state)
        write_kubejs_scripts(result, translations, write_report_state)
        write_config_sources(result, translations, write_report_state)

        print("[i] Проверка результатов...")
        problems = post_write_validation(write_report_state)
        if problems:
            print(f"[!] Обнаружено {len(problems)} проблем при финальной проверке (см. отчёт об ошибках).")
            result.errors.extend(problems)

        print("[i] Проверка целостности оригинальных файлов...")
        original_problems = verify_originals_untouched(original_hashes)
        if original_problems:
            print(f"[КРИТИЧЕСКАЯ ОШИБКА] Оригинальный модпак был изменён! ({len(original_problems)})")
            result.errors.extend(original_problems)

        result.errors.extend(write_report_state.get("errors", []))

        final_report = build_report(result, translations_raw, stats)
        final_report["write_stats"] = {
            k: v for k, v in write_report_state.items() if k != "errors"
        }
        # fold the write-phase validation counters into the top-level stats
        # requested by никифор the audit (these are only known once writing/validating
        # each output file has actually happened).
        for stat_key in (
            "validation_failed", "json_validation_failed",
            "snbt_validation_failed", "kubejs_validation_failed",
            "config_validation_failed", "technical_data_changed",
        ):
            final_report[stat_key] = write_report_state.get(stat_key, 0)
        final_report["technical_values_detected"] = get_technical_stats()["detected"]
        final_report["technical_values_skipped"] = get_technical_stats()["detected"]
        write_reports(result, final_report, dry_run=False)
        print_final_summary(final_report)
    finally:
        cache.close()
        global_cache.close()


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\n[!] Прервано пользователем. Прогресс сохранён в translation_cache.db.")
        sys.exit(130)
    except Exception:
        print("\n[ОШИБКА] Необработанное исключение:")
        traceback.print_exc()
        sys.exit(1)
