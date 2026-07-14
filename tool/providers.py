# -*- coding: utf-8 -*-
"""
ZTLStudio: the LLM provider layer. The translator speaks in messages;
this module speaks HTTP to whichever backend the user chose. Two
families:

  * OpenAI-compatible (Groq, OpenAI, OpenRouter, DeepSeek, xAI, Together)
    — one chat/completions shape;
  * Anthropic (Claude) — its own messages endpoint and system field.

A weaker model mis-formalizes (the curator's crocodile: llama produced
imp(not(Tr(K)),Tr(C)) instead of the clean R:Tr(M), M:not(Tr(R))), so
the studio must let a stronger model in. Keys live in the environment
or in local untracked files tool/.<provider>_key (the repo is public —
never in code); the UI may also pass a key/model per request, which
wins over the stored one.
"""

import json
import os
import time
import urllib.error
import urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))

# name -> (family, url, default model, env var, key-file, label, key-console)
PROVIDERS = {
    "groq": ("openai", "https://api.groq.com/openai/v1/chat/completions",
             "llama-3.3-70b-versatile", "GROQ_API_KEY", ".groq_key",
             "Groq (free · weaker, may misformalize)",
             "https://console.groq.com/keys"),
    "anthropic": ("anthropic", "https://api.anthropic.com/v1/messages",
                  "claude-sonnet-5", "ANTHROPIC_API_KEY",
                  ".anthropic_key", "Anthropic (Claude)",
                  "https://console.anthropic.com/settings/keys"),
    "openai": ("openai", "https://api.openai.com/v1/chat/completions",
               "gpt-5", "OPENAI_API_KEY", ".openai_key", "OpenAI",
               "https://platform.openai.com/api-keys"),
    "openrouter": ("openai",
                   "https://openrouter.ai/api/v1/chat/completions",
                   "anthropic/claude-sonnet-4", "OPENROUTER_API_KEY",
                   ".openrouter_key", "OpenRouter (any model)",
                   "https://openrouter.ai/keys"),
    "deepseek": ("openai", "https://api.deepseek.com/v1/chat/completions",
                 "deepseek-reasoner", "DEEPSEEK_API_KEY", ".deepseek_key",
                 "DeepSeek", "https://platform.deepseek.com/api_keys"),
    "gemini": ("openai",
               "https://generativelanguage.googleapis.com/v1beta/openai/"
               "chat/completions",
               "gemini-2.5-pro", "GEMINI_API_KEY", ".gemini_key",
               "Google Gemini", "https://aistudio.google.com/apikey"),
    "xai": ("openai", "https://api.x.ai/v1/chat/completions",
            "grok-4", "XAI_API_KEY", ".xai_key", "xAI (Grok)",
            "https://console.x.ai"),
}

# FLAGSHIP models only (Sonnet-level or above) — weaker models mis-formalize.
# First = default. VERIFY IDS: only the Anthropic ids are known-current here;
# the others (gpt-5, o3, gemini-2.5-pro, grok-4, deepseek-reasoner) are best
# guesses at each provider's frontier — adjust if a call 404s.
MODELS = {
    "anthropic":  ["claude-sonnet-5", "claude-opus-4-8"],
    "openai":     ["gpt-5", "o3"],
    "gemini":     ["gemini-2.5-pro"],
    "xai":        ["grok-4"],
    "openrouter": ["anthropic/claude-sonnet-5", "anthropic/claude-opus-4-8",
                   "openai/gpt-5", "google/gemini-2.5-pro"],
    "deepseek":   ["deepseek-reasoner"],
    "groq":       ["llama-3.3-70b-versatile"],   # free, but weak — mis-formalizes
}


class ProviderError(Exception):
    pass


def get_key(provider):
    """Env var first, then the local untracked key file."""
    if provider not in PROVIDERS:
        return None
    env, keyfile = PROVIDERS[provider][3], PROVIDERS[provider][4]
    key = os.environ.get(env)
    if key:
        return key.strip()
    path = os.path.join(HERE, keyfile)
    if os.path.exists(path):
        with open(path) as f:
            return f.read().strip()
    return None


def available():
    """[{provider, label, default_model, has_key}] for the settings UI."""
    out = []
    for name, tup in PROVIDERS.items():
        out.append({"provider": name, "label": tup[5],
                    "default_model": tup[2], "has_key": bool(get_key(name)),
                    "console": tup[6],
                    "models": MODELS.get(name, [tup[2]])})
    return out


def _post(url, body, headers):
    for attempt in range(4):
        try:
            req = urllib.request.Request(url, data=json.dumps(body).encode(),
                                         headers=headers)
            with urllib.request.urlopen(req, timeout=90) as r:
                return json.loads(r.read().decode())
        except urllib.error.HTTPError as e:
            if e.code == 429 and attempt < 3:       # rate limit: breathe
                time.sleep(15 * (attempt + 1))
                continue
            detail = ""
            try:
                detail = e.read().decode()[:200]
            except Exception:
                pass
            if (e.code == 400 and "temperature" in detail.lower()
                    and "temperature" in body):
                body.pop("temperature", None)   # newer models deprecate it
                continue
            raise ProviderError(f"HTTP {e.code}: {detail or e.reason}")
        except Exception as e:
            raise ProviderError(str(e))


def chat(messages, provider="groq", model="", key="", temperature=0.2):
    """messages: [{role: system|user|assistant, content}]. Returns text."""
    if provider not in PROVIDERS:
        raise ProviderError(f"unknown provider: {provider}")
    family, url, default_model, label = (PROVIDERS[provider][0],
        PROVIDERS[provider][1], PROVIDERS[provider][2], PROVIDERS[provider][5])
    model = (model or "").strip() or default_model
    key = (key or "").strip() or get_key(provider)
    if not key:
        raise ProviderError(
            f"no key for {label}: set its env var, drop it into "
            f"tool/{PROVIDERS[provider][4]}, or enter it in Settings")

    if family == "anthropic":
        system = "\n\n".join(m["content"] for m in messages
                             if m["role"] == "system")
        conv = [{"role": m["role"], "content": m["content"]}
                for m in messages if m["role"] in ("user", "assistant")]
        body = {"model": model, "max_tokens": 1500,
                "temperature": temperature, "messages": conv}
        if system:
            body["system"] = system
        headers = {"x-api-key": key, "anthropic-version": "2023-06-01",
                   "content-type": "application/json",
                   "user-agent": "ZTLStudio/1.0"}
        data = _post(url, body, headers)
        parts = data.get("content", [])
        return "".join(p.get("text", "") for p in parts).strip()

    # OpenAI-compatible
    body = {"model": model, "messages": messages, "temperature": temperature}
    headers = {"Authorization": f"Bearer {key}",
               "Content-Type": "application/json",
               "User-Agent": "ZTLStudio/1.0"}
    if provider == "openrouter":
        headers["HTTP-Referer"] = "https://github.com/inventor1975/ZTL"
        headers["X-Title"] = "ZTLStudio"
    data = _post(url, body, headers)
    return data["choices"][0]["message"]["content"].strip()
