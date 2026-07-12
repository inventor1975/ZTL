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

# name -> (family, url, default model, env var, key-file basename, label)
PROVIDERS = {
    "groq": ("openai", "https://api.groq.com/openai/v1/chat/completions",
             "llama-3.3-70b-versatile", "GROQ_API_KEY", ".groq_key", "Groq"),
    "anthropic": ("anthropic", "https://api.anthropic.com/v1/messages",
                  "claude-haiku-4-5-20251001", "ANTHROPIC_API_KEY",
                  ".anthropic_key", "Anthropic (Claude)"),
    "openai": ("openai", "https://api.openai.com/v1/chat/completions",
               "gpt-4o", "OPENAI_API_KEY", ".openai_key", "OpenAI"),
    "openrouter": ("openai",
                   "https://openrouter.ai/api/v1/chat/completions",
                   "anthropic/claude-sonnet-4", "OPENROUTER_API_KEY",
                   ".openrouter_key", "OpenRouter (any model)"),
    "deepseek": ("openai", "https://api.deepseek.com/v1/chat/completions",
                 "deepseek-chat", "DEEPSEEK_API_KEY", ".deepseek_key",
                 "DeepSeek"),
}


class ProviderError(Exception):
    pass


def get_key(provider):
    """Env var first, then the local untracked key file."""
    if provider not in PROVIDERS:
        return None
    _, _, _, env, keyfile, _ = PROVIDERS[provider]
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
    for name, (_, _, model, _, _, label) in PROVIDERS.items():
        out.append({"provider": name, "label": label,
                    "default_model": model, "has_key": bool(get_key(name))})
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
            raise ProviderError(f"HTTP {e.code}: {detail or e.reason}")
        except Exception as e:
            raise ProviderError(str(e))


def chat(messages, provider="groq", model="", key="", temperature=0.2):
    """messages: [{role: system|user|assistant, content}]. Returns text."""
    if provider not in PROVIDERS:
        raise ProviderError(f"unknown provider: {provider}")
    family, url, default_model, _, _, label = PROVIDERS[provider]
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
