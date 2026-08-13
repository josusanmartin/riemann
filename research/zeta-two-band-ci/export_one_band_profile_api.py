#!/usr/bin/env python3
"""Append stable public aliases to the generated one-band sharp-profile file.

The large profile proof was produced mechanically and its internal declaration
names are not part of the intended API.  This script discovers the concrete
profile function and the strongest theorem whose header constructs a
`ProfileStep`, then appends stable aliases in the same Lean source file.  Being
in the same file also allows a private generated declaration to be exported
without trusting textual names outside the generator.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path


def declaration_headers(text: str):
    pattern = re.compile(
        r"(?m)^(?:private\s+)?(?:theorem|lemma|def|abbrev)\s+([A-Za-z0-9_']+)"
    )
    matches = list(pattern.finditer(text))
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        yield match.group(1), text[match.start():end]


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: export_one_band_profile_api.py <OneBandSharpProfile.lean>")

    path = Path(sys.argv[1])
    text = path.read_text(encoding="utf-8")
    headers = list(declaration_headers(text))

    step_candidates = [
        (name, block)
        for name, block in headers
        if "ProfileStep" in block and ("theorem " in block or "lemma " in block)
    ]
    if not step_candidates:
        raise RuntimeError("no ProfileStep theorem found in generated profile source")

    # Prefer the last theorem: generated files place the assembled certificate
    # after all of its interval lemmas.
    step_name, step_block = step_candidates[-1]

    profile_identifiers = re.findall(
        r"\b([A-Za-z_][A-Za-z0-9_'.]*(?:profile|Profile)[A-Za-z0-9_']*)\b",
        step_block,
    )
    profile_identifiers = [
        name for name in profile_identifiers
        if not name.endswith("ProfileStep") and name != "ProfileStep"
    ]
    if not profile_identifiers:
        # Fall back to the most frequently used profile-like definition in the
        # entire generated source.
        all_profiles = []
        for name, block in headers:
            if "profile" in name.lower() and (block.startswith("def ") or " def " in block):
                all_profiles.append(name)
        if not all_profiles:
            raise RuntimeError("no sharp-profile definition found")
        profile_name = all_profiles[-1]
    else:
        profile_name = max(
            set(profile_identifiers),
            key=profile_identifiers.count,
        ).split(".")[-1]

    marker = "-- stable-api-export: one-band-sharp-profile"
    if marker in text:
        return

    # Recover the innermost namespace opened by the generated source.  In the
    # current file this is `Zeta23.GapMatching.OneBandSharpProfile`.
    namespaces = re.findall(r"(?m)^namespace\s+([A-Za-z0-9_.']+)\s*$", text)
    namespace = namespaces[-1] if namespaces else "Zeta23.GapMatching.OneBandSharpProfile"

    appendix = f"""

{marker}
namespace {namespace}

/-- Stable public alias for the generated sharp overlap profile. -/
abbrev exportedSharpProfile := {profile_name}

/-- Stable public alias for the assembled one-band profile-step certificate. -/
abbrev exportedProfileStepCertificate := @{step_name}

end {namespace}
"""
    path.write_text(text + appendix, encoding="utf-8")
    print(f"exported profile={profile_name}, certificate={step_name}")


if __name__ == "__main__":
    main()
