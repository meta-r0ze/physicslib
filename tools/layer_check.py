#!/usr/bin/env python3
"""Where PMTransport.Machine actually sits in the import graph.

Prints the lower layer the machine needs: every PMTransport.Machine module plus every
PMAction (or other) module imported, transitively, by one of them. A clean split
"machine below PMAction" needs that whole set below the rest of PMAction. Also lists the
machine modules that depend on no PMAction module at all.
Usage: python3 tools/layer_check.py [--list]
"""
import glob, os, re, sys

src = os.path.join(os.path.dirname(__file__), "..", "src")
mods = {}
for f in glob.glob(src + "/**/*.lean", recursive=True):
    m = os.path.relpath(f, src)[:-5].replace(os.sep, ".")
    mods[m] = re.findall(r"^import\s+([\w.]+)", open(f).read(), re.M)
mach = {m for m in mods if m.startswith("PMTransport.Machine.")}
lower, stack = set(mach), list(mach)
while stack:
    for i in mods.get(stack.pop(), []):
        if i in mods and i not in lower and not i.startswith(("PMSubstrate", "PersistenceMechanics")):
            lower.add(i); stack.append(i)
action = sorted(m for m in lower if m.startswith("PMAction"))
allA = [m for m in mods if m.startswith("PMAction.")]
memo = {}
def needs_action(m):
    if m not in memo:
        memo[m] = False
        memo[m] = any(i.startswith("PMAction") or (i in mods and needs_action(i)) for i in mods.get(m, []))
    return memo[m]
free = sorted(m for m in mach if not needs_action(m))
above = sorted(m for m in allA if m not in lower and any(i in mach for i in mods[m]))
print(f"machine modules: {len(mach)}; with no PMAction dependency: {len(free)}")
print(f"PMAction modules below the machine: {len(action)} of {len(allA)}")
print(f"PMAction modules above the machine (import it, not imported by it): {len(above)}")
other = sorted(m for m in lower if not m.startswith(("PMAction", "PMTransport.Machine")))
print(f"other modules below the machine: {other or 'none'}")
if "--list" in sys.argv:
    print("\n# machine with no PMAction dependency"); print("\n".join(free))
    print("\n# PMAction below the machine"); print("\n".join(action))
