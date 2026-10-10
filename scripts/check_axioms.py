#!/usr/bin/env python3
"""Print and check all 198 frozen anchors, then audit every project declaration.

Run from the project root after lake build: python3 scripts/check_axioms.py
No axiom beyond propext, Classical.choice, Quot.sound is accepted.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import secrets
import shutil
import subprocess
import sys
import tempfile

STANDARD = {"propext", "Classical.choice", "Quot.sound"}
ANCHOR_DIGEST = "037625cc9567328cb23dbd16c0c434f830bf0c2f34f0f27eceb4bd3549f71605"
ALL_DECLS = r"""import Christodoulou
import Lean
open Lean Elab Command

/-- Transitive axiom dependencies, walking types and values directly (no olean axiom cache). -/
partial def axVisit (env : Environment) (c : Name) :
    StateM (NameMap NameSet) NameSet := do
  if let some r := (← get).find? c then return r
  modify fun m => m.insert c {}
  let mut acc : NameSet := {}
  let deps : Array Name ← pure <| match env.find? c with
    | some (.axiomInfo v) => v.type.getUsedConstants
    | some (.defnInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.thmInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.opaqueInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.ctorInfo v) => v.type.getUsedConstants
    | some (.recInfo v) => v.type.getUsedConstants
    | some (.inductInfo v) => v.type.getUsedConstants ++ v.ctors.toArray
    | _ => #[]
  if let some (.axiomInfo _) := env.find? c then acc := acc.insert c
  for d in deps do
    for a in (← axVisit env d) do acc := acc.insert a
  modify fun m => m.insert c acc
  return acc

/-- The declarations stored in a module's most private serialized part (as the Lean kernel replay tool reads
them), independent of the merged environment. -/
def storedConstants (m : Name) : IO (Array ConstantInfo) := do
  let mFile ← findOLean m
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  match parts.back? with
  | some (d, _) => return d.constants
  | none => throw <| IO.userError s!"no module data for {m}"

run_cmd do
  let env ← getEnv
  let std : NameSet := ({} : NameSet) |>.insert ``propext |>.insert ``Classical.choice
    |>.insert ``Quot.sound
  let root := `Christodoulou
  let mut names : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      let mod := env.header.moduleNames[idx.toNat]!
      if root.isPrefixOf mod then names := names.push n
  let mut projAx : Array Name := #[]
  let mut bad : Array String := #[]
  let mut privCount := 0
  let mut memo : NameMap NameSet := {}
  for n in names do
    if isPrivateName n then privCount := privCount + 1
    if let some (.axiomInfo _) := env.find? n then projAx := projAx.push n
    let (axs, m') := (axVisit env n).run memo
    memo := m'
    for a in axs do
      unless std.contains a do bad := bad.push s!"{n} -> {a}"
  -- Compare every stored occurrence with the declaration being audited.
  let mods := env.header.moduleNames.filter (root.isPrefixOf ·)
  let mut occ : Nat := 0
  let mut conflicts : Array String := #[]
  for m in mods do
    logInfo m!"PROJECT-MODULE @NONCE@ {m}"
    let cs ← storedConstants m
    for ci in cs do
      occ := occ + 1
      match env.find? ci.name with
      | some ci' =>
        unless ci == ci' do conflicts := conflicts.push s!"{m}: {ci.name} differs from the audited declaration"
      | none => conflicts := conflicts.push s!"{m}: {ci.name} missing from the environment"
      -- Audit every stored occurrence as a root too (including declarations realized in a
      -- project module under a name whose module index points elsewhere).
      let (axs, m') := (axVisit env ci.name).run memo
      memo := m'
      for a in axs do
        unless std.contains a do bad := bad.push s!"{ci.name} -> {a}"
      if let .axiomInfo _ := ci then
        unless projAx.contains ci.name do projAx := projAx.push ci.name
  for b in bad[:50] do logInfo m!"NONSTANDARD {b}"
  for c in conflicts[:50] do logInfo m!"CONFLICT {c}"
  logInfo m!"AXIOMS-ALL @NONCE@ decls={names.size} private={privCount} project_axioms={projAx.size} nonstandard={bad.size} modules={mods.size} occurrences={occ} conflicts={conflicts.size}"
"""


def main():
    root = Path(__file__).resolve().parents[1]
    metadata = root / "depgraph/anchors.json"
    if hashlib.sha256(metadata.read_bytes()).hexdigest() != ANCHOR_DIGEST:
        raise ValueError("anchor inventory differs from the release inventory")
    anchors = json.loads(metadata.read_text())["anchors"]
    exports = [a["declaration"] for a in anchors]
    if len(anchors) != 198 or len(set(exports)) != 198 or any(a["state"] != "SEALED" for a in anchors):
        raise ValueError("expected exactly 198 distinct sealed anchors")
    expected = {a["file"] for a in anchors}
    actual = {p.relative_to(root).as_posix() for p in (root / "Christodoulou/Frozen").rglob("*.lean")}
    if expected != actual:
        raise ValueError("anchor inventory does not cover every frozen file exactly")
    for a in anchors:
        if hashlib.sha256((root / a["file"]).read_bytes()).hexdigest() != a["sha256"]:
            raise ValueError("frozen file differs from release: " + a["file"])
    env = {k: v for k, v in os.environ.items()
           if not k.startswith(("LEAN_", "LAKE_")) and k != "ELAN_TOOLCHAIN"}
    lake = shutil.which("lake", path=env.get("PATH"))
    if lake is None:
        raise ValueError("lake not found on PATH")
    with tempfile.TemporaryDirectory(prefix=".axiom-audit-", dir=root) as tmp:
        probe = Path(tmp) / "Anchors.lean"
        probe.write_text("import Christodoulou\n" + "".join("#print axioms " + e + "\n" for e in exports))
        result = subprocess.run([lake, "env", "lean", str(probe)], cwd=root, env=env,
                                capture_output=True, text=True)
        print(result.stdout, end="", flush=True)
        if result.stderr:
            print(result.stderr, file=sys.stderr, end="")
        output = result.stdout.replace("\n ", " ")
        found = {}
        for match in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", output):
            name, axioms = match.groups()
            if name in found:
                raise ValueError("duplicate axiom output: " + name)
            found[name] = set(filter(None, (x.strip() for x in (axioms or "").split(","))))
        bad = [e for e in exports if e not in found or not found[e] <= STANDARD]
        if result.returncode or bad or set(found) != set(exports):
            raise ValueError("anchor axiom check failed: " + repr(bad))
        nonce = secrets.token_hex(16)
        probe = Path(tmp) / "AllDeclarations.lean"
        probe.write_text(ALL_DECLS.replace("@NONCE@", nonce))
        result = subprocess.run([lake, "env", "lean", str(probe)], cwd=root, env=env,
                                capture_output=True, text=True)
        output = result.stdout.replace("\n ", " ")
        matches = re.findall(r"AXIOMS-ALL " + nonce + r" decls=(\d+) private=(\d+) project_axioms=(\d+) "
                             r"nonstandard=(\d+) modules=(\d+) occurrences=(\d+) conflicts=(\d+)", output)
        if result.returncode or len(matches) != 1:
            print(result.stdout, end="")
            print(result.stderr, file=sys.stderr, end="")
            raise ValueError("all-declaration audit did not complete")
        decls, private, project_axioms, nonstandard, modules, occurrences, conflicts = map(int, matches[0])
        imported = set(re.findall(r"PROJECT-MODULE " + nonce + r" (\S+)", output))
        inventory = set()
        for directory, extension in [(root, ".lean"), (root / ".lake/build/lib/lean", ".olean")]:
            if (directory / ("Christodoulou" + extension)).exists():
                inventory.add("Christodoulou")
            for p in (directory / "Christodoulou").rglob("*" + extension):
                inventory.add(p.relative_to(directory).with_suffix("").as_posix().replace("/", "."))
        if (project_axioms or nonstandard or conflicts or modules != len(imported)
                or inventory - imported or decls < 198 or occurrences < decls):
            print(output, end="")
            raise ValueError("all-declaration axiom or module inventory check failed")
        print(f"AXIOM CHECK OK: 198 sealed exports; all {decls} project declarations "
              f"({private} private; {occurrences} stored occurrences in {modules} modules; "
              "all source and built modules imported) depend on standard axioms only")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, TypeError) as error:
        print("AXIOM CHECK FAIL: " + str(error), file=sys.stderr)
        sys.exit(1)
