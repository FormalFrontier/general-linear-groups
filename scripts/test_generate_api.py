# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
# Adapted by Prism (AI) from Anchor (AI), ideal-completion
# f0c8c34386109116e4912fb425a8ad15d9dc42a4/scripts/test_generate_api.py.
# Portable controls from group-rings fe121a046bd40691bba6cf275273a71cd5d7d007;
# Dedekind adaptation f2f718d4e38f5b1a6ef1ce683a7ca8a405974bf6 (unreviewed input);
# GLG 128-declaration/16-module adaptation by Prism (AI).
"""Bounded data-only controls; actual native records are checked separately."""
import copy
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
import generate_api as api

REV = "a" * 40
LEAF0 = "GeneralLinearGroups.AdditiveCommutator"
LEAF1 = "GeneralLinearGroups.CongruenceSubgroup"


def fixture():
    records = {m: dict(name=m, declarations=[]) for m in api.MODULES}
    for i, (name, kind) in enumerate(api.EXPECTED.items(), 1):
        module = api.DECL_MODULES[name]
        header = (f'<div class="decl_header"><span class="decl_kind">{api.displayed_kind(name, kind)}</span> '
                  f'<span class="decl_name">{name}</span> '
                  f'<span>{" ".join(api.assumptions(name))}</span> :'
                  '<div class="decl_type">A → A</div></div>')
        records[module]["declarations"].append(dict(header=header, info=dict(
            name=name, kind=kind, doc="Fixture only; not a claimed Lean declaration.",
            line=i, sourceLink="source-snapshot:" + REV + "/" +
            api.MODULE_PATHS[module],
            docLink="./" + module.replace(".", "/") + ".html#" + name)))
    sources = {p: b"fixture\n" * 256 for p in api.INPUTS}
    return records, sources


class Controls(unittest.TestCase):
    def test_all_128_and_binding(self):
        records, sources = fixture()
        raw, manifest = api.render(records, REV, sources)
        facts = json.loads(manifest)
        self.assertEqual(raw.count(b"\n## "), 128)
        self.assertEqual(facts["api_sha256"], api.digest(raw))
        self.assertEqual(set(facts["inputs"]), set(api.INPUTS))
        self.assertNotIn(b"example.invalid", raw + manifest)
        self.assertFalse(facts["proof_certification"])

    def test_implicit_arguments_and_entities_retained(self):
        header = api.Header('<div><span>{A : Type u} [CommSemiring A] '
                            '{σ : Type v}</span> :<div class="decl_type">'
                            'x &lt; y ∧ x ≤ y</div></div>')
        self.assertEqual(header.rendered(),
                         '{A : Type u} [CommSemiring A] {σ : Type v} : x < y ∧ x ≤ y')

    def test_no_whitespace_inside_name_added(self):
        self.assertEqual(api.Header('<span><span>Order</span>.<span>Ideal</span></span>').rendered(),
                         'Order.Ideal')

    def test_refuse_corruptions(self):
        mutations = [
            lambda r: r.pop(LEAF1),
            lambda r: r[LEAF0]["declarations"].pop(),
            lambda r: r[LEAF0]["declarations"].append(copy.deepcopy(r[LEAF0]["declarations"][0])),
            lambda r: r[LEAF1]["declarations"].append(copy.deepcopy(r[LEAF0]["declarations"][0])),
            lambda r: r[LEAF0].update(name="Wrong"),
        ]
        for key, value in [("name", "Wrong"), ("kind", "axiom"), ("doc", ""),
                           ("line", 0), ("line", 999), ("line", True),
                           ("sourceLink", "https://example.invalid/main/x.lean"),
                           ("docLink", "wrong"), ("doc", "```inject")]:
            mutations.append(lambda r, k=key, v=value: r[LEAF0]["declarations"][0]["info"].update({k: v}))
        mutations += [
            lambda r: r[LEAF0]["declarations"][0]["info"].update(sourceLink=
                r[LEAF0]["declarations"][0]["info"]["sourceLink"] + "#L2-L2"),
            lambda r: r[LEAF0]["declarations"][0]["info"].update(sourceLink=
                r[LEAF0]["declarations"][0]["info"]["sourceLink"].replace(REV, "b" * 40)),
            lambda r: r[LEAF0]["declarations"][1].update(header=
                r[LEAF0]["declarations"][1]["header"].replace("theorem", "def")),
            lambda r: r[LEAF0]["declarations"][0].update(header="<script>bad</script>"),
            lambda r: r[LEAF0]["declarations"][0].update(header="<div><span></div>"),
            lambda r: r[LEAF0]["declarations"][0].update(header="<span onclick='bad'>x</span>"),
            lambda r: r[LEAF0]["declarations"][0].update(header=r[LEAF0]["declarations"][0]["header"].replace("[Ring R]", "")),
        ]
        for i, mutate in enumerate(mutations):
            with self.subTest(control=i):
                records, sources = fixture()
                mutate(records)
                with self.assertRaises(ValueError):
                    api.render(records, REV, sources)

    def test_revision_and_inventory(self):
        records, sources = fixture()
        for rev in ["main", "a" * 39, "-" * 40]:
            with self.assertRaises(ValueError):
                api.render(records, rev, sources)
        sources.pop("lean-toolchain")
        with self.assertRaises(ValueError):
            api.render(records, REV, sources)

    def test_each_declaration_module_and_assumptions(self):
        for name in api.EXPECTED:
            module = api.DECL_MODULES[name]
            for mutation in ["missing", "wrong-module", *api.assumptions(name)]:
                with self.subTest(declaration=name, mutation=mutation):
                    records, sources = fixture()
                    row = next(r for r in records[module]["declarations"]
                               if r["info"]["name"] == name)
                    if mutation == "missing":
                        records[module]["declarations"].remove(row)
                    elif mutation == "wrong-module":
                        records[module]["declarations"].remove(row)
                        records[api.MODULES[-1]]["declarations"].append(row)
                    else:
                        row["header"] = row["header"].replace(mutation, "WrongAssumption")
                    with self.assertRaises(ValueError):
                        api.render(records, REV, sources)

    def test_retained_binding(self):
        records, sources = fixture()
        _, manifest = api.render(records, REV, sources)
        binding = json.loads(manifest)
        api.validate_binding(binding, REV, sources, records)
        # Adapter changes require regenerated output, not invented source hashes.
        binding["adapter_sha256"] = "b" * 64
        api.validate_binding(binding, REV, sources, records)

    def test_binding_refusals(self):
        records, sources = fixture()
        _, manifest = api.render(records, REV, sources)
        mutations = [
            lambda b: b.update(extra="unrecognized"),
            lambda b: b.pop("inputs"),
            lambda b: b.update(format=True),
            lambda b: b.update(format=2),
            lambda b: b.update(generator="other.py"),
            lambda b: b.update(docgen_revision="b" * 40),
            lambda b: b.update(analyzed_source_revision="b" * 40),
            lambda b: b.update(modules=list(reversed(api.MODULES))),
            lambda b: b["inputs"].pop("lean-toolchain"),
            lambda b: b["inputs"].update(extra="a" * 64),
            lambda b: b["inputs"].update({"lean-toolchain": "a" * 64}),
            lambda b: b["native_record_sha256"].pop(LEAF0),
            lambda b: b["native_record_sha256"].update({LEAF0: "a" * 64}),
            lambda b: b.update(public_declarations=["Wrong"] * len(api.EXPECTED)),
            lambda b: b.update(public_declarations=[{}] * len(api.EXPECTED)),
            lambda b: b.update(proof_certification=True),
            lambda b: b.update(proof_certification=0),
            lambda b: b.update(adapter_sha256="bad"),
            lambda b: b.update(api_sha256=False),
        ]
        for index, mutate in enumerate(mutations):
            with self.subTest(control=index):
                binding = json.loads(manifest)
                mutate(binding)
                with self.assertRaises(ValueError):
                    api.validate_binding(binding, REV, sources, records)
        binding = json.loads(manifest)
        sources["lean-toolchain"] += b"changed\n"
        with self.assertRaises(ValueError):
            api.validate_binding(binding, REV, sources, records)
        records, sources = fixture()
        records[LEAF0]["declarations"][0]["info"]["doc"] += " changed"
        with self.assertRaises(ValueError):
            api.validate_binding(binding, REV, sources, records)

    def test_duplicate_json_fields(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "binding.json"
            path.write_text('{"inputs": {}, "inputs": {}}')
            with self.assertRaises(ValueError):
                api.load_json(path)

    def test_source_only_cli_and_refusals(self):
        records, sources = fixture()
        markdown, manifest = api.render(records, REV, sources)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "scripts").mkdir()
            (root / "docs").mkdir()
            (root / "native").mkdir()
            shutil.copyfile(api.__file__, root / "scripts/generate_api.py")
            for path, raw in sources.items():
                target = root / path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(raw)
            for module, record in records.items():
                (root / "native" / ("declaration-data-" + module + ".bmp")).write_text(json.dumps(record))
            (root / "docs/API.md").write_bytes(markdown)
            bound = root / "docs/api-manifest.json"
            bound.write_bytes(manifest)
            argv = [sys.executable, "-B", "-O", str(root / "scripts/generate_api.py"),
                    "--native-data", str(root / "native"), "--source-revision", REV]

            def run(*flags):
                # No Git executable, inherited repository or PYTHONPATH is needed.
                return subprocess.run(argv + list(flags), cwd=root,
                                      env={"PATH": str(root / "no-executables")},
                                      capture_output=True, timeout=20)

            self.assertEqual(run("--check").returncode, 0)
            self.assertEqual(run().returncode, 0)
            self.assertEqual(bound.read_bytes(), manifest)
            self.assertEqual((root / "docs/API.md").read_bytes(), markdown)
            self.assertNotEqual(run("--check", "--refresh-binding").returncode, 0)
            self.assertNotEqual(run("--refresh-binding").returncode, 0)
            for path in api.INPUTS:
                target = root / path
                raw = target.read_bytes()
                target.write_bytes(raw + b"changed\n")
                for flags in [(), ("--check",)]:
                    self.assertNotEqual(run(*flags).returncode, 0)
                self.assertEqual(bound.read_bytes(), manifest)
                target.write_bytes(raw)
            bound.unlink()
            self.assertNotEqual(run().returncode, 0)
            bound.write_bytes(manifest)
            self.assertEqual(run("--check").returncode, 0)


if __name__ == "__main__":
    unittest.main()
