"""Exercise the compiled e8p reporter with an independent exact-rational parser.

Physics formulas are certified by PMConstantsProof. These checks cover CLI,
serialization, outward formatting, paper/only filtering, audit, and LaTeX blocks.
"""
import json
import re
from fractions import Fraction
from pathlib import Path
import subprocess
import sys


def run(binary, *args):
    return subprocess.run([str(binary), *args], capture_output=True, text=True)


EXPECTED = {
    # paper 0: substrate invariants
    "delta", "nu", "sigma", "chi", "D",
    # paper 1
    "alpha_inv", "alpha",
    # paper 1 pillars of alpha^-1
    "cap", "map", "protocol", "governor", "toll", "margin",
    "c_light", "von_klitzing", "planck_charge_attenuation", "planck_charge_ratio",
    "planck_mass",
    # paper 3
    "eta", "footprint", "weak_fraction", "lambda", "scalar_toll",
    "electron_yukawa", "alpha_s", "vev_over_me", "electron_mass_input",
    "vev", "higgs_mass", "fermi_constant",
    # paper 4
    "jarlskog", "wolf_lambda", "wolf_A", "wolf_rho", "wolf_eta",
    "sin2_theta12", "sin2_theta23", "sin2_theta13", "pmns_jarlskog",
    "pmns_e11", "pmns_e12", "pmns_e13", "pmns_e21", "pmns_e22", "pmns_e23",
    "pmns_e31", "pmns_e32", "pmns_e33",
    "ckm_s13", "ckm_s23", "ckm_vcb", "vud", "vud_dressed",
    # paper 0 derived loads + structure
    "l_intrinsic", "l_embed", "l_substrate", "n", "rm",
    "nc", "weinberg_gut", "boundary_storage", "beta_0",
    # paper 3 gravity
    "alpha_G", "w_ratio", "gauge_hyper", "gauge_colour",
    "w_mass_uncorrected", "z_mass_uncorrected", "g_weak", "g_prime", "electron_closure",
    "b_res",
    # paper 4 extra
    "jarlskog_geo", "cabibbo",
    # paper 5
    "proton_ratio", "neutron_ratio", "muon_ratio",
    "tau_ratio", "proton_radius", "pion0_mev", "kaon0_mev", "kaon_plus_mev",
    "up_mev", "down_mev", "strange_mev", "charm_mev", "bottom_mev", "top_mev",
    "pion_plus_mev", "f_pi_mev", "f_k_mev", "neutrino_floor_mass", "tau_lifetime_fs", "muon_lifetime_finite",
    "tau_lifetime_e8_natural", "neutron_spectral_fraction", "neutron_lifetime_e8",
    "muon_lifetime_s", "neutron_lifetime_s", "neutron_lifetime_predicted_s", "pion_lifetime_predicted_s", "kaon_pion_width_ratio", "neutron_lifetime_unified_s",
    "pion_finite_width", "pion_finite_lifetime",
    "kaon_finite_width", "kaon_finite_lifetime",
    "neutral_pion_finite_width", "neutral_pion_finite_lifetime",
    "pion_finite_lifetime_s", "kaon_finite_lifetime_s",
    "neutral_pion_finite_lifetime_s",
    "rydberg_ev", "bohr_radius", "shell_capacity_n4",
    # paper 6
    "load", "hubble_late", "clustering_late", "hubble_sigma", "s8_sigma",
    "omega_ratio", "baryon_pmJ", "baryon_pm3J", "z_eq", "dark_raw",
}


def main():
    binary = Path(sys.argv[1] if len(sys.argv) > 1 else ".lake/build/bin/e8p").resolve()
    for digits in (0, 3, 12, 18, 50):
        out = run(binary, "--json", "--digits", str(digits))
        assert out.returncode == 0, out.stderr
        report = json.loads(out.stdout)
        assert report["schema"] == "pm.e8p.v1"
        assert report["digits"] == digits
        rows = report["constants"]
        assert len(rows) == len(EXPECTED)
        assert {r["id"] for r in rows} == EXPECTED
        for row in rows:
            assert row["paper"] in {"0", "1", "3", "4", "5", "6"}
            lo, hi = Fraction(row["rational_lower"]), Fraction(row["rational_upper"])
            dlo, dhi = Fraction(row["decimal_lower"]), Fraction(row["decimal_upper"])
            assert dlo <= lo <= hi <= dhi, (digits, row)
            quantum = Fraction(1, 10**digits)
            assert 0 <= lo - dlo < quantum, (digits, row)
            assert 0 <= dhi - hi < quantum, (digits, row)
            assert row["kind"] == ("exact_rational" if lo == hi else "certified_interval")
            assert row["theorem"]
        by_id = {r["id"]: r for r in rows}
        assert by_id["electron_mass_input"]["role"] == "external_input"
        for key in ("vev", "higgs_mass", "fermi_constant"):
            assert by_id[key]["inputs"] == ["electron_mass_input"]
        assert by_id["fermi_constant"]["unit"] == "GeV^-2"
        assert by_id["alpha_inv"]["experimental"] is not None
        assert "sigma" in by_id["alpha_inv"]["experimental"]
        assert len(by_id["alpha_inv"]["comparisons"]) == 4
        assert len(by_id["w_mass_uncorrected"]["comparisons"]) == 2
        for c in by_id["alpha_inv"]["comparisons"]:
            assert {"value", "uncertainty", "citation", "diff", "sigma"} <= set(c)

    # Match inverse partial widths to partial-lifetime references, never total lifetimes.
    pion_tau, pion_b = Fraction("26.033e-9"), Fraction("0.9998770")
    kaon_tau, kaon_b = Fraction("12.380e-9"), Fraction("0.6356")
    neutral_tau, neutral_b = Fraction("8.43e-17"), Fraction("0.98823")
    partials = {
        "pion_lifetime_predicted_s": pion_tau / pion_b,
        "kaon_finite_lifetime_s": kaon_tau / kaon_b,
        "neutral_pion_finite_lifetime_s": neutral_tau / neutral_b,
        "kaon_pion_width_ratio": (pion_tau / pion_b) / (kaon_tau / kaon_b),
    }
    for key, expected in partials.items():
        row = by_id[key]
        assert Fraction(row["experimental"]["value"]) == expected
        assert "partial" in row["decay"]["observable"]
        assert row["experimental"]["uncertainty_note"]
    # Each stored error bounds first-order independent-input quadrature, with only rounding slack.
    for key, tau, branch, dtau, dbranch in (
        ("pion_lifetime_predicted_s", pion_tau, pion_b, Fraction("5e-12"), Fraction("0.0000004")),
        ("kaon_finite_lifetime_s", kaon_tau, kaon_b, Fraction("0.020e-9"), Fraction("0.0011")),
        ("neutral_pion_finite_lifetime_s", neutral_tau, neutral_b, Fraction("0.13e-17"), Fraction("0.00034")),
    ):
        variance = (dtau / branch)**2 + (tau*dbranch / branch**2)**2
        error = Fraction(by_id[key]["experimental"]["uncertainty"])
        assert variance <= error**2 <= variance * Fraction("1.002"), (key, error)
    ratio = partials["kaon_pion_width_ratio"]
    variance = ratio**2 * ((Fraction("5e-12")/pion_tau)**2 +
        (Fraction("0.0000004")/pion_b)**2 + (Fraction("0.020e-9")/kaon_tau)**2 +
        (Fraction("0.0011")/kaon_b)**2)
    error = Fraction(by_id["kaon_pion_width_ratio"]["experimental"]["uncertainty"])
    assert variance <= error**2 <= variance * Fraction("1.002")
    assert not by_id["kaon_finite_lifetime_s"]["experimental"]["scored"]
    assert not by_id["muon_lifetime_s"]["experimental"]["scored"]
    assert Fraction(by_id["tau_lifetime_fs"]["experimental"]["uncertainty"]) == Fraction("0.82")
    assert "already combines" in by_id["tau_lifetime_fs"]["caveat"]
    assert "van Ritbergen-Stuart" in by_id["muon_lifetime_s"]["caveat"]
    assert by_id["alpha_inv"]["decay"] is None
    # Reporting changes must not change the physical formulas' certified intervals.
    for key, interval in {
        "pion_lifetime_predicted_s": ("2.61592e-8", "2.61602e-8"),
        "kaon_finite_lifetime_s": ("1.98e-8", "2.12e-8"),
        "neutral_pion_finite_lifetime_s": ("8.44e-17", "8.48e-17"),
        "muon_lifetime_s": ("2.196974e-6", "2.196984e-6"),
    }.items():
        assert tuple(Fraction(by_id[key][field]) for field in ("rational_lower", "rational_upper")) == tuple(map(Fraction, interval))
    decay_text = run(binary, "--values", "--only=neutral_pion_finite_lifetime_s").stdout
    assert "two-photon partial" in decay_text and "quadrature" in decay_text
    assert re.search(r"exp.*[1-9][0-9.]*e-17", decay_text), decay_text
    assert "van Ritbergen-Stuart" in run(binary, "--values", "--only=muon_lifetime_s").stdout
    decay_audit = run(binary, "--audit", "--only=kaon_finite_lifetime_s").stdout
    assert "· kaon_finite_lifetime_s" in decay_audit and "not total K lifetime" in decay_audit
    decay_latex = run(binary, "--latex", "--only=neutral_pion_finite_lifetime_s").stdout
    assert "Observable>inverse two-photon partial" in decay_latex and "ComparisonNote>partial reference" in decay_latex

    # paper filtering
    def ids(paper):
        return {r["id"] for r in json.loads(run(binary, "--json", f"--paper={paper}").stdout)["constants"]}
    assert ids(0) == {"delta", "nu", "sigma", "chi", "D", "l_intrinsic", "l_embed",
                      "l_substrate", "n", "rm", "nc", "weinberg_gut", "boundary_storage"}
    assert ids(1) == {"alpha_inv", "alpha", "cap", "map", "protocol", "governor", "toll",
                      "margin", "c_light", "von_klitzing", "planck_charge_attenuation",
                      "planck_charge_ratio", "planck_mass"}
    assert len(ids(3)) == 23
    assert ids(4) == {"jarlskog", "jarlskog_geo", "cabibbo", "wolf_lambda", "wolf_A",
                      "wolf_rho", "wolf_eta", "sin2_theta12", "sin2_theta23",
                      "sin2_theta13", "pmns_jarlskog",
                      "pmns_e11", "pmns_e12", "pmns_e13", "pmns_e21", "pmns_e22",
                      "pmns_e23", "pmns_e31", "pmns_e32", "pmns_e33",
                      "ckm_s13", "ckm_s23", "ckm_vcb", "vud", "vud_dressed"}
    assert ids(5) == {"proton_ratio", "neutron_ratio", "muon_ratio", "tau_ratio",
                      "proton_radius", "pion0_mev", "kaon0_mev", "kaon_plus_mev",
                      "up_mev", "down_mev", "strange_mev", "charm_mev", "bottom_mev", "top_mev",
                      "pion_plus_mev", "f_pi_mev", "f_k_mev", "neutrino_floor_mass", "tau_lifetime_fs", "muon_lifetime_finite",
                      "tau_lifetime_e8_natural", "neutron_spectral_fraction", "neutron_lifetime_e8",
    "muon_lifetime_s", "neutron_lifetime_s", "neutron_lifetime_predicted_s", "pion_lifetime_predicted_s", "kaon_pion_width_ratio", "neutron_lifetime_unified_s",
    "pion_finite_width", "pion_finite_lifetime",
    "kaon_finite_width", "kaon_finite_lifetime",
    "neutral_pion_finite_width", "neutral_pion_finite_lifetime",
    "pion_finite_lifetime_s", "kaon_finite_lifetime_s",
    "neutral_pion_finite_lifetime_s",
    "tau_lifetime_e8_natural", "neutron_spectral_fraction", "neutron_lifetime_e8",
    "muon_lifetime_s", "neutron_lifetime_s", "neutron_lifetime_predicted_s", "pion_lifetime_predicted_s", "kaon_pion_width_ratio", "neutron_lifetime_unified_s",
    "pion_finite_width", "pion_finite_lifetime",
    "kaon_finite_width", "kaon_finite_lifetime",
    "neutral_pion_finite_width", "neutral_pion_finite_lifetime",
    "pion_finite_lifetime_s", "kaon_finite_lifetime_s",
    "neutral_pion_finite_lifetime_s",
                      "rydberg_ev", "bohr_radius", "shell_capacity_n4"}
    assert ids(6) == {"load", "hubble_late", "clustering_late", "hubble_sigma", "s8_sigma",
                      "omega_ratio", "baryon_pmJ", "baryon_pm3J", "z_eq", "dark_raw"}

    # --only filter (space and equals forms)
    only = json.loads(run(binary, "--json", "--only=wolf_rho,omega_ratio").stdout)
    assert {r["id"] for r in only["constants"]} == {"wolf_rho", "omega_ratio"}
    only2 = json.loads(run(binary, "--json", "--only", "delta,cap").stdout)
    assert {r["id"] for r in only2["constants"]} == {"delta", "cap"}

    assert by_id["rydberg_ev"]["section"] == "Atoms"
    assert by_id["alpha_inv"]["section"] == "Substrate"
    assert by_id["wolf_rho"]["section"] == "Flavor"
    assert by_id["hubble_late"]["section"] == "Cosmology"
    assert by_id["hubble_late"]["inputs"] == ["h0_anchor"]
    assert by_id["clustering_late"]["inputs"] == ["s8_anchor"]

    human = run(binary, "--values").stdout
    everything = run(binary).stdout
    assert "comparisons over" in everything and "Periodic table" in everything and "Shells" in everything
    assert "Substrate" in human and "Constants" in human and "Atoms" in human
    assert "Paper 1" not in human
    for key in EXPECTED:
        assert key + "  —" in human or key + " [" in human
    assert "supplied input" in human

    audit = run(binary, "--audit").stdout
    assert "σ" in audit and "comparisons over" in audit and "✓" in audit
    assert "undressed; compare vud_dressed" in audit
    assert "uses measured muon lifetime and B_e" in audit
    audit_only = run(binary, "--audit", "--only=wolf_rho").stdout
    assert "wolf_rho" in audit_only and "omega_ratio" not in audit_only

    # Independently sum unrounded pulls from the exact JSON enclosure midpoints.
    # This also tests deriving-paper groups (Substrate combines papers 0 and 1),
    # alternative references, context exclusions, filtering and the N=0 case.
    def check_chi(args, selected):
        text = run(binary, "--audit", *args).stdout
        parsed = dict((label, (int(n), Fraction(chi), red)) for label, n, chi, red in
                      re.findall(r"(Paper [0-9]+|All selected): N = ([0-9]+); χ² = ([0-9.]+); reduced χ² = ([0-9.]+|n/a)", text))
        def expected(rs):
            pulls = []
            for row in rs:
                mid = (Fraction(row["rational_lower"]) + Fraction(row["rational_upper"])) / 2
                for ref in row["comparisons"]:
                    if ref["scored"]:
                        pulls.append((mid - Fraction(ref["value"])) / Fraction(ref["uncertainty"]))
            return len(pulls), sum((p*p for p in pulls), Fraction(0))
        groups = {f"Paper {p}": [r for r in selected if r["paper"] == p]
                  for p in {r["paper"] for r in selected}}
        groups["All selected"] = selected
        assert set(parsed) == set(groups), (args, text)
        for label, rs in groups.items():
            n, chi = expected(rs)
            pn, pc, pr = parsed[label]
            assert pn == n and 0 <= chi - pc < Fraction(1, 1000), (label, parsed[label], chi)
            if n:
                assert pr != "n/a" and 0 <= chi/n - Fraction(pr) < Fraction(1, 1000)
            else:
                assert pc == 0 and pr == "n/a"
    check_chi([], rows)
    check_chi(["--digits", "0"], rows)
    check_chi(["--paper=1"], [r for r in rows if r["paper"] == "1"])
    for key in ("wolf_rho", "alpha_inv", "w_mass_uncorrected", "delta"):
        check_chi([f"--only={key}"], [by_id[key]])
    check_chi(["--only=not_a_key"], [])

    latex = run(binary, "--latex").stdout
    assert "%<*alpha_invVal>" in latex and "%<*alpha_invEq>" in latex
    assert "%<*capVal>" in latex and "%<*deltaEq>" in latex

    for args in (["--digits"], ["--digits", "-1"], ["--digits", "51"],
                 ["--digits", "no"], ["--unknown"], ["--paper=9"], ["--only"]):
        out = run(binary, *args)
        assert out.returncode == 2 and out.stderr and not out.stdout, args
    table = run(binary, "--periodic-table")
    assert table.returncode == 0
    assert "configuration" in table.stdout and "1s1" in table.stdout and "2p6" in table.stdout
    assert "20  Ca" in table.stdout
    assert "12.000000" in table.stdout  # C-12 isotopic mass, not the 12.011 standard weight
    table5 = run(binary, "--periodic-table", "5")
    assert table5.returncode == 0 and "5  B" in table5.stdout and "6  C" not in table5.stdout
    table3 = run(binary, "--periodic-table=3")
    assert table3.returncode == 0 and "3  Li" in table3.stdout and "4  Be" not in table3.stdout
    cert = run(binary, "--certified")
    assert cert.returncode == 0
    assert "E8 ledger (m_e)" in cert.stdout and "12.000" in cert.stdout and "z(scatter)" in cert.stdout and "nuclei compared" in cert.stdout
    assert run(binary, "--masses").stdout == cert.stdout
    assert "C-12" in run(binary, "--masses=6,6").stdout
    cert12 = run(binary, "--certified=6,6")
    assert cert12.returncode == 0
    assert "C-12" in cert12.stdout and "12.000" in cert12.stdout and "E8 − measured" in cert12.stdout
    certcf = run(binary, "--certified=98,154")
    assert certcf.returncode == 0 and "no enclosure printed" in certcf.stdout
    nuc = run(binary, "--nuclear")
    assert nuc.returncode == 0
    assert "He-4" in nuc.stdout and "pp=1" in nuc.stdout and "0.012985" in nuc.stdout
    assert "0.000820" in nuc.stdout
    assert "11/4" in nuc.stdout and "16/5" in nuc.stdout and "mirror difference" in nuc.stdout
    assert run(binary, "--line-table").returncode == 2
    assert "2S+1" in table.stdout
    summ = run(binary, "--summary")
    assert summ.returncode == 0
    assert "## Decay conventions and comparison errors" in summ.stdout
    assert "## Scoreboard" in summ.stdout and "## Tensions" in summ.stdout and "proton_ratio" in summ.stdout
    shells = run(binary, "--shells")
    assert shells.returncode == 0
    assert "1h11/2" in shells.stdout and "same set" in shells.stdout
    assert "[2, 8, 20, 28, 50, 82, 126]" in shells.stdout
    assert run(binary, "--help").returncode == 0
    print(f"e8p reporter checks passed: {len(EXPECTED)} rows, five precisions, paper/only filters, audit, latex, CLI")


if __name__ == "__main__":
    main()
