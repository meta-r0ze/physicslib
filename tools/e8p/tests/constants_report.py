"""Exercise the compiled e8p reporter with an independent exact-rational parser.

Physics formulas are certified by PMConstantsProof. These checks cover CLI,
serialization, outward formatting, paper/only filtering, audit, and LaTeX blocks.
"""
import json
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
    "pion_plus_mev", "neutrino_floor_mass", "tau_lifetime_fs", "muon_lifetime_finite",
    "tau_lifetime_e8_natural", "neutron_spectral_fraction",
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
                      "pion_plus_mev", "neutrino_floor_mass", "tau_lifetime_fs", "muon_lifetime_finite",
                      "tau_lifetime_e8_natural", "neutron_spectral_fraction",
    "tau_lifetime_e8_natural", "neutron_spectral_fraction",
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

    human = run(binary).stdout
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
    nuc = run(binary, "--nuclear")
    assert nuc.returncode == 0
    assert "He-4" in nuc.stdout and "pp=1" in nuc.stdout and "0.012985" in nuc.stdout
    assert "0.000820" in nuc.stdout
    assert "11/4" in nuc.stdout and "16/5" in nuc.stdout and "mirror difference" in nuc.stdout
    lt = run(binary, "--line-table")
    assert lt.returncode == 0
    assert "C" in lt.stdout and "res_line" in lt.stdout and "Coulomb" in lt.stdout
    assert run(binary, "--help").returncode == 0
    print(f"e8p reporter checks passed: {len(EXPECTED)} rows, five precisions, paper/only filters, audit, latex, CLI")


if __name__ == "__main__":
    main()
