"""One charged-current normalization for the hadron rates (PMHadrons REVIEW, first item).

Convention, each factor once:
  Gamma(P -> mu nu (gamma)) = G_F^2 |V_eff|^2 f_P^2 m_P m_mu^2 (1 - m_mu^2/m_P^2)^2 / (8 pi) * (1 + delta_P)
with G_F from muon decay, |V_eff| = q |V| (PMFlavor's dressing q^2 = 515/516 of colour-carrier
transitions, which muon decay does not carry: PMFlavor.DressingInheritance), and delta_P the full
radiative correction (short- plus long-distance, hadronic structure): delta_pi = 0.0176(21),
delta_K = 0.0107(21) (PDG review, Rosner-Stone-Van de Water, arXiv:1509.02220). The same review
extracts |V_ud| f_pi = 127.13(13) MeV and |V_us| f_K = 35.09(6) MeV from the measured widths in
exactly this convention, so the E8 products can be compared directly.

The library's pion factor 32/33 stands in for |V_ud|^2 (1 + delta_pi); it agrees with |V_ud|^2 R
(R the derived short-distance running, ShortDistanceRunning) to 6e-5, but that omits the dressing
and the long-distance part. The derived R is the short-distance piece of delta: (2 alpha/pi) ln(M_Z/mu)
with mu = m_p and the E8 M_Z, against the standard (2 alpha/pi) ln(M_Z/m_rho) - QCD (0.0219).
"""
import math
a = 1/137.035999212
q = math.sqrt(515/516)
vud, vus = 0.9744945, 0.22435        # E8 (PMFlavor.Values.vud_bounds, KaonWidth.vusE8_bounds)
fpi, fK = 130.275, 154.565           # E8 (pionDecayConstantMeV_bounds, kaonDecayConstantMeV_bounds)
meas = {"pi": (127.13, 0.13), "K": (35.09, 0.06)}   # |V| f from the measured widths, 1509.02220
dpi, dK = 0.0176, 0.0107
print("E8 |V| f against the measured |V| f (convention above):")
for name, V, f in (("pi", vud, fpi), ("K", vus, fK)):
    m, e = meas[name]
    for lab, Veff in (("dressed q|V|", q*V), ("undressed |V|", V)):
        x = Veff*f
        print(f"  {name}: {lab:14s} {x:8.3f} MeV  vs {m} +/- {e}:  {100*(x/m-1):+.2f}%  {(x-m)/e:+.1f} sigma")
print("what the library's 32/33 amounts to for the pion: |V|_eff f =",
      round(fpi*math.sqrt((32/33)/(1+dpi)), 3), "MeV (fitted by construction)")
R = 1.021179
sd = 2*a/math.pi*math.log(91187.6/775.26) - 0.00033
print(f"short distance: derived R - 1 = {R-1:.5f} (mu = m_p, E8 M_Z); standard {sd:.5f} (mu = m_rho, QCD-corrected)")
print("f_pi the measurement implies (dressed): ", round(127.13/(q*vud), 2), "+/-", round(0.13/(q*vud), 2), "MeV; E8", fpi)
print("f_K  the measurement implies (dressed): ", round(35.09/(q*vus), 2), "+/-", round(0.06/(q*vus), 2), "MeV; E8", fK)
