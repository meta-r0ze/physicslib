#!/usr/bin/env python3
"""Tier ledger versus wire routes (external, arithmetic; EP OVERVIEW, "Tier ledger and the wire").

The tier ledger (QuarkMasses, LeptonMasses) gives each protocol three tiers Delta^n. The derived
wire gives the heaviest-to-middle ratio one node passage, k = alpha/2 with alpha^-1 ~ pi Delta,
so one power of 1/Delta, and the lightest mass zero at resonance. This prints the ledger's two
generation steps in powers of 1/Delta for each protocol: both ledger and wire put the
heavy-to-middle step at one power of Delta for every protocol, and the ledger puts up's
middle-to-light step at two powers (exactly 3/Delta^2) and down's and the electron's at one.
"""
import math

D, S, C, De = 4, 5, 2, 43
eta = 171 / 172
up, down = D / eta, (D + S) / eta
strange, charm = (D * De + C * S) / eta, D * De**2 / (eta * (S - C))
bottom, top = De**2 * (D + C / S) / eta, De**3 * (D + 1 / D)
e, mu, tau = 1.0, 206.768, 3477.0  # LeptonMasses tier ledger values (units of m_e)
k = (1 / 137.035999) / 2
print(f"wire, bare: m2/m3 = sqrt(3/2) k = {math.sqrt(1.5) * k:.5f} = {math.sqrt(1.5) * k * De:.3f}/Delta")
for name, (m1, m2, m3) in {"up": (up, charm, top), "down": (down, strange, bottom),
                           "electron": (e, mu, tau)}.items():
    print(f"{name:8s} m2/m3 = {m2 / m3:.5f} = {m2 / m3 * De:.3f}/Delta;  "
          f"m1/m2 = {m1 / m2:.6f} = {m1 / m2 * De:.3f}/Delta = {m1 / m2 * De**2:.2f}/Delta^2")
