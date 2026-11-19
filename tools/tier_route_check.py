#!/usr/bin/env python3
"""Comparison only: arithmetic on the normalized bare wire and declared tier ledger."""
import math

dimension, symmetry, euler, delta, channels = 4, 5, 2, 43, 16
resolution = dimension * delta
eta = (resolution - 1) / resolution
gap = resolution - symmetry
load = channels + symmetry + euler + 2 * dimension
# PMSubstrate.geometricIndex and PMConstants.Values.alpha
impedance = (
    math.pi * delta + euler - 1 / gap - euler / delta
    + euler * gap / ((2 * channels)**3 * symmetry * resolution)
    + 1 / (load * (symmetry + 1) * delta**2)
)
alpha = 1 / impedance
k = alpha / 2
wire_ratio = math.sqrt(3) * k / math.sqrt(2 + k * k)

up = dimension / eta
down = (dimension + symmetry) / eta
strange = (dimension * delta + euler * symmetry) / eta
charm = dimension * delta**2 / (eta * (symmetry - euler))
bottom = delta**2 * (dimension + euler / symmetry) / eta
top = delta**3 * (dimension + 1 / dimension)
electron = 1.0  # Ledger units of m_e.
muon = symmetry * delta - euler - 2 * math.pi + (euler + symmetry) * alpha / (1 - alpha)
tau = euler * delta**2 - symmetry * delta - (dimension + euler)

print("Comparison only: normalized bare wire and declared tier formulas.")
print(f"bare wire m2/m3 = {wire_ratio:.5f} = {wire_ratio * delta:.3f}/Delta")
for name, (m1, m2, m3) in {
    "up": (up, charm, top),
    "down": (down, strange, bottom),
    "electron": (electron, muon, tau),
}.items():
    print(f"{name:8s} m2/m3 = {m2 / m3:.5f} = {m2 / m3 * delta:.3f}/Delta;  "
          f"m1/m2 = {m1 / m2:.6f} = {m1 / m2 * delta:.3f}/Delta = "
          f"{m1 / m2 * delta**2:.2f}/Delta^2")
