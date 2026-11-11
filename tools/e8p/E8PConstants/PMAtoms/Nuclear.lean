import PMAtoms.NuclearGraph
import PMAtoms.NuclearLine
import PMAtoms.NuclearCharge

/-!
# Nuclear-graph diagnostic

The typed link counts are computed from `PMAtoms.NuclearGraph`; the He-4
closure gap is the frozen mass-data comparison from `NuclearBinding`, not a
fitted weight.
-/

namespace E8PConstants

def nuclearTable : List String :=
  let h3 := PMAtoms.h3Label
  let he3 := PMAtoms.he3Label
  let he4 := PMAtoms.he4Label
  let c12 := PMAtoms.lineCounts 6 6
  let o16 := PMAtoms.lineCounts 8 8
  [
    "nuclear graph diagnostic",
    "counts are proved in PMAtoms.NuclearGraph; closure gap is the frozen mass comparison",
    s!"H-3   Z=1 N=2 A=3  pp={PMAtoms.completeEdgeCount h3 .pp} pn={PMAtoms.completeEdgeCount h3 .pn} nn={PMAtoms.completeEdgeCount h3 .nn}  tetrahedron=no",
    s!"He-3  Z=2 N=1 A=3  pp={PMAtoms.completeEdgeCount he3 .pp} pn={PMAtoms.completeEdgeCount he3 .pn} nn={PMAtoms.completeEdgeCount he3 .nn}  tetrahedron=no",
    s!"He-4  Z=2 N=2 A=4  pp={PMAtoms.completeEdgeCount he4 .pp} pn={PMAtoms.completeEdgeCount he4 .pn} nn={PMAtoms.completeEdgeCount he4 .nn}  tetrahedron=yes  closure gap=0.012985 u",
    "",
    "line/ring + alpha-diagonal counts (PMAtoms.NuclearLine):",
    s!"C-12  pp={c12.1} pn={c12.2.1} nn={c12.2.2}",
    s!"O-16  pp={o16.1} pn={o16.2.1} nn={o16.2.2}",
    "",
    "static charge energy (Paper II Green's function, Paper III Q):",
    "H-3  3/4 = 0.75   (chargeEnergy3_H3)",
    "He-3 11/4 = 2.75  (chargeEnergy3_He3)",
    "He-4 16/5 = 3.20  (chargeEnergy4_He4)",
    "mirror difference He-3 - H-3 = 2 kernel units",
    "",
    "The H-3/He-3 mirror fixes w_nn - w_pp = 0.000820 u; He-4 needs the 4-body closure."
  ]

end E8PConstants
