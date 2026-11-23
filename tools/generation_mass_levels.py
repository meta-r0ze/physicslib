"""Generation-mass pattern at the carrier level and through the Dirac-wall seesaw (no data).

Generation g (label g) has class g+1 on wall 1 and g-1 on wall 2 (PMAction.GenerationWalls.side).
The equal-class crossing of class c joins wall 1 of generation c-1 to wall 2 of generation c+1
(PMAction.InterWallDiagonal), with amplitude amp[c]. The reference class v = 0 crosses in-cycle
(amplitude 1); the two spinor classes touch the reference axis and pass the node, two legs for
colour carriers: amplitude alpha (PMFlavor.NodeElimination, PMFlavor.ExchangeAxis).

* Carrier level (PMAction.WallTransfer: the crossing is the mass bilinear): masses are the
  crossing's singular values, the class amplitudes: 1 : 1 : 1/alpha. One heavy, two light.
* Dirac-wall seesaw (PMAction.WallSeesaw, the crossing on the gapped components, components a,b,c,d):
  one light and two heavy, both for a flavour-blind on-site detuning and for a label insertion.
So the seesaw gives the opposite pattern; MassInsertion's CKM ordering excludes it too.
"""
import numpy as np
def Y(amp):
    M=np.zeros((3,3))
    for c in range(3): M[(c-1)%3,(c+1)%3]=amp[c]
    return M
def seesaw_light(Ym,D):
    Z=np.zeros((3,3))
    H=np.block([[Z,D,Z,Z],[D,Z,-Ym,Z],[Z,-Ym.T,Z,D],[Z,Z,D,Z]])
    return np.sort(np.sort(np.abs(np.linalg.eigvalsh(H)))[:6:2])
alpha=1/137.035999177; eps=0.1
for name,D in [('seesaw, flavour-blind detuning',np.eye(3)*0.05),('seesaw, label insertion',np.diag([0.05,0.05*eps,0.05*eps]))]:
    m=seesaw_light(Y([1,alpha,alpha]),D); print(name,': masses / lightest =',np.round(m/m[0],3))
sv=np.sort(np.linalg.svd(Y([1,alpha,alpha]),compute_uv=False)); print('carrier level: masses / lightest =',np.round(sv/sv[0],3))
