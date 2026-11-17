"""Does the other wall's flip program disturb a protocol label? (EP REVIEW, Toll and register.)

In the register reading a wall's label is a carrier of the other wall's D4 factor. PMAction's flip
program is class-blind: exp(i theta beta) on the odd sector and 1 on the even sector of every class of
its factor. Applied to label carriers at a certain flip (theta = pi/2): every label is disturbed by the
same amount (stays with 1/4 in classes v and c, 1/2 in class s), so the disturbance cannot give
per-protocol weights; and in classes v and c it moves lepton labels onto colour labels, which breaks
colour. So a wall's flip must not reach the other wall's labels.
"""
import itertools, numpy as np
h=0.5
V=[np.array([s*(i==j) for j in range(4)],float) for i in range(4) for s in (1,-1)]
S=[np.array(p) for p in itertools.product((h,-h),repeat=4) if sum(x<0 for x in p)%2==0]
C=[np.array(p) for p in itertools.product((h,-h),repeat=4) if sum(x<0 for x in p)%2==1]
cls={'v':V,'s':S,'c':C}
B=np.array([[0,0,1,0],[0,0,0,1],[1,0,0,0],[0,1,0,0]],float)
def name(w,frame):
    # protocol of a label: lepton axis 0; vector frame: axis/sign; spinor frame: via x0 and S
    if frame=='v':
        ax=int(np.argmax(abs(w))); sg=w[ax]>0
        return ('nu' if sg else 'e') if ax==0 else (('u' if sg else 'd')+str(ax))
    x0=w[0]>0; Ssum=w[1:].sum()
    if abs(Ssum)>1: return 'nu' if x0 else 'e'
    return 'u' if x0 else 'd'
th=np.pi/2
for k,X in cls.items():
    idx={tuple(w):i for i,w in enumerate(X)}
    P=np.zeros((8,8)); A=np.zeros((8,8))
    for j,w in enumerate(X): P[idx[tuple(B@w)],j]=1; A[idx[tuple(-w)],j]=1
    odd=(np.eye(8)-A)/2; even=(np.eye(8)+A)/2
    U=np.eye(8)+ (np.exp(1j*th)*P-np.eye(8))@odd   # exp(i th beta) on odd, 1 on even  (beta odd = P odd)
    U=even+ (np.cos(th)*np.eye(8)+1j*np.sin(th)*P)@odd
    out=[]
    for j,w in enumerate(X):
        col=U[:,j]; stay=abs(col[j])**2
        dest={name(X[i],k):round(abs(col[i])**2,3) for i in range(8) if abs(col[i])>1e-9 and i!=j}
        out.append((name(w,k),round(stay,3),dest))
    print(k,out)
