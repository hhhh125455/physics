"""Reproduce two 1000-step TTbar-saddle Lanczos tables and emit Lean certificate.
Numerical convergence is NOT a formal bound on continuum quadrature error.
"""
from pathlib import Path
import argparse, math
import numpy as np
from scipy.linalg import eigh_tridiagonal
from scipy.special import i1e, logsumexp

C=120.
BETA=math.pi
MU=1/400
A=math.pi**2*C/3
K=2*math.sqrt(MU*A)
D=math.sqrt(BETA**2-K**2)
R=BETA-K
ALPHA=1/(2*MU)
F=(BETA-D)/(2*MU)

def laguerre_logweights(t):
    n=len(t)
    prev=np.zeros(n); cur=np.ones(n); scale=np.zeros(n)
    for j in range(n-1):
        nxt=((2*j+1-t)*cur-j*prev)/(j+1)
        prev,cur=cur,nxt
        mag=np.maximum(abs(prev),abs(cur))
        hi=mag>1e100; lo=(mag<1e-100)&(mag>0)
        prev[hi]*=1e-100;cur[hi]*=1e-100;scale[hi]+=math.log(1e100)
        prev[lo]*=1e100;cur[lo]*=1e100;scale[lo]-=math.log(1e100)
    return np.log(t)-2*math.log(n)-2*(np.log(abs(cur))+scale)

def discrete_measure(n):
    j=np.arange(n,dtype=float)
    t=eigh_tridiagonal(2*j+1,j[1:],eigvals_only=True,check_finite=False)
    E=t/R
    y=np.sqrt(E*(E+2*ALPHA))
    logcont=(laguerre_logweights(t)+np.log(ALPHA*K/y)
        +np.log(i1e(K*y))+K*(y-E)-math.log(R)-F)
    nodes=np.r_[0.,E]
    lw=np.r_[-F,logcont]
    assert abs(math.exp(logsumexp(lw))-1)<1e-8
    return nodes,lw

def lanczos(n,nodes,lw):
    lw=lw-logsumexp(lw)
    prev_s=np.zeros(len(nodes));cur_s=np.ones(len(nodes))
    prev_l=np.zeros(len(nodes));cur_l=np.zeros(len(nodes))
    a=np.zeros(n+1);b=np.zeros(n+1)
    for j in range(n+1):
        z=lw+2*cur_l
        z-=np.max(z)
        w=np.exp(z)
        a[j]=np.dot(nodes,w)/sum(w)
        if j==n:break
        dx=nodes-a[j]
        with np.errstate(divide='ignore',invalid='ignore'):
            s1=np.sign(dx)*cur_s
            l1=np.where(s1!=0,np.log(abs(dx))+cur_l,-np.inf)
            s2=-prev_s
            l2=np.where(s2!=0,math.log(b[j])+prev_l,-np.inf) if j>0 else np.full(len(dx),-np.inf)
        m=np.maximum(l1,l2)
        m=np.where(np.isfinite(m),m,-1e300)
        v=s1*np.exp(l1-m)+s2*np.exp(l2-m)
        sn=np.sign(v)
        with np.errstate(divide='ignore',invalid='ignore'):
            ln=np.where(sn!=0,m+np.log(abs(v)),-np.inf)
        normlog=0.5*logsumexp(lw+2*ln)
        b[j+1]=math.exp(normlog)
        prev_s,cur_s=cur_s,sn
        prev_l,cur_l=cur_l,ln-normlog
    return a,b

def lean_array(name,data):
    lines=['def '+name+' : Array Nat := #[']
    for j in range(0,len(data),20):
        part=', '.join(str(int(x)) for x in data[j:j+20])
        lines.append('  '+part+(',' if j+20<len(data) else ''))
    lines.append(']')
    return '\n'.join(lines)

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--out',type=Path,default=Path('TTbar-TFD-Spread/generated'))
    args=p.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    aa,ab=lanczos(1000,*discrete_measure(2000))
    ba,bb=lanczos(1000,*discrete_measure(4500))
    assert max(abs(ba[0]-(BETA/D-1)/(2*MU)),abs(bb[1]**2-2*A/D**3))<3e-7
    arrays={}
    for name,seq in [('a2000',aa),('b2000',ab),('a4500',ba),('b4500',bb)]:
        arrays[name]=np.rint(seq[1:]*1_000_000).astype(np.int64)
    assert max(abs(arrays['a2000']-arrays['a4500']).max(),
               abs(arrays['b2000']-arrays['b4500']).max())<=1
    code=['import Mathlib','namespace TTbarLanczosNumericalCertificate']
    for name,data in arrays.items():
        code.append(lean_array(name,data))
    code += [
      'theorem lengths : a2000.size = 1000 ∧ b2000.size = 1000 ∧ a4500.size = 1000 ∧ b4500.size = 1000 := by native_decide',
      'theorem every_index_converged : ∀ i : Fin 1000,',
      ' a2000[i.val]! ≤ a4500[i.val]! + 1 ∧ a4500[i.val]! ≤ a2000[i.val]! + 1 ∧',
      ' b2000[i.val]! ≤ b4500[i.val]! + 1 ∧ b4500[i.val]! ≤ b2000[i.val]! + 1 := by native_decide',
      'theorem every_index_positive : ∀ i : Fin 1000,',
      ' 0 < a4500[i.val]! ∧ 0 < b4500[i.val]! := by native_decide',
      'theorem every_index_monotone : ∀ i : Fin 999,',
      ' a4500[i.val]! < a4500[i.val+1]! ∧ b4500[i.val]! < b4500[i.val+1]! := by native_decide',
      'theorem endpoint : a4500[999]! = 1754957363 ∧ b4500[999]! = 877049613 := by native_decide',
      'end TTbarLanczosNumericalCertificate']
    target=args.out/'18_N1000LeanCertificate.lean'
    target.write_text('\n'.join(code)+'\n')
    print('max absolute a,b difference',float(np.max(abs(aa-ba))),float(np.max(abs(ab-bb))))
    print('n1000 a,b',ba[1000],bb[1000])
    print('generated Lean certificate',target)
if __name__=='__main__':main()
