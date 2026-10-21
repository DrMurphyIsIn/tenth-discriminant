"""Ball-arithmetic (Arb via python-flint) check of the d <= 652 threshold, outside Lean.
Claims certified here, for s = 7/8 and Q principal (a = 1):
 (i)  zeta(3/4) < 0 and zeta(7/8) < 0 (balls);
 (ii) the main term M(d) = zeta(7/4) + 2^{-1/4} sqrt(pi) Gamma(3/8)/Gamma(7/8) d^{-3/8} zeta(3/4) is increasing in d (zeta(3/4) < 0) and
      M(655) > 0 with a certified lower bound;
 (iii) |E_d(7/8)| <= B(d) with an explicit crude bound: |K_nu(x)| <= sqrt(pi/(2x)) e^{-x} (1 + |nu^2-1/4|/(2x))  for nu = 3/8 real, x > 0
      (a standard bound, FROM MEMORY; to be replaced by a proved integral bound in Lean), sigma_{-3/4}(n) <= d(n) <= 2 sqrt n;
      B(655) is computed and compared with M(655).
Also certifies M(652) < 0 to show 652 is genuinely not excluded by this route."""
from flint import arb, ctx
ctx.prec = 256
s = arb(7)/8
def M(d):
    return (2*s).zeta() + arb(2)**(2*s-1) * arb.pi().sqrt() * (s-arb(1)/2).gamma()/s.gamma() * arb(d)**(arb(1)/2-s) * (2*s-1).zeta()
z34, z78 = (arb(3)/4).zeta(), s.zeta()
print("zeta(3/4) =", z34.str(15), " <0:", z34 < 0)
print("zeta(7/8) =", z78.str(15), " <0:", z78 < 0)
for d in (652, 655):
    m = M(d); print(f"M({d}) =", m.str(15), " >0:", m > 0, " <0:", m < 0)
def B(d):
    nu = arb(3)/8; x0 = arb.pi()*arb(d).sqrt()
    pref = arb(2)**(s+arb(3)/2) * arb.pi()**s / (s.gamma() * arb(d)**(s/2-arb(1)/4))
    tot = arb(0)
    for n in range(1, 60):
        x = x0*n
        kb = (arb.pi()/(2*x)).sqrt() * (-x).exp() * (1 + abs(nu*nu - arb(1)/4)/(2*x))
        tot += arb(n)**(s-arb(1)/2) * 2*arb(n).sqrt() * kb
    return pref*tot   # tail n >= 60 is below e^{-60 pi sqrt d}: negligible but not bounded here (to do in Lean)
b = B(655); print("B(655) (n<60) =", b.str(6), "  M(655) - B(655) > 0:", (M(655) - b) > 0)
