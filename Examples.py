lp.lapy(r"""
$\m{Pos}=[x\le x, x\le y\And y\le x\implies x=y, x\le y\And y\le z\implies x\le z]$

$\m{PoMag}=\m{Pos}+[x\le y\And z\le w\implies x\cdot z\le y\cdot w]$

$\m{NPoMag}=\m{Pos}+[x\le y\And z\le w\implies x\cdot z\le y\cdot w]+[x\le y\implies -y\le -x]$

$\m{P21}=[0\le 1, \Not 0\le 2, \Not 2\le 0, \Not 1\le 2, \Not 2\le 1]$

$\Mod(\m{PoMag}+\m{P21}+[(x\cdot y)\cdot z=x\cdot(y\cdot z), x\cdot e=x, e\cdot x=x],3)?$
""")
