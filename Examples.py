l.l(r"""
$\m{Pos}=[x\le x, x\le y\And y\le x\implies x=y, x\le y\And y\le z\implies x\le z]$

$\m{PoMag}=\m{Pos}+[x\le y\And z\le w\implies x\cdot z\le y\cdot w]$

$\m{NPoMag}=\m{Pos}+[x\le y\And z\le w\implies x\cdot z\le y\cdot w]+[x\le y\implies -y\le -x]$

The following list defines the fundamental operations of partially ordered algebras
and their tonicity, i.e., whether they are order preserving or order reversing in
each argument.

$\s{prime}=[x\le y\implies y'\le x']$

$\s{inverse}=[x\le y\implies y^{-1}\le x^{-1}]$

$\s{neg}=[x\le y\implies \neg y\le \neg x]$

$\s{sim}=[x\le y\implies \sim y\le \sim x]$

$\s{negative}=[x\le y\implies -y\le -x]$

$\s{diamond}=[x\le y\implies f(x)\le f(y)]$

$\s{box}=[x\le y\implies g(x)\le g(y)]$

$\s{cdot}=[
  x\le y\implies x\cdot z\le y\cdot z,
  x\le y\implies z\cdot x\le z\cdot y]$

$\s{backslash}=[
  x\le y\implies y\backslash z\le x\backslash z,
  x\le y\implies z\backslash x\le z\backslash y]$

$\s{slash}=[
  x\le y\implies x/z\le y/z,
  x\le y\implies z/y\le z/x]$

$\s{minus}=[
  x\le y\implies x-z\le y-z,
  x\le y\implies z-y\le z-x]$

$\s{plus}=[
  x\le y\implies x+z\le y+z,
  x\le y\implies z+x\le z+y]$

$\s{vee}=[
  x\le y\implies x\vee z\le y\vee z,
  x\le y\implies z\vee x\le z\vee y]$

$\s{wedge}=[
  x\le y\implies x\wedge z\le y\wedge z,
  x\le y\implies z\wedge x\le z\wedge y]$

$\s{to}=[
  x\le y\implies y\to z\le x\to z,
  x\le y\implies z\to x\le z\to y]$



Now comes a list of basic (quasi)(in)equational properties
from which theories of (po-)algebras are constructed.

$\s{A} = [(x\cdot y)\cdot z=x\cdot(y\cdot z)]$ associative cdot

$\s{Ap} = [(x+y)+z=x+(y+z)]$ associative plus

$\s{U} = [x\cdot 1=x, 1\cdot x=x]$ unital cdot

$\s{Up} = [x+0=x, 0+x=x]$ unital plus

$\s{Inv} = [x\cdot x^{-1}=1]$ right inverse cdot

$\s{Invp} = [x+ -x=0]$ right inverse for plus

$\s{C} = [x\cdot y=y\cdot x]$ commutative cdot

$\s{Cp} = [x+y=y+x]$ commutative plus

$\s{IP} = [x^{-1}\cdot(x\cdot y)=y, y=(y\cdot x)\cdot x^{-1}]$ inverse property (from loop theory)

$\s{Me} = [(x^{-1})^{-1}=x, x\cdot(x\cdot x^{-1})=x]$ meadow identities

$\s{Dcp} = [x\cdot(y+z)=x\cdot y+x\cdot z, (x+y)\cdot z=x\cdot z+y\cdot z]$ distributivity of cdot over plus

$\s{Id} = [x\cdot x=x]$ idempotent

$\s{Aw} = [(x\wedge y)\wedge z=x\wedge (y\wedge z)]$ associative wedge

$\s{Av} = [(x\vee y)\vee z=x\vee(y\vee z)]$ associative vee

$\s{Cw} = [x\wedge y=y\wedge x]$ commutative wedge

$\s{Cv} = [x\vee y=y\vee x]$ commutative vee

$\s{Abs} = [(x\wedge y)\vee x=x, (x\vee y)\wedge x=x]$ absorption laws

$\s{L}= \s{Aw}+\s{Av}+\s{Cw}+\s{Cv}+\s{Abs}$ lattice-ordered

$\s{Mo} = [x\wedge(y\vee (x\wedge z))=x\wedge y\vee x \wedge z]$ modular

$\s{Dwvl} = [x\wedge(y\vee z)=(x\wedge y)\vee (x\wedge z)]$ distributivity of wedge over vee left

$\s{Dvwl} = [x\vee(y\wedge z)=(x\vee y)\wedge x\vee z]$ distributivity of vee over wedge left

$\s{Dwvr} = [(x\vee y)\wedge z=(x\wedge z)\vee (y\wedge z)]$ distributivity of wedge over vee right

$\s{Dvwr} = [(x\wedge y)\vee z=(x\vee z)\wedge y\vee z]$ distributivity of vee over wedge right

$\s{Dm} = [(x\wedge y)'=x'\vee y', x''=x]$ De Morgan

$\s{Co} = [x\wedge x'=0, x\vee x'=1]$ complemented

$\s{b} = [x\wedge 0=0, x\vee 1=1]$ bounded

$\s{H} = [x\wedge y\le z\iff y\le x\to z]$ Heyting adjunction

$\s{B} = [(x\to 0)\to 0=x]$ Boolean

$\s{Lr} = [x\cdot y\le z\iff y\le x\backslash z]$ left residuated

$\s{I} = [x\vee 1=1]$ integral

$\s{R} = [x\le z/y\iff x\cdot y\le z\iff y\le x\backslash z]$ residuated

$\s{Insl} = [0/(x\backslash 0)=(0/x)\backslash 0]$ involutive for slashes

$\s{In} = [x\le -(y\cdot \sim z)\iff x\cdot y\le z\iff y\le \sim(-z\cdot x)]$ involutive

$\s{Adj} = [x\le \Box\Diamond x, \Diamond\Box x\le x]$ adjunction

$\s{Ga} = [x\le \sim-x, x\le -\sim x]$ Galois connection

$\s{dG} = [\sim-x\le x, -\sim x\le x]$ dual Galois connection



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
Some basic theories of algebras.

$\m{Set} = [x=x]$ sets (no operations)

$\m{O} = [x=y]$ one element sets 

$\m{Mag} = [x\cdot x=x\cdot x]$ magmas 

$\m{Sgrp} = \s{A}$ semigroups

$\m{Bnd} = \s{Id}+\m{Sgrp}$ bands

$\m{Slat} = \s{C}+\m{Bnd}$ semilattices

$\m{Mon} = \s{U}+\m{Sgrp}$ monoids

$\m{CMonp} = \s{Ap}+\s{Cp}+\s{Up}$ commutative monoids with +,0

$\m{IPLoop} = \s{IP}+\s{U}+\m{Mag}$ IP-loops

$\m{Grp} = \s{Inv}+\m{Mon}$ groups

$\m{AbGrp} = \s{C}+\m{Grp}$ abelian groups

$\m{AbGrpp} = \s{Invp}+\m{CMonp}$ abelian groups with +, -, 0

$\m{Srng} = \s{Ap}+\s{Cp}+\s{Dcp}+\m{Sgrp}?$ semirings

$\m{Ring} = \s{Up}+\s{Invp}+\m{Srng}?$ rings

$\m{SkMead} = \s{Me}+\s{U}+\m{Ring}?$ skew meadows (= skew fields with $0^{-1}=0$)

$\m{Mead} = \s{C}+\m{SkMead}$ meadows



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
Some basic theories of lattice-ordered algebras.

$\m{Lat} = \s{L}$ lattices

$\m{iLat} = \s{Dm}+\m{Lat}$

$\m{OL} = \s{Co}+\m{iLat}$

%$\m{OmL} = \s{Om}+\m{OL}$

$\m{HA} = \s{b}+\s{H}+\m{Lat}$

$\m{BA} = \s{B}+\m{HA}$

$\m{LrL} = \s{Lr}+\s{L}+\m{Mon}$

%$\m{LGrp} = \s{}$

$\m{RL} = \s{R}+\s{L}+\m{Mon}$

$\m{FL} = \m{RL}$+[0=0]



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
Some basic theories of partially ordered algebras.

These theories have to add the tonicity formulas (unless they are known to follow from other properties).

$\m{Pos}=[
  x\le x, \newline
  x\le y\ \s{and}\ y\le x\implies x=y, \newline
  x\le y\ \s{and}\ y\le z\implies x\le z]$ partially ordered sets

$\s{lub}=\s{vee}+[x\le x\vee y,x\le y\vee x,x\vee x\le x]$ least upper bound

$\m{Jslat}=\m{Pos}+\s{lub}$ join-semilattices

$\s{glb}=\s{wedge}+[x\wedge y\le x,x\wedge y\le y,x\le x\wedge x]$ greatest lower bound

$\m{Mslat}=\m{Pos}+\s{glb}$ meet-semilattices

$\m{leLat}=\m{Pos}+\s{lub}+\s{glb}?$ lattices defined by the partial order le

$\m{bleLat}=\m{leLat}+[\bot\le x,x\le\top]$ bounded lattices

$\m{GaPos} = \m{Pos}+\s{sim}+\s{negative}+\s{Ga}$ Galois connection

$\m{ImPos} = \m{Pos}+\s{to}+[x\to x=x\to x]$ implicative poset

$\m{BCK} = \m{ImPos}$ BCK-po-algebras

$\m{RPoSgrp} = \m{Pos}$ residuated po-semigroups

$\m{RPoMon} = \m{Pos}$ residuated po-monoids

$\m{ipoMon} = \m{Pos}$ involutive (residuated) po-monoids

$\m{PrGrp} = \m{Pos}$ pregroups as po-algebras

$\m{MV} = \m{Pos}$ MV-po-algebras



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
Some (random) examples to test a few things.

$B=\Mod(\m{Jslat},3)?$

$show(B)$

$C = (\m{Grp}\nvdash x\cdot y=y\cdot x)?$

$C\models x\cdot y=e \implies y=x^{-1}?$

$\m{Grp}\vdash e\cdot x=x?$

$S = \{1,\dots,51\}?$

$\{x\in S \mid 2\vert x\}?$

$L=\Mod(\m{leLat},4)?$

$C=\Con(L_2)?$

$show(C)$

$P=\Pre(L_2)?$

$show(P)$

$\m{CyInLat}=\m{Lat}+[x\le y \implies y'\le x', x''=x]$ cyclic involutive lattices

$\m{CyInLat}?$ cyclic involutive lattices

$\m{CyInRL}=\m{Lat}+[x\le y \implies -y\le -x, --x=x]$ cyclic involutive lattices
""")
