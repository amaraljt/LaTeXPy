# LaTeXPy

The aim of this project is to use LaTeX as a high-level mathematical calculator syntax 
that can be used in undergraduate education by students who know or learn some basic LaTeX, 
but they should not need to know any Python.

The file LaTeXPy.py contains experimental code that parses LaTeX math expressions (enclosed 
by $ or $$) and (attempts to) translate them to valid Python code. This code is evaluated by 
Python and the resulting value (if any) is inserted into the LaTeX file. If the math expression
is an assignment, the value of the right hand side is assigned to a Python variable with
a similar name and can be used in subsequent LaTeX expressions.

It is recommended to use this code in a Colab Jupyter notebook freely available at 
https://colab.research.google.com (use a free gmail account to login to Colab).

**Step 1:** Click on the link above, and start a new Colab notebook (use **File->New notebook** on the webpage menu, **not** on your computer menu).

**Step 2:** Copy the following lines into the first notebook cell and click the red start button to install LaTeXPy. This takes about 30 seconds since it installs the Prover9 theorem prover on the Google server (nothing is installed on your computer).
```
!rm -rf LaTeXPy #remove any previous version
!git clone https://github.com/jipsen/LaTeXPy.git
import sys; sys.path.append('/content/LaTeXPy'); import LaTeXPy as l
```
**Step 3:** Copy some of the examples below to see how to do various calculations using the LaTeX syntax that is valid with this script.

The main function of the code is called `lp.lapy(...)` and takes a **r"""raw string"""** as input. (If something doesn't work it may help to add a second input in the form `lp.lapy(rawstring, 1)` then some diagnostic output is printed as well.)

Here is a (longer) example about small po-algebras that were chosen during a LIACT summer research school at the University of Johannesburg (Jan 3-13, 2023). Shorter examples are further below.
```
l.m(r"""
\m{Pos}=[
  x\le x, \newline
  x\le y \And y\le x\implies x=y,\newline
  x\le y \And y\le z\implies x\le z]

\s{cdot} = [x\le y\implies x\cdot z\le y\cdot z, x\le y\implies z\cdot x\le z\cdot y]

A = \Mod(\m{Pos}+\s{cdot}+
[0\le 1, 0\nleq 2, 2\nleq 0, 1\nleq 2, 2\nleq 1, -0=2, -1=2, -2=0,
(x\cdot y)\cdot z = x\cdot(y\cdot z), 
x\cdot y = y\cdot x, 
x\cdot x=x], 3)

|A|?

Grape = A_1?

B = \Mod(\m{Pos}+\s{cdot}+
[0\le 1, 0\nleq 2, 2\nleq 0, 1\nleq 2, 2\nleq 1, -0=1, -1=0, -2=2,
(x\cdot y)\cdot z = x\cdot(y\cdot z), 
x\cdot x=x, 0\cdot 2=2], 3)

Gondar = B_0?

C = \Mod(\m{Pos}+\s{cdot}+
[0\le 1, 0\nleq 2, 2\nleq 0, 1\nleq 2, 2\nleq 1, -0=1, -1=0, -2=2,
(x\cdot y)\cdot z = x\cdot(y\cdot z), 
x\cdot y = y\cdot x, 
x\cdot x=x], 3)

Joburg = C_0?

D = \Mod(\m{Pos}+\s{cdot}+
[0\le 1, 0\nleq 2, 2\nleq 0, 1\nleq 2, 2\nleq 1, -0=1, -1=0, -2=2,
0\cdot 0=2,1\cdot 0=2,2\cdot 0=2,0\cdot 1=2,1\cdot 1=2,2\cdot 1=2,1\cdot 1=2, 2\cdot 2=1], 3)

Saturn = D_1?

E = \Mod(\m{Pos}+
[0\le 1, 0\nleq 2, 2\nleq 0, 1\nleq 2, 2\nleq 1, -0=1, -1=0, -2=2,
0\cdot 0=1,1\cdot 0=0,2\cdot 0=2,0\cdot 1=0,1\cdot 1=0,2\cdot 1=2,0\cdot 2=2, 1\cdot 2=2], 3)

CIMPA = E_2?

show(\Pre([Grape,Gondar,Joburg,Saturn,CIMPA]))
""")
```

The following design principles are part of this project:

1. The LaTeX input is written using standard mathematical/logical notation.
2. Input and output can be copy-pasted from and to standard LaTeX documents.
3. LaTeXPy is intended to be used in a Jupyter notebook environment. It makes use of the display module (for LaTeX and Markdown) and the graphviz module (for graphs and Hasse diagrams).
4. The parser does not require a parser generator. Local modifications and extensions should be fairly easy to make for someone familiar with Python.
5. The LaTeX interface connects with automated theorem provers and model finders (currently Prover9/Mace4). Future syntax extensions may include other provers, SMT-solvers and mathematical Python modules like SymPy and NumPy.

The current version of LaTeXPy.py is experimental and intended to get feedback on design decisions.
The input language covers an interesting fragment of discrete mathematics (including finite sets 
and first-order logic), but the syntax is still evolving and incorrect input currently does not 
produce useful error messages.

Below are other example of what is covered (can be copy-pasted as input). A question mark after an expression is a request to evaluate the expression and insert the result in the typeset output (colored blue). Expressions with a top-level equal sign and a variable on the left are interpreted as assignments that get executed by Python. Input that was parsed and evaluated without error appears in green, and all other expressions (without ? or = or that generated errors) as well as text outside of $...$ math regions appear in black.

```
l.l(r"""
Arithmetic expressions are written in calculator style, e.g., $1+2\cdot 4/4^2 ?$. 
The '?' indicates that the answer should be inserted in the typeset output.

Sets are finite and can contain numbers, unevaluated expressions and 
other (finite) sets e.g., $A=\{2,a,b,\gamma,\delta\}?$.

Standard set-operations are available: $A\cap \{1,2,3,b\}?$, $A\cup \{1,2,3,b\}?$, 
$A\setminus \{1,2,3,b\}?$, $A\oplus \{1,2,3,b\}?$.

Ranges $\{3,\dots,10\}?$, cartesian product $\{1,2,3\}\times\{a,b\}?$.

Powerset $P=\mathcal{P}(\{1,2\})?$, cardinality $|P|?$.

A lattice of subsets can be displayed using $show(P)$ (it is shown before the rest of the output).

Lists use [...] syntax: $L=[a,b,c]$ and subscripts access elements. 
The first element is $L_0?$, and if $i=2$ then $L_i?$.
""")
```


