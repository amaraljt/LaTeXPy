# LaTeXPy

The aim of this project is to use LaTeX as a high-level mathematical calculator syntax 
that can be used in undergraduate education by students who know or learn some basic LaTeX, 
but they should not need to know any Python.

The file LaTeXPy.py contains experimental code that parses LaTeX math expressions (enclosed 
by $ or $$) and (attempts to) translate them to valid Python code. This code is evaluated by 
Python and the resulting value (if any) is inserted into the LaTeX file. If the math expression
is an assignment, the value of the right hand side is assigned to a Python variable with
a similar name and can be used in subsequent LaTeX expressions.

The following design principles are part of this project:

1. The LaTeX input is written in a standard way close to what most users would expect, without the use of macros.
2. Input and output can be copy-pasted from and to standard LaTeX documents.
3. LaTeXPy is intended to be used in a Jupyter notebook environment. It makes use of the display module (for LaTeX and Markdown) and the graphviz module (for graphs and Hasse diagrams).
4. The parser does not require a parser generator. Local modifications and extensions should be fairly easy to make for someone familiar with Python.
5. The LaTeX interface connects with automated theorem provers and model finders (currently Prover9/Mace4). Future syntax extensions may include other provers, SMT-solvers and mathematical Python modules like SymPy and NumPy.

The current version of LaTeXPy.py is experimental and intended to get feedback on design decisions.
The input language covers an interesting fragment of discrete mathematics (including finite sets 
and first-order logic), but the syntax is still evolving and incorrect input currently does not 
produce useful error messages.

Below are some examples of what is covered (they can be copy-pasted as input). A question mark after an expression is a request to evaluate the expression and insert the result in the typeset output (colored blue). Expressions with a top-level equal sign and a variable on the left are interpreted as assignments that get executed by Python. Input that was parsed and evaluated without error appears in green, and all other expressions (without ? or = or that generated errors) as well as text outside of $...$ math regions appear in black.

The main function of the code is called lapy(...) and takes a r"""raw string""" as input, with some options for diagnostic output and pure LaTeX output with or without color coding.

The following lines install LaTeXPy in a https://colab.research.google.com Jupyter notebook cell (copy-paste them). You need a gmail account to use this free Colab(orative) Jupyter notebook. (LaTeXPy should work in any Jupyter notebook, but the file LaTeXPy may need to be copied manually and modified slightly. Using it via Colab ensures you have the latest version, but does require an internet connection.)
```
!rm -rf LaTeXPy #remove any previous version
!git clone https://github.com/jipsen/LaTeXPy.git
import sys; sys.path.append('/content/LaTeXPy'); import LaTeXPy as lp
```
Here are some examples
```
lp.P9=False
lp.lapy(r"""
Arithmetic expressions are written in calculator style, e.g., $1+2*4/4^2 ?$. 
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


