# LaTeXPy

## Introduction
The aim of this project is to use LaTeX as a high-level mathematical calculator syntax 
that can be used in undergraduate education by students who know or learn some basic LaTeX, 
but they should not need to know any Python.

The file LaTeXPy.py contains experimental code that parses LaTeX math expressions (enclosed 
by $ or $$) and (attempts to) translate them to valid Python code. This code is evaluated by 
Python and the resulting value (if any) is inserted into the LaTeX file. If the math expression
is an assignment, the value of the right hand side is assigned to a Python variable with
a similar name and can be used in subsequent LaTeX expressions.

## Group Members
Jared Amaral, Jose Arellano, Nathan Nguyen, Alex Wunderli

## Contributions
- Nathan Nguyen: 
  * README formatting
- Jared Amaral
  * Added coherent documentation
  * Implemented fractions, trig functions, and limits

## Setup Instructions
It is recommended to use this code in a Colab Jupyter notebook freely available at 
https://colab.research.google.com (use a free gmail account to login to Colab).

**Step 1:** Click on the link above, and start a new Colab notebook (use **File->New notebook** on the webpage menu, **not** on your computer menu).

**Step 2:** Copy the following lines into the first notebook cell and click the red start button to install LaTeXPy. This takes a few seconds since it installs `latex2sympy2` on the colab server (nothing is installed or modified on your computer).
```
!rm -rf LaTeXPy #remove any previous version
!git clone https://github.com/amaraljt/LaTeXPy.git
execfile("/content/LaTeXPy/LaTeXPy.py")
```
**Step 3:** Copy some of the examples below to see how to do various calculations using the LaTeX syntax that is valid with this script.

The main function of the code is called `l(...)` and takes a LaTeX **r"""raw string"""** as input. (A **rawstring** in Python starts with r" and in such strings the backslash is an ordinary character. The triple-quotes """ are used for strings that extend over several lines. If something doesn't work it may help to add a second input in the form `l(rawstring, 1)` then some diagnostic output is printed as well.)

Below are some example of what is covered (can be copy-pasted as input ). A **question mark** after an expression is a request to evaluate the expression and insert the result in the typeset output (colored **blue**). Expressions with a **top-level equal sign and a variable on the left** are interpreted as assignments that get executed by Python. Input that was parsed and evaluated without error appears in **green**, and all other expressions (without ? or =, or that generated errors) as well as text outside of $...$ math regions appear in black.

## Examples
```
l(r"""
Here we are using the l(...) command which requires $...$ to surround math expressions.

Arithmetic expressions are written in calculator style, e.g., $1+2\cdot 4/4^2 ?$. 
The '?' indicates that the answer should be inserted in the typeset output.
""")
```

```
l(r"""
Set comprehension has two forms: $A=\{1,\dots,100\}$, 

$\{x\in A\mid p(x)\}$ and $\{f(x)\mid x\in A\And p(x)\}$. In the second case the property $p(x)$ can also be omitted.

Use set comprehension to list the prime numbers under 100:

$\{x\in A\mid x\ne 1\And\forall {y\in A, y\vert x\implies y=1\Or y=x}\}?$
""")
```

**More examples** can be found in the Examples folder (presented as self-contained Jupyter notebooks; just copy the whole notebook and upload it into a Colab notebook at https://colab.research.google.com).

The following design principles are part of this project:

1. The LaTeX input is written using standard mathematical/logical notation.
2. Input and output can be copy-pasted from and to standard LaTeX documents.
3. LaTeXPy is intended to be used in a Jupyter notebook environment. It makes use of the display module (for LaTeX and Markdown) and the graphviz module (for graphs and Hasse diagrams).
4. The parser does not require a parser generator. Local modifications and extensions should be fairly easy to make for someone familiar with Python. Currently the `latex2sympy2` package is also used.
5. The LaTeX interface connects with automated theorem provers and model finders (currently Prover9/Mace4). Future syntax extensions may include other automated provers and SMT-solvers. *NOTE: This version of LaTeXPy does not implement model finders, Prover9 due to dependency issues.

The current version of LaTeXPy.py is experimental and intended to get feedback on design decisions.
The input language covers an interesting fragment of discrete mathematics (including finite sets, first-order logic and some `SymPy` functionality), but the syntax is still evolving and incorrect input currently does not 
produce useful error messages.
