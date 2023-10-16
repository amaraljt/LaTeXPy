# LaTeXPy Setup Instructions
It is recommended to use this code in a Colab Jupyter notebook freely available at 
https://colab.research.google.com (use a free gmail account to login to Colab).

**Step 1:** Click on the link above, and start a new Colab notebook (use **File->New notebook** on the webpage menu, **not** on your computer menu).

**Step 2:** Copy the following lines into the first notebook cell and click the red start button to install LaTeXPy. This takes a few seconds since it installs `latex2sympy2` on the colab server (nothing is installed or modified on your computer).
```
!rm -rf LaTeXPy #remove any previous version
!git clone https://github.com/amaraljt/LaTeXPy.git
execfile("/prototype/PsuedocodePy.py")
```
**Step 3:** Copy some of the examples below to see how to do various calculations using the LaTeX syntax that is valid with this script.

The main function of the code is called `l(...)` and takes a LaTeX **r"""raw string"""** as input. (A **rawstring** in Python starts with r" and in such strings the backslash is an ordinary character. The triple-quotes """ are used for strings that extend over several lines. If something doesn't work it may help to add a second input in the form `l(rawstring, 1)` then some diagnostic output is printed as well.)

Below are some example of what is covered (can be copy-pasted as input ). A **question mark** after an expression is a request to evaluate the expression and insert the result in the typeset output (colored **blue**). Expressions with a **top-level equal sign and a variable on the left** are interpreted as assignments that get executed by Python. Input that was parsed and evaluated without error appears in **green**, and all other expressions (without ? or =, or that generated errors) as well as text outside of $...$ math regions appear in black.
