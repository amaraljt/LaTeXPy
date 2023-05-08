# LaTeXPy

## Introduction
Latex is utilized in mathematics, physics, economics, and more as the leading text formatting language for typesetting mathematics. The interest for language lies mostly for those who wish to type mathematics in a formal, simple and clean method, allowing others to easily see documents related to math easily and clearly. Current versions of Latex, however, cannot perform operations within text, which would a useful function for calculating mathematical expressions while typsetting instead of going onto an external site. Our project extends Dr. Peter Jipsen's project and current work with the LatexPy program, and includes functionality seen in Calculus, such as derivatives, summations, integrals, limits, and trigometric functions. 

The aim of this project is to use LaTeX as a high-level mathematical calculator syntax 
that can be used in undergraduate education by students who know or learn some basic LaTeX, 
but they should not need to know any Python.

The file LaTeXPy.py contains experimental code that parses LaTeX math expressions (enclosed 
by $ or $$) and (attempts to) translate them to valid Python code. This code is evaluated by 
Python and the resulting value (if any) is inserted into the LaTeX file. If the math expression
is an assignment, the value of the right hand side is assigned to a Python variable with
a similar name and can be used in subsequent LaTeX expressions.

If you wish to see our presentation's **Google Slides**, please follow it [here](https://docs.google.com/presentation/d/1NYcR6Po-vqJWPNR_UdUPZKJZrQKUf4SI_xwPwBoXS4s/edit?usp=sharing). 

## Group Members
Jared Amaral, Jose Arellano, Nathan Nguyen, Alex Wunderli

## Contributions
- Nathan Nguyen: 
  * README formatting
  * Researched literature and related work
  * Added extra documention in code
- Jared Amaral
  * Added coherent documentation
  * Implemented fractions, trig functions, and limits
- Alex Wunderli
  * Algorithm Research and overall understanding of how parser works

## Literature Review / Related Work
* Latex Accessibility for the Visually Impaired (2018)
    - This article shows a similar proecdure of extending latex but instead they wanted to generate PDF latex documents that are accessible for the visually impaired
    - Shows the scopre of latex - latex is utilized by anyone and useful in all fields, having an accesible latex document that outputs pdfs would be extremely useful in creating mathematical textbooks for the visually impaired
    - “We have developed Axessibility, a LATEX package that generates PDF documents with braille bar and screen readeraccessible mathematical formulae. Our package is complemented with additional external scripts to assists authors during content creation and readers during document access via screen reader. Through a preliminary evaluation with 4 blind users we uncover that Axessibility is effective in making mathematical formulae accessible.”
    - Ahmetovic, D., Armano, T., Bernareggi, C., Berra, M., Capietto, A., Coriasco, S., Murru, N., Ruighi, A., & Taranto, E. (2018). Axessibility. In Proceedings of the 20th International ACM SIGACCESS Conference on Computers and Accessibility. ASSETS ’18: The 20th International ACM SIGACCESS Conference on Computers and Accessibility. ACM. https://doi.org/10.1145/3234695.3241029

* PDF2Latex (2020)
    - This article parses through a PDF document and using machine learning (neural networks), the program attempts to convert the PDF document into a latex coded document
    - This would be very beneficial for older documents that include mathematical expressions and are not created in LaTex, allowing for easy adaptability of older documents to LaTex and ability to update their contents without copying entire pages by hand
    - “In this paper, we propose a novel OCR system called PDF2LaTeX, which extracts math expressions and text in both postscript and image-based PDF files and translates them into LaTeX markup … The analysis of math expressions and text is based on a series of deep learning algorithms … “
    - Wang, Z., & Liu, J.-C. (2020). PDF2LaTeX. In Proceedings of the ACM Symposium on Document Engineering 2020. DocEng ’20: ACM Symposium on Document Engineering 2020. ACM. https://doi.org/10.1145/3395027.3419580



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

## Example
```
l(r"""
Here we are using the l(...) command which requires $...$ to surround math expressions.

Arithmetic expressions are written in calculator style, e.g., $1+2\cdot 4/4^2 ?$. 
The '?' indicates that the answer should be inserted in the typeset output.
""")
```

**More examples** can be found by going to this following [link](https://colab.research.google.com/drive/1GxquIfefMr7ifbUvcZKuXEK1ulIDkb4n?usp=sharing) to a notebook on google collab that details examples of functionality implemented by our team. The same examples can also be found in the test.ipynb file in this repository (presented as self-contained Jupyter notebooks; just copy the whole notebook and upload it into a Colab notebook at https://colab.research.google.com).


The following design principles are part of this project:

1. The LaTeX input is written using standard mathematical/logical notation.
2. Input and output can be copy-pasted from and to standard LaTeX documents.
3. LaTeXPy is intended to be used in a Jupyter notebook environment. It makes use of the display module (for LaTeX and Markdown) and the graphviz module (for graphs and Hasse diagrams).
4. The parser does not require a parser generator. Local modifications and extensions should be fairly easy to make for someone familiar with Python. Currently the `latex2sympy2` package is also used.
5. The LaTeX interface connects with automated theorem provers and model finders (currently Prover9/Mace4). Future syntax extensions may include other automated provers and SMT-solvers. *NOTE: This version of LaTeXPy does not implement model finders, Prover9 due to dependency issues.

The current version of LaTeXPy.py is experimental and intended to get feedback on design decisions.
The input language covers an interesting fragment of discrete mathematics (including finite sets, first-order logic and some `SymPy` functionality), but the syntax is still evolving and incorrect input currently does not 
produce useful error messages.

## References
This project is forked from Dr. Peter Jipsen's repository. Some of the code is credited and attributed to him. Since our respository is an experimental project with possible errors, please see his repository for fully working functionaility, although not all functionaility will be included there.

## Future Work
* Create a robust error message system
    - Catch exceptions and prevent code from shutting down with incorrect inputs
       * Modify parser to catch these exceptions
    - Help the user understand exactly what the problem is and how to fix it
        * when exceptions or errors are caught, output where the error occured and possibly how to fix depending on whether the program can detect error
* Add more math functions
    - Possible implementation of numpy (for matrix operations and other linear algebra operations)
       * Similar to Sympy inclusion - add numpy functions and modify parser and prefixes accordingly 
* Ultimate goal for a finished product is the ablity to parse and run anything that is mathematically sound and written in laTex 

