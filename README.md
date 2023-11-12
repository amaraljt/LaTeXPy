# LaTeXPy

## Group Members
Jared Amaral,  Maverick Wadman, Alex Haberman

## 11/1/23 Update
Please go to the ``prototype`` folder and follow the README to run our updated program.

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

