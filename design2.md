# LaTeXPy Updated Semester Design

After discussing with Dr. Jipsen about the future of LaTeXPy, we decided to update our goals. We have decided to put aside the mathematical side of the project and focus more on algorithms. We want LaTeXPy to be able to parse through an entire algorithm, written in LaTeX, and produce valid Python code that is runnable. By utilizing the syntax in the `algpseudocodex` LaTeX package, we will upgrade our parser to be able to parse and create a correct abstract syntax tree of an entire algorithm. We also agreed that publishing LaTeXPy to VSCode as a public extension would be beneficial to any LaTeX users who like to use VSCode as their editor of choice. In order to accomplish these goals we would need to:

    1. Add `algpseudocodex` package to LaTeXPy to make it understand the new syntax
    2. Update or create a new wrapper function (`?` is currently being used as root of our AST to evaluate a mathematical expression) to translate it into Python code
    - update the symbol table with `algpseudocodex` functions (i.e. \If, \State, \While, ...)
    - start with simple conditional statements (\If, \else, ...) that can handle all types of conditions then move on to loops (\For, \While, ...)

    3. Use JavaScript to create a VSCode extension of LaTeXPy