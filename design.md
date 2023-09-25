# LaTeXPy Design/Future Work
* Publish LaTeX as a VSCode extension for future users to use
* Create a robust error message system
    - Catch exceptions and prevent code from shutting down with incorrect inputs
       * Modify parser to catch these exceptions
    - Help the user understand exactly what the problem is and how to fix it
        * when exceptions or errors are caught, output where the error occured and possibly how to fix depending on whether the program can detect error
* Add more math functions
    - Possible implementation of numpy (for matrix operations and other linear algebra operations)
       * Similar to Sympy inclusion - add numpy functions and modify parser and prefixes accordingly 
* Ultimate goal for a finished product is the ablity to parse and run anything that is mathematically sound and written in laTex 
