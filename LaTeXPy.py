# Python program to parse LaTeX formulas and produce Python/Prover9 expressions

# by Peter Jipsen 2023-3-21 distributed under LGPL 3 or later.
# Terms are read using Vaughn Pratt's top-down parsing algorithm.

# List of symbols handled by the parser (at this point)
# =====================================================
# \And \approx \backslash \bb \bigcap \bigcup \bot \cap \cc \cdot  
# \circ \Con \cup \equiv \exists \forall \ge \implies \in \le \ln \m 
# \mathbb \mathbf \mathcal \mid \Mod \models \ne \neg \ngeq \nleq \Not 
# \nvdash \oplus \Or \Pre \setminus \sim \subset \subseteq \supset \supseteq 
# \times \to \top \vdash \vee \vert \wedge + * / ^ _ ! = < > ( ) [ ] \{ \} | | $

# Greek letters and most other LaTeX symbols can be used as variable names.
# A LaTeX symbol named \abc... is translated to the Python variable _abc...

#!pip install provers
#from provers import *
import math, itertools, re, sys, subprocess
subprocess.check_call([sys.executable, '-m', 'pip', 'install', 'latex2sympy2'])
from sympy import *
init_session()
from latex2sympy2 import *
from IPython.display import *

# The macros below are used to simplify the input that needs to be typed.
macros=r"""
\renewcommand{\And}{\ \text{and}\ }
\renewcommand{\Or}{\ \text{or}\ }
\renewcommand{\Not}{\text{not}\ }
\renewcommand{\m}{\mathbf}
\renewcommand{\bb}{\mathbb}
\renewcommand{\cc}{\mathcal}
\renewcommand{\s}{\text}
\renewcommand{\bsl}{\backslash}
\renewcommand{\sm}{{\sim}}
\renewcommand{\tup}[1]{(#1)}
\renewcommand{\Mod}{\text{Mod}}
\renewcommand{\Con}{\text{Con}}
\renewcommand{\Pre}{\text{Pre}}
"""
display(Markdown("$"+macros+"$"))
RunningInCOLAB = 'google.colab' in str(get_ipython())
if not RunningInCOLAB: macros=""

p9options=[ # redeclare Prover9 syntax
    "redeclare(conjunction, and)",
    "redeclare(disjunction, or)",
    "redeclare(negation, not)",
    'redeclare(implication, "==>")',
    'redeclare(backward_implication, "<==")',
    'redeclare(equivalence, "<=>")',
    'redeclare(equality, "==")']

P9 = False

def p9st(t):
  global P9
  P9=True;ps=str(t);P9=False
  return ps

def pr9(assume_list, goal_list, mace_seconds=2, prover_seconds=60, cardinality=None, params='', info=False):
    global prover9
    if type(cardinality) == int or cardinality == None:
        return prover9(assume_list, goal_list, mace_seconds, prover_seconds, cardinality, params=params, info=info, options=p9options)
    else:
        algs = [[], [1]]+[[] for i in range(2, cardinality[0]+1)]
        for i in range(2, cardinality[0]+1):
            algs[i] = prover9(assume_list, goal_list, mace_seconds, prover_seconds, i, params=params, info=info, options=p9options)
        print("Fine spectrum: ", [len(x) for x in algs[1:]])
        return algs

from IPython.display import *
import math, itertools, re
_pi = sympy.pi
_e = math.e

def is_postfix(t):
    return hasattr(t,'leftd') and len(t.a)==1

def w(t,i): # decide when to add parentheses during printing of terms
    subt = t.a[i] if len(t.a)>i else "index out of range"
    return str(subt) if subt.lbp < t.lbp or subt.a==[] or \
        (subt.sy==t.sy and subt.lbp==t.lbp) or \
        (not hasattr(subt,'leftd') or not hasattr(t,'leftd')) or \
        (is_postfix(subt) and is_postfix(t)) else "("+str(subt)+")"

def w2(t,i):
  subt = t.a[i] if len(t.a)>i else "index out of range"
  return str(subt) if subt.lbp < t.lbp or subt.a==[] \
        or (not hasattr(subt,'leftd') and subt.lbp==1200) \
        else "("+str(subt)+")"

def w3(t,i): # always add parentheses
  subt = t.a[i] if len(t.a)>i else "index out of range"
  return "("+str(subt)+")"

def letter(c): return 'a'<=c<='z' or 'A'<=c<='Z'
def alpha_numeric(c): return 'a'<=c<='z' or 'A'<=c<='Z' or '0'<=c<='9'

class symbol_base(object):
    a = []
    def __repr__(self): 
        if   len(self.a) == 0: return self.sy.replace("\\","_").replace("{","").replace("}","")
        elif len(self.a) == 2:
         return w(self,0)+" "+self.sy+" "+w(self,1)
        else:
         return self.sy+"("+",".join([w(self,j) for j in range(len(self.a))])+")"

def symbol(id, bp=1200): # identifier, binding power; LOWER binds stronger
    if id in symbol_table:
        s = symbol_table[id]    # look symbol up in table
        s.lbp = min(bp, s.lbp)  # update left binding power
    else:
        class s(symbol_base):   # create class for this symbol
            pass
        s.sy = id
        s.lbp = bp
        s.nulld = lambda self: self
        symbol_table[id] = s
    return s

def advance(id=None):
    global token
    if id and token.sy != id:
        raise SyntaxError("Expected "+id+" got "+token.sy)
    token = next()

def nulld(self): # null denotation
    expr = expression()
    advance(")")
    return expr

def nulldbr(self): # null denotation
    expr = expression()
    advance("}")
    return expr

def prefix(id, bp=0): # parse n-ary prefix operations
    global token
    def nulld(self): # null denotation
        global token
        if token.sy not in ["(","[","{"] and self.sy not in ["\\forall","\\exists"]:
            #print('token.sy',token.sy,'self.sy',self.sy)
            self.a = [] if token.sy in [",",")","}",":","=","!="] else [expression(bp)]
            if self.sy=="|": advance("|")
            return self
        else:
            closedelim = ")" if token.sy=="(" else "]" if token.sy=="[" else "}"
            token = next()
            self.a = []
            if token.sy != ")":
                while 1:
                    self.a.append(expression())
                    if token.sy != ",":
                        break
                    advance(",")
            advance(closedelim)
            if closedelim=="}" and token.sy=="(": #make \cmd{v}(...) same as \cmd c(...)
              prefix(self.a[0].sy)
              token = next()
              self.a[0].a = []
              if token.sy != ")":
                while 1:
                    self.a[0].a.append(expression())
                    if token.sy != ",":
                        break
                    advance(",")
              advance(")")
            return self
    s = symbol(id, bp)
    s.nulld = nulld
    return s

def infix(id, bp, right=False):
    def leftd(self, left): # left denotation
        self.a = [left]
        self.a.append(expression(bp+(1 if right else 0)))
        return self
    s = symbol(id, bp)
    s.leftd = leftd
    return s

def preorinfix(id, bp, right=True): # used for minus
    def leftd(self, left): # left denotation
        self.a = [left]
        self.a.append(expression(bp+(1 if right else 0)))
        return self
    def nulld(self): # null denotation
        global token
        self.a = [expression(bp)]
        return self
    s = symbol(id, bp)
    s.leftd = leftd
    s.nulld = nulld
    return s

def plist(id, bp=0): #parse a parenthesized comma-separated list
    global token
    def nulld(self): # null denotation
        global token
        self.a = []
        if token.sy not in ["]","\\}"]:
            while True:
                self.a.append(expression())
                if token.sy != ",": break
                advance(",")
        advance()
        return self
    s = symbol(id, bp)
    s.nulld = nulld
    return s

def postfix(id, bp):
    def leftd(self,left): # left denotation
        self.a = [left]
        return self
    s = symbol(id, bp)
    s.leftd = leftd
    return s

symbol_table = {}

# The parsing rules  below decode a string of tokens into an abstract syntax tree with methods .sy 
# for symbol (a string) and .a for arguments.

def init_symbol_table():
    global symbol_table
    symbol_table = {}
    symbol("(").nulld = nulld
    symbol(")")
    symbol("{").nulld = nulldbr
    symbol("}")
    prefix("|").__repr__ = lambda x: "len("+str(x.a[0])+")" #interferes with p|q from Prover9
    plist("[").__repr__ = lambda x: "["+",".join([strorval(y) for y in x.a])+"]"
    plist("\\tup{").__repr__ = lambda x: "("+",".join([strorval(y) for y in x.a])+")"
    plist("\\{").__repr__ = lambda x: "frozenset(["+x.a[0].a[0].a[0].sy+" for "+str(x.a[0].a[0])+\
      " if "+str(x.a[0].a[1]).replace(" = "," == ")+"])"\
      if len(x.a)==1 and x.a[0].sy=="\\mid" and x.a[0].a[0].sy=="\\in"\
      else "frozenset(["+str(x.a[0].a[0])+" for "+str(x.a[0].a[1].a[0])+\
      " if "+str(x.a[0].a[1].a[1]).replace(" = "," == ")+"])"\
      if len(x.a)==1 and x.a[0].sy=="\\mid" and x.a[0].a[1].sy=="\\And" and x.a[0].a[1].a[0].sy=="\\in"\
      else "frozenset(["+str(x.a[0].a[0])+" for "+str(x.a[0].a[1])+"])"\
      if len(x.a)==1 and x.a[0].sy=="\\mid" and x.a[0].a[1].sy=="\\in"\
      else "frozenset(["+",".join([strorval(y) for y in x.a])+"])"\
      if len(x.a)<2 or x.a[1].sy!='\\dots' else "frozenset(range("+str(x.a[0])+","+str(x.a[2])+"+1))"
    symbol("]")
    symbol("\\}")
    symbol(",")
    postfix("!",300).__repr__ =       lambda x: "math.factorial("+str(x.a[0])+")"
    postfix("f",300).__repr__ =       lambda x: "f"+w3(x,0)
    postfix("'",300).__repr__ =       lambda x: str(x.a[0])+"'"
    prefix("\\ln",310).__repr__ =     lambda x: "math.log("+str(x.a[0])+")"
    prefix("\\sin",310).__repr__ =    lambda x: "sin("+str(x.a[0])+")"  # use math.sin if sympy is not loaded
    infix(":", 450).__repr__ =        lambda x: str(x.a[0])+": "+w3(x,1) # for f:A\to B
    infix("^", 300).__repr__ =        lambda x: "converse("+str(x.a[0])+")"\
      if len(x.a)>1 and str(x.a[1].sy)=='\\smallsmile' else "O("+str(x.a[0])+")"\
      if P9 and len(x.a)>0 and str(x.a[1])=="-1" else w2(x,0)+"\\wedge "+w2(x,1)\
      if P9 else w2(x,0)+"**"+w2(x,1)                                       # power
    infix("_", 300).__repr__ =        lambda x: str(x.a[0])+"["+w(x,1)+"]"  # sub
    infix(";", 303).__repr__ =        lambda x: "relcomposition("+w(x,0)+","+w(x,1)+")" # relation composition
    infix("\\circ", 303).__repr__ =   lambda x: "relcomposition("+w(x,1)+","+w(x,0)+")" # function composition
    infix("*", 311).__repr__ =        lambda x: w2(x,0)+"\\cdot "+w2(x,1)   # times
    infix("\\cdot", 311).__repr__ =   lambda x: w2(x,0)+"*"+w2(x,1)         # times
    infix("/", 312).__repr__ =        lambda x: w2(x,0)+"/"+w2(x,1)         # over
    infix("+", 313).__repr__ =        lambda x: w2(x,0)+" + "+w2(x,1)       # plus
    preorinfix("-",313).__repr__ =    lambda x: "-"+w(x,0) if len(x.a)==1 else str(x.a[0])+" - "+w(x,1) #negative or minus
    symbol("\\top").__repr__ =        lambda x: "T"
    symbol("\\bot").__repr__ =        lambda x: "0"
    infix("\\times", 322).__repr__ =  lambda x: "frozenset(itertools.product("+w(x,0)+","+w(x,1)+"))" #product
    infix("\\cap", 323).__repr__ =    lambda x: w(x,0)+" & "+w(x,1)         # intersection
    infix("\\cup", 324).__repr__ =    lambda x: w(x,0)+" | "+w(x,1)         # union
    infix("\\setminus", 325).__repr__=lambda x: w(x,0)+" - "+w(x,1)         # setminus
    infix("\\oplus", 326).__repr__ =  lambda x: w(x,0)+" ^ "+w(x,1)         # symmetric difference
    prefix("\\bigcap",350).__repr__ = lambda x: "intersection("+str(x.a[0])+")" # intersection of a set of sets
    prefix("\\bigcup",350).__repr__ = lambda x: "union("+str(x.a[0])+")"    # union of a set of sets
    prefix("\\mathcal{P}",350).__repr__=lambda x: "powerset("+str(x.a[0])+")" #powerset of a set
    prefix("\\cc{P}",350).__repr__=   lambda x: "powerset("+str(x.a[0])+")" # powerset of a set
    prefix("\\mathbf",350).__repr__ = lambda x: "_mathbf"+str(x.a[0].sy)    # algebra or structure or theory
    prefix("\\m",350).__repr__ =      lambda x: "_m"+str(x.a[0].sy)         # algebra or structure or theory
    prefix("\\mathbb",350).__repr__ = lambda x: "_mathbb"+str(x.a[0].sy)    # blackboard bold
    prefix("\\bb",350).__repr__ =     lambda x: "_bb"+str(x.a[0].sy)        # blackboard bold

    ###### testing trig functions ##### (works with one variable and no other operations inside it)
    prefix("\\sin",310).__repr__ =    lambda x: "sympy.sin("+str(x.a[0])+")"
    prefix("\\cos",310).__repr__ =    lambda x: "sympy.cos("+str(x.a[0])+")"
    prefix("\\tan",310).__repr__ =    lambda x: "sympy.tan("+str(x.a[0])+")"
    prefix("\\arcsin",310).__repr__ =    lambda x: "sympy.asin("+str(x.a[0])+")"
    prefix("\\arccos",310).__repr__ =    lambda x: "sympy.acos("+str(x.a[0])+")"
    prefix("\\arctan",310).__repr__ =    lambda x: "sympy.atan("+str(x.a[0])+")"

    # testing derivatives/integrations ( NOT WORKING )
    prefix("\\frac",310).__repr__ =    lambda x: "sympy.simplify("+ str(x.a[0]) + ")"
    prefix("\\frac{d}{dx}",310).__repr__ =    lambda x: "sympy.diff("+str(x.a[0])+")"

    infix("\\vert", 365).__repr__ =   lambda x: w(x,1)+"%"+w(x,0)+"==0"     # divides
    infix("\\in", 370).__repr__ =     lambda x: w(x,0)+" in "+w(x,1)        # element of
    infix("\\subseteq", 370).__repr__=lambda x: w(x,0)+" <= "+w(x,1)        # subset of
    infix("\\subset", 370).__repr__ = lambda x: w(x,0)+" < "+w(x,1)         # proper subset of
    infix("\\supseteq", 370).__repr__=lambda x: w(x,1)+" <= "+w(x,0)        # supset of
    infix("\\supset", 370).__repr__ = lambda x: w(x,1)+" < "+w(x,0)         # proper subset of
    infix("=", 405).__repr__ =        lambda x: w(x,0)+"=="+w(x,1)          # assignment or identity
    infix("==", 405).__repr__ =       lambda x: w(x,0)+" = "+w(x,1)         # assignment or identity
    infix("\\ne", 405).__repr__ =     lambda x: w(x,0)+" != "+w(x,1)        # nonequality
    infix("!=", 405).__repr__ =       lambda x: w(x,0)+"\\ne "+w(x,1)       # nonequality
    infix("\\le", 405).__repr__ =     lambda x: w2(x,0)+" <= "+str(x.a[1])  # less or equal
    infix("<=", 405).__repr__ =       lambda x: w2(x,0)+"\\le "+str(x.a[1]) # less or equal in Python
    infix("\\ge", 405).__repr__ =     lambda x: w2(x,0)+">="+str(x.a[1])    # greater or equal
    infix("<", 405).__repr__ =        lambda x: w2(x,0)+" < "+str(x.a[1])   # less than
    infix(">", 405).__repr__ =        lambda x: w2(x,0)+" > "+str(x.a[1])   # greater than
    infix("\\nleq", 405).__repr__ =   lambda x: "not("+w2(x,0)+"<="+str(x.a[1])+")" # not less or equal
    infix("\\ngeq", 405).__repr__ =   lambda x: "not("+w2(x,1)+"<="+str(x.a[0])+")" # not greater or equal
#    infix("\\approx", 405).__repr__ = lambda x: w2(x,0)+" Aprx "+str(x.a[1]) # approximately
#    infix("\\equiv", 405).__repr__ =  lambda x: w2(x,0)+" Eq "+str(x.a[1])   # equivalence relation
    prefix("\\neg",450).__repr__=     lambda x: "not "+w(x,0)               # negation symbol
    prefix("\\Not",450).__repr__=     lambda x: "not "+w3(x,0)              # logical negation
    prefix("\\forall",450).__repr__ = lambda x: "all("+str(x.a[-1]).replace(" = "," == ")+\
            "".join(" for "+str(x) for x in x.a[:-1])+")"                   # universal quantifier
    prefix("\\exists",450).__repr__ = lambda x: "any("+str(x.a[-1]).replace(" = "," == ")+\
            "".join(" for "+str(x) for x in x.a[:-1])+")"                   # existential quantifier
    infix("\\Or", 503).__repr__=      lambda x: w(x,0)+(" or ")+w(x,1)      # disjunction
    infix("\\And", 503).__repr__=     lambda x: w(x,0)+(" and ")+w(x,1)     # conjunction
    infix("\\implies", 504).__repr__ =lambda x: "not "+w3(x,0)+" or "+w3(x,1) # implication
    infix("\\iff", 505).__repr__ =    lambda x: w3(x,0)+" <=> "+w3(x,1)     # if and only if
    infix("\\mid", 550).__repr__ =    lambda x: str(x.a[0])+" mid "+str(x.a[1]) # such that
    prefix("primefactors",310).__repr__ = lambda x: "latex(primefactors("+str(x.a[0])+"))" # factor an integer
    prefix("ls",310).__repr__ =       lambda x: "latex2latex("+str(x.a[0])+")" # use the latex2sympy2 parser and sympy to calculate
    prefix("factor",310).__repr__ =   lambda x: "latex(factor("+str(x.a[0])+("" if len(x.a)==1 else ","+str(x.a[1]))+"))" # factor a polynomial
    prefix("solve",310).__repr__ =    lambda x: "latex(solve("+(str(x.a[0].a[0])+"-("+str(x.a[0].a[1])+")" if x.a[0].sy=="=" else str(x.a[0]))+\
      ("" if len(x.a)==1 else ","+str(x.a[1]))+"))" # solve a (list of) equations
    prefix("show",310).__repr__ =     lambda x: "show("+str(x.a[0])+(")" if len(x.a)==1 else ","+str(x.a[1])+")") # show poset or (semi)lattice
    postfix("?", 600).__repr__ =      lambda x: str(x.a[0])+"?"             # calculate value and show it
    symbol("(end)")
##########################
# syntax below is used only for Prover9
    infix("or", 503).__repr__=        lambda x: w(x,0)+r"\ \text{or}\ "+w(x,1) # disjunction to LaTeX
    infix("and", 503).__repr__=       lambda x: w(x,0)+r"\ \text{and}\ "+w(x,1) # conjunction to LaTeX
    infix("==>", 504).__repr__ =      lambda x: w2(x,0)+"\\implies "+w2(x,1) # implication
    infix("<=>", 505).__repr__ =      lambda x: w3(x,0)+"\\iff "+w3(x,1) # if and only if
    infix("\\backslash", 312).__repr__=lambda x: w(x,0)+"\ "+w(x,1)      # under
    infix("\\bsl", 312).__repr__=     lambda x: w(x,0)+"\ "+w(x,1)       # under
    infix("\\wedge", 314).__repr__ =  lambda x: w2(x,0)+" ^ "+w2(x,1)    # meet
    infix("\\vee", 314).__repr__ =    lambda x: w2(x,0)+" v "+w2(x,1)    # join
    infix("v", 314).__repr__ =        lambda x: w2(x,0)+"\\vee "+w2(x,1) # join
    infix("\\to", 316).__repr__ =     lambda x: w(x,0)+" -> "+w(x,1)
    prefix("O",310).__repr__ =        lambda x: "{"+str(x.a[0])+"^{-1}}" #P9 name for inverse
    preorinfix("\\sim",310).__repr__= lambda x: "~"+w(x,0)\
      if len(x.a)==1 else str(x.a[0])+" ~ "+w(x,1) #left negative or equivalence relation
    prefix("\\sm",310).__repr__=      lambda x: "~"+w(x,0) #version of \sim with better spacing
    prefix("\\Mod",350).__repr__=     lambda x: "[z for y in pr9(pyp9("+p9st(x.a[0])+"),[],"+(p9st(x.a[2]) if len(x.a)>2\
      else "100")+",0,["+(p9st(x.a[1]) if len(x.a)>1 else "2")+"])[2:] for z in y]"
    prefix("\\Con",350).__repr__=     lambda x: "congruences("+str(x.a[0])+")" # set of congruences of an algebra
    prefix("\\Pre",350).__repr__=     lambda x: "precongruences("+str(x.a[0])+")" # set of precongruences of a po-algebra
    infix("\\models", 550).__repr__ = lambda x: "check("+p9st(x.a[0])+",\""+p9st(x.a[1])+"\")" # check if A satisfies phi
    infix("\\vdash", 550).__repr__ =  lambda x: "pr9(pyp9("+p9st(x.a[0])+"),[pyp9(\""+p9st(x.a[1])+"\")],2,60)[0]" # proves
    infix("\\nvdash", 550).__repr__ = lambda x: "pr9(pyp9("+p9st(x.a[0])+"),[pyp9(\""+p9st(x.a[1])+"\")],10,0)[0]" # disproves
########end of Prover9 syntax

init_symbol_table()

# tokenize(st):
  # 

def tokenize(st):
    i = 0
    # loop the length of the string
    while i<len(st):
        tok = st[i]
        j = i+1
        # if 
        if j<len(st) and (st[j]=="{" or st[j]=="}") and tok=='\\':
          j += 1
          tok = st[i:j]
          symbol(tok)
        elif letter(tok) or tok=='\\': #read consecutive letters or digits
            while j<len(st) and alpha_numeric(st[j]): j+=1
            tok = st[i:j]
            if tok=="\\" and j<len(st) and st[j]==" ": j+=1
            if tok=="\\text": j = st.find("}",j)+1 if st[j]=="{" else j #extend token to include {...} part
            if tok=="\\s": j = st.find("}",j)+1 if st[j]=="{" else j
            if tok=="\\mathcal": j = st.find("}",j)+1 if st[j]=="{" else j
            if tok=="\\cc": j = st.find("}",j)+1 if st[j]=="{" else j
            if tok=="\\tup": j += 1 if st[j]=="{" else j
            tok = st[i:j]
            symbol(tok)
            if j<len(st) and st[j]=='(': prefix(tok, 1200) #promote tok to function
        elif "0"<=tok<="9": #read (decimal) number in scientific notation
            while j<len(st) and ('0'<=st[j]<='9' or st[j]=='.'):# in ['.','e','E','-']):
                j+=1
            tok = st[i:j]
            symbol(tok)
        elif tok =="-" and st[j]=="-": pass
        elif tok not in " '(,)[]{}\\|\n": #read operator string
            while j<len(st) and not alpha_numeric(st[j]) and \
                  st[j] not in " '(,)[]{}\\\n": j+=1
            tok = st[i:j]
            if tok not in symbol_table: symbol(tok)
        i = j
        if tok not in [' ','\\newline','\\ ','\n']: #skip these tokens
            symb = symbol_table[tok]
            if not symb: #symb = symbol(tok)
                raise SyntaxError("Unknown operator")
#            print tok, 'ST', symbol_table.keys()
            yield symb()
    symb = symbol_table["(end)"]
    yield symb()

def expression(rbp=1200): # read an expression from token stream
    global token
    t = token
    try:
      token = next()
    except:
      token = ttt
    left = t.nulld()
    while rbp > token.lbp:
        t = token
        token = next()
        left = t.leftd(left)
    return left

# parse(str):
  # 

def parse(str):
    global token, next
    next = tokenize(str).__next__
    token = next()
    return expression()

ttt=parse(".")

def ast(t):
    if len(t.a)==0: return '"'+t.sy+'"'
    return '("'+t.sy+'",'+", ".join(ast(s) for s in t.a)+")"

def intersection(X):
  S = frozenset()
  for x in X: S &= x
  return S

def union(X):
  S = frozenset()
  for x in X: S |= x
  return S

def powerset(X):
  PX = [()]
  for i in range(len(X)):
    PX += itertools.combinations(X, i+1)
  return frozenset(frozenset(x) for x in PX)

def converse(R):
  return frozenset((x[1],x[0]) for x in R if len(x)==2)

def relcomposition(R,S):
  ss = {}
  for x in S:
    if len(x)==2:
      if x[0] not in ss.keys(): ss[x[0]] = set()
      ss[x[0]].add(x[1])
  rr = frozenset(x for x in R if len(x)==2 and x[1] in ss.keys())
  return frozenset((x[0],y) for x in rr for y in ss[x[1]])

def eqrel2partition(co):
    classes = {}
    for x in co:
        if x[0] not in classes.keys(): classes[x[0]] = set([x[0]])
        classes[x[0]].add(x[1])
    return frozenset(frozenset(classes[y]) for y in classes.keys())

def rel2pairs(rel):
  B = range(len(rel))
  return frozenset((i,j) for j in B for i in B if rel[i][j])

cntr = 0 # global model counter
def pyla(p,newl=False): # convert Python object to LaTeX string
  global cntr
  if type(p)==frozenset:
    try:
      sp = sorted(p)
    except:
      sp = p
    cntr=0; st="\\{"+", ".join(pyla(el,True) for el in sp)+"\\}" if len(p)>0 else "\\emptyset";cntr=0
  elif type(p)==list:  cntr=0; st="["+", ".join(pyla(el,True) for el in p)+"]";cntr=0
  elif type(p)==tuple: cntr=0; st="("+", ".join(pyla(el,True) for el in p)+")";cntr=0
  elif type(p)==bool:  st = "\mathbf{"+str(p)+"}"
  elif prvrs and type(p)==Model: st = modelLa(p)
  elif prvrs and type(p)==Proof: st = proofLa(p)
  elif type(p)==str:
    if p=="N": return "\\text{No counterexample after 10 seconds}"
    try:
      st =  str(parse(p if p[0]!="_" else "\\"+p[1:]))
    except: pass
    if st[0]=="_": st = "\\"+st[1:]
  else:
    st =  str(p)
  if newl and len(st)>=20: return "\\newline\n"+st
  #if newl and len(st)>=5: return " \\ "+st
  return st

import networkx as nx
from graphviz import Graph
from IPython.display import display_html
def hasse_diagram(op,rel,dual,unary=[]):
    A = range(len(op))
    G = nx.DiGraph()
    if rel:
        G.add_edges_from([(x,y) for x in A for y in A if (op[y][x] if dual else op[x][y]) and x!=y])
    else: 
        G.add_edges_from([(x,y) for x in A for y in A if op[x][y]==(y if dual else x) and x!=y])
    try:
        G = nx.algorithms.dag.transitive_reduction(G)
    except:
        pass
    P = Graph()
    P.attr('node', shape='circle', width='.15', height='.15', fixedsize='true', fontsize='10')
    for x in A: P.node(str(x), color='red' if unary[x] else 'black')
    P.edges([(str(x[0]),str(x[1])) for x in G.edges])
    return P

def m4diag(li,symbols="<= v", unaryRel=""):
    # use graphviz to display a mace4 structure as a diagram
    # symbols is a list of binary symbols that define a poset or graph
    # unaryRel is a unary relation symbol that is displayed by red nodes
    i = -1
    sy = symbols.split(" ")
    #print(sy)
    st = ""
    for x in li:
        i+=1
        st+=str(i)
        uR = x.relations[unaryRel] if unaryRel!="" else [0]*x.cardinality
        for s in sy:
            t = s[:-1] if s[-1]=='d' else s
            if t in x.operations.keys():
                st+=hasse_diagram(x.operations[t],False,s[-1]=='d',uR)._repr_image_svg_xml()+"&nbsp; &nbsp; &nbsp; "
            elif t in x.relations.keys():
                st+=hasse_diagram(x.relations[t], True, s[-1]=='d',uR)._repr_image_svg_xml()+"&nbsp; &nbsp; &nbsp; "
        st+=" &nbsp; "
    display_html(st,raw=True)

# Convert (a subset of) LaTeX input to valid Python(sympy) code
# Display LaTeX with calculated answers inserted
# Return LaTeX and/or Python code as a string

#nextmath(st, index):
  # checks if the string is enclosed in '$'

  # st - string input from user
  # index - st starting index

def nextmath(st,i): #find next j,k>=i such that st[j:k] is inline or display math
  # find first occurence of '$'
  j = st.find("$",i)
  # if '$' is not found, return j=-1,k=0,d=false
  if j==-1: return (-1,0,False)
  # check if the math string is just "$$"
  if st[j+1]=="$":
    # set k equal to the starting index of "$$"
    k = st.find("$$",j+2)
    # j = index after the double "$$"
    # k = starting index of "$$"
    # d = True (found "$$")
    return (j+2,k,True)
  else:
    # j = index after first '$'
    # k = index of second '$' (if there is one)
    # d = False (did not find "$$")
    return (j+1,st.find("$",j+1),False)


#process is called from main function
#crates syntax tree and decides the hierarchy of functions to use first
# process(st, info, nocolor):
  # 


def process(st, info=False, nocolor=False):
  # convert st (a LaTeX string) to Python/Prover9 code and evaluate it
  if st[:3]=="ls(": # use latex2sympy2 parser
    return ("" if nocolor else "\color{green}")+macros+st[3:-1]+("" if nocolor else "\color{blue}")+" = "+latex2latex(st[3:-1])
  # 
  t=parse(st)
  if info:
    print("Abstract syntax tree:", ast(t))
    print("Expression:", t)
  if t.sy!="?": # check if t is not asking to be evaluated
    if t.sy!="=": # check if t is an assignment
      if t.sy=="show": # check if t is a show command
        try:
          exec(str(t),globals())
        except:
          if info: print("no result")
          return macros+st
        return ("" if nocolor else "\color{green}")+macros+st
      return macros+st
    ss = str(t).replace("==","=",1)
    try:
      exec(ss,globals())
    except:
      if info: print("no result")
      return macros+st
    return ("" if nocolor else "\color{green}")+macros+st
  tt = t.a[0]
  st = st.replace("?","")
  if tt.sy=="=":
    ss = str(tt).replace("==","=",1)
    try:
      exec(ss,globals())
    except:
      if info: print("no result")
      return macros+st
    return ("" if nocolor else "\color{green}")+macros+st+("" if nocolor else "\color{blue}")+" = "+pyla(eval(str(tt.a[0])))
  try:
    val=eval(str(tt))
    if info: print("Value:", val)
    ltx = val if str(tt)[:5]=="latex" else pyla(val)
  except:
    return ("" if nocolor else "\color{green}")+macros+st
  return ("" if nocolor else "\color{green}")+macros+st+("" if nocolor else "\color{blue}")+" = "+ltx

# l(st, info, output, nocolor)
  # st - string input from user
  # info - 
  # output -
  # nocolor - 


  # Main function to translate valid LaTeX/Markdown string st
def l(st, info=False, output=False, nocolor=False):
  # assuming this is used to get r""" ?
  global macros
  st = re.sub("\n%.*?\n","\n",st) #remove LaTeX comments
  st = re.sub("%.*?\n","\n",st) #remove LaTeX comments
  # look for '$' in the string and update indices (j,k)
  (j,k,d) = nextmath(st,0)
  # out = the first '$'
  out = st[0:j]
  # while there are two '$'
  while j!=-1 and k!=-1:
    # process the math equation in latex
    out += process(st[j:k],info,nocolor)
    p = k
    (j,k,d) = nextmath(st,k+(2 if d else 1))
    out += st[p:j] if j!=-1 else st[p:]
  display(Markdown(out))
  if output: print(out)

def m(st, info=False, output=False, nocolor=False): 
  # math input; $-signs are not needed, but commands should be separated by empty lines
  global macros
  st = re.sub("\n%.*?\n","\n",st) #remove LaTeX comments
  st = re.sub("%.*?\n","\n",st) #remove LaTeX comments
  li = st.split("\n\n")
  out = "$"+"$\n\n$".join(process(x.strip(),info,nocolor) for x in li)+"$"
  display(Markdown(out))
  if output: print(out)

prvrs="Model" in dir() # check if provers module is loaded
