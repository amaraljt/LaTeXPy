# Python program to parse LaTeX formulas and evaluate Python/Prover9 expressions

# Terms are read using Vaughn Pratt's top-down parsing algorithm
# by Peter Jipsen, version 2023-1-6 distributed under GPL v3 or later
import math, itertools, re, sys, subprocess
subprocess.check_call([sys.executable, '-m', 'pip', 'install', 'provers'])
from provers import *
from IPython.display import *

def is_postfix(t):
    return hasattr(t,'leftd') and len(t.a)==1

def w(t,i): # decide when to add parentheses during printing of terms
    subt = t.a[i] if len(t.a)>i else t
    return str(subt) if subt.lbp < t.lbp or subt.a==[] or \
        (subt.sy==t.sy and subt.lbp==t.lbp) or \
        (not hasattr(subt,'leftd') or not hasattr(t,'leftd')) or \
        (is_postfix(subt) and is_postfix(t)) else "("+str(subt)+")"

def w2(t,i):
  subt = t.a[i] if len(t.a)>i else t
  return str(subt) if subt.lbp < t.lbp or subt.a==[] \
        or (not hasattr(subt,'leftd') and subt.lbp==1200) \
        else "("+str(subt)+")"

def w3(t,i): # 
  subt = t.a[i] if len(t.a)>i else t
  return "("+str(subt)+")"
    #str(subt) if subt.a==[] or not hasattr(subt,'leftd') or \
    #subt.sy not in ['@', '&', '|', '=>', '<=', '<=>', '\\implies'] else "( "+str(subt)+" )"

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
              #self.a[0].a = [expression()]
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

def plist(id, bp=0):
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
P9 = False

def init_symbol_table():
    global symbol_table
    symbol_table = {}
    symbol("(").nulld = nulld
    symbol(")")
    symbol("{").nulld = nulldbr
    symbol("}")
    prefix("|").__repr__ = lambda x: "len("+str(x.a[0])+")" #interferes with p|q from Prover9
    plist("[").__repr__ = lambda x: "["+",".join([strorval(y) for y in x.a])+"]"
    plist("\\{").__repr__ = lambda x: "frozenset(["+x.a[0].a[0].a[0].sy+" for "+str(x.a[0].a[0])+\
      " if "+str(x.a[0].a[1]).replace(" = "," == ")+"])" if len(x.a)==1 and x.a[0].sy=="\\mid"\
      else "frozenset(["+",".join([strorval(y) for y in x.a])+"])"\
      if len(x.a)<2 or x.a[1].sy!='\\dots' else "frozenset(range("+str(x.a[0])+","+str(x.a[2])+"+1))"
    symbol("]")
    symbol("\\}")
    symbol(",")

    postfix("!",300).__repr__ =       lambda x: "math.factorial("+str(x.a[0])+")"
    postfix("'",300).__repr__ =       lambda x: str(x.a[0])+"'"
    prefix("\\ln",310).__repr__ =     lambda x: "math.log("+str(x.a[0])+")"
    prefix("O",310).__repr__ =        lambda x: "{"+str(x.a[0])+"^{-1}}" #P9 name for inverse
    preorinfix("\\sim",310).__repr__= lambda x: "~"+w(x,0)
    preorinfix("-",310).__repr__ =    lambda x: "-"+w(x,0)\
      if len(x.a)==1 else str(x.a[0])+" - "+w(x,1) #negative or minus
    infix(":", 450).__repr__ =        lambda x: str(x.a[0])+": "+w3(x,1) # for f:A\to B
    infix("^", 300).__repr__ =        lambda x: "converse("+str(x.a[0])+")"\
      if len(x.a)>1 and str(x.a[1].sy)=='\\smallsmile' else "O("+str(x.a[0])+")"\
      if P9 and len(x.a)>0 and str(x.a[1])=="-1" else w2(x,0)+"\\wedge "+w2(x,1)\
      if P9 else w2(x,0)+"**"+w2(x,1) # power
    infix("_", 300).__repr__ =        lambda x: str(x.a[0])+"["+w(x,1)+"]" # sub
    infix(";", 303).__repr__ =        lambda x: "relcomposition("+w(x,0)+","+w(x,1)+")" # relation composition
    infix("\\circ", 303).__repr__ =   lambda x: "relcomposition("+w(x,1)+","+w(x,0)+")" # function composition
    infix("*", 311).__repr__ =        lambda x: w2(x,0)+"\\cdot "+w2(x,1) # times
    infix("\\cdot", 311).__repr__ =   lambda x: w2(x,0)+"*"+w2(x,1) # times
    infix("/", 312).__repr__ =        lambda x: w(x,0)+"/"+w(x,1) # over
    infix("\\backslash", 312).__repr__=lambda x: w(x,0)+"\ "+w(x,1) # under
    infix("+", 313).__repr__ =        lambda x: w2(x,0)+" + "+w2(x,1) # plus
    infix("\\wedge", 314).__repr__ =  lambda x: w2(x,0)+" ^ "+w2(x,1) # meet
    infix("\\vee", 315).__repr__ =    lambda x: w2(x,0)+" v "+w2(x,1) # join
    infix("v", 315).__repr__ =        lambda x: w2(x,0)+"\\vee "+w2(x,1) # join
    infix("\\to", 316).__repr__ =     lambda x: w(x,0)+" -> "+w(x,1)
    symbol("\\top").__repr__ =        lambda x: "T"
    symbol("\\bot").__repr__ =        lambda x: "0"
    
    infix("\\times", 322).__repr__ =  lambda x: "frozenset(itertools.product("+w(x,0)+","+w(x,1)+"))" #product
    infix("\\cap", 323).__repr__ =    lambda x: w(x,0)+" & "+w(x,1) # intersection
    infix("\\cup", 324).__repr__ =    lambda x: w(x,0)+" | "+w(x,1) # union
    infix("\\setminus", 325).__repr__=lambda x: w(x,0)+" - "+w(x,1) # setminus
    infix("\\oplus", 326).__repr__ =  lambda x: w(x,0)+" ^ "+w(x,1) # setminus
    prefix("\\bigcap",350).__repr__ = lambda x: "intersection("+str(x.a[0])+")" # intersection of a set of sets
    prefix("\\bigcup",350).__repr__ = lambda x: "union("+str(x.a[0])+")" # union of a set of sets
    prefix("\\mathcal{P}",350).__repr__= lambda x: "powerset("+str(x.a[0])+")"
    prefix("\\cc{P}",350).__repr__= lambda x: "powerset("+str(x.a[0])+")"
    prefix("\\mathbf",350).__repr__ = lambda x: "mbf"+str(x.a[0].sy) # algebra or structure or theory
    prefix("\\m",350).__repr__ = lambda x: "mbf"+str(x.a[0].sy) # algebra or structure or theory
    prefix("\\mathbb",350).__repr__ = lambda x: "mbb"+str(x.a[0].sy) # blackboard bold
    prefix("\\bb",350).__repr__ = lambda x: "mbb"+str(x.a[0].sy) # blackboard bold
    prefix("\\Mod",350).__repr__=lambda x: "[z for y in p9(pyp9("+str(x.a[0])+"),[],"+(str(x.a[2]) if len(x.a)>2\
      else "100")+",0,["+(str(x.a[1]) if len(x.a)>1 else "2")+"])[2:] for z in y]"
    prefix("\\Con",350).__repr__=lambda x: "congruences("+str(x.a[0])+")" # set of congruences of an algebra
    prefix("\\Pre",350).__repr__=lambda x: "precongruences("+str(x.a[0])+")" # set of precongruences of a po-algebra
    infix("\\vert", 365).__repr__ =   lambda x: w(x,1)+"%"+w(x,0)+"==0" # divides
    infix("\\in", 370).__repr__ =     lambda x: w(x,0)+" in "+w(x,1) # element of
    infix("\\subseteq", 370).__repr__=lambda x: w(x,0)+" <= "+w(x,1) # subset of
    infix("\\subset", 370).__repr__ = lambda x: w(x,0)+" < "+w(x,1) # proper subset of
    infix("=", 405).__repr__ =        lambda x: w(x,0)+(" = " if P9 else " == ")+w(x,1) # assignment or identity
    infix("\\ne", 405).__repr__ =     lambda x: w(x,0)+" != "+w(x,1) # nonequality
    infix("!=", 405).__repr__ =       lambda x: w(x,0)+"\\ne "+w(x,1) # nonequality
    infix("\\le", 405).__repr__ =     lambda x: w2(x,0)+" <= "+str(x.a[1])
    infix("<=", 405).__repr__ =       lambda x: w2(x,0)+"\\le "+str(x.a[1])
    infix("\\ge", 405).__repr__ =     lambda x: w2(x,0)+" >= "+str(x.a[1])
    infix("<", 405).__repr__ =        lambda x: w2(x,0)+" < "+str(x.a[1])
    infix(">", 405).__repr__ =        lambda x: w2(x,0)+" > "+str(x.a[1])
    prefix("\\neg",450).__repr__=     lambda x: "not "+w(x,0) # negation
    prefix("\\Not",450).__repr__=lambda x: ("-" if P9 else "not ")+w3(x,0) # negation
    prefix("\\forall",450).__repr__ = lambda x: "all("+str(x.a[-1]).replace(" = "," == ")+\
            "".join(" for "+str(x) for x in x.a[:-1])+")" # universal quantifier
    prefix("\\exists",450).__repr__ = lambda x: "any("+str(x.a[-1]).replace(" = "," == ")+\
            "".join(" for "+str(x) for x in x.a[:-1])+")" # existential quantifier
    infix("\\Or", 503).__repr__=lambda x: w(x,0)+(" | " if P9 else " or ")+w(x,1) # disjunction
    #infix("||", 503).__repr__=        lambda x: w(x,0)+r"\ \text{or}\ "+w(x,1) # P9 disjunction to LaTeX
    infix("\\And", 503).__repr__=lambda x: w(x,0)+(" & " if P9 else " and ")+w(x,1) # conjunction
    infix("&", 503).__repr__=         lambda x: w(x,0)+r"\ \text{and}\ "+w(x,1) # P9 conjunction to LaTeX
    infix("\\implies", 504).__repr__ =lambda x: w3(x,0)+(" -> " if P9 else " <= ")+w3(x,1) # implication
    infix("->", 504).__repr__ =       lambda x: w2(x,0)+"\\implies "+w2(x,1)
    infix("\\iff", 505).__repr__ =    lambda x: w3(x,0)+(" <-> " if P9 else " == ")+w3(x,1) # if and only if
    infix("\\mid", 550).__repr__ =    lambda x: str(x.a[0])+" mid "+str(x.a[1]) # such that
    infix("\\models", 550).__repr__ = lambda x: "check("+str(x.a[0])+",\""+str(x.a[1])+"\")" # check if A satisfies phi
    infix("\\vdash", 550).__repr__ =  lambda x: "p9(pyp9("+str(x.a[0])+"),[pyp9(\""+str(x.a[1])+"\")],2,60)[0]" # proves
    infix("\\nvdash", 550).__repr__ = lambda x: "p9(pyp9("+str(x.a[0])+"),[pyp9(\""+str(x.a[1])+"\")],10,0)[0]" # disproves
    prefix("show",310).__repr__ =     lambda x: "show("+str(x.a[0])+")" #show poset or (semi)lattice
    postfix("?", 600).__repr__ =      lambda x: str(x.a[0])+"?" # calculate value and show it
    symbol("(end)")

macros=r"""
\renewcommand{\And}{\ \text{and}\ }
\newcommand{\Or}{\ \text{or}\ }
\newcommand{\Not}{\text{not}\ }
\newcommand{\Mod}{\text{Mod}}
\newcommand{\Con}{\text{Con}}
\newcommand{\Pre}{\text{Pre}}
\newcommand{\m}{\mathbf}
\newcommand{\bb}{\mathbb}
\newcommand{\cc}{\mathcal}
\newcommand{\s}{\text}
"""

init_symbol_table()

def tokenize(st):
    i = 0
    while i<len(st):
        tok = st[i]
        j = i+1
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
            tok = st[i:j]
            symbol(tok)
            if j<len(st) and st[j]=='(': prefix(tok, 1200) #promote tok to function
        elif "0"<=tok<="9": #read (decimal) number in scientific notation
            while j<len(st) and ('0'<=st[j]<='9' or st[j]=='.'):# in ['.','e','E','-']):
                j+=1
            tok = st[i:j]
            symbol(tok)
        elif tok not in " '(,)[]{}\\|\n": #read operator string
            while j<len(st) and not alpha_numeric(st[j]) and \
                  st[j] not in " '-(,)[]{}\\\n": j+=1
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

def parse(str):
    global token, next
    next = tokenize(str).__next__
    token = next()
    return expression()

ttt=parse(".")

def ast(t):
    if len(t.a)==0: return '"'+t.sy+'"'
    return '("'+t.sy+'",'+", ".join(ast(s) for s in t.a)+")"

def pyla(p,newl=False): # convert Python object to LaTeX string
  if type(p)==frozenset:
    try:
      sp = sorted(p)
    except:
      sp = p
    return "\\{"+", ".join(pyla(el,True) for el in sp)+"\\}" if len(p)>0 else "\\emptyset"
  if type(p)==list:  return "["+", ".join(pyla(el,True) for el in p)+"]"
  if type(p)==tuple: return "("+", ".join(pyla(el,True) for el in p)+")"
  if type(p)==bool:  return "\mathbf{"+str(p)+"}"
  if type(p)==Model: return modelLa(p)
  if type(p)==Proof: return proofLa(p)
  if type(p)==str:
    if p=="N": return "\\text{No counterexample after 10 seconds}"
    try:
      st =  str(parse(p if p[0]!="_" else "\\"+p[1:]))
    except: pass
    if st[0]=="_": st = "\\"+st[1:]
    if newl and len(st)>=20: return "\\newline\n"+st
    #if newl and len(st)>=5: return " \\ "+st
    return st
  st =  str(p)
  #if newl and len(st)>=20: return "\\newline\n"+st
  return st

# Translate from Prover9 symbols to LaTeX symbols
p92la = {"*":"\\cdot", "^":"\\wedge", "v":"\\vee", "O":"{}^{-1}", "<=":"\\le", "~":"\\sim",
         "&":"\\ \\text{and}\\ ", "|":"\\ \\text{or}\\ ",
         "->":"\\implies", "<->":"\\iff", "all":"\\forall", "exists":"\\exists"}

def p92lasym(st):
  return p92la[st] if st in p92la.keys() else st

def p9la(st): # convert Prover9 ast to LaTeX string
  try:
    if st.find("#")==-1: return str(parse(st.replace("$","")))
    return str(parse(st[:st.find("#")]))+"\\text{ goal}"
  except: return st

def pyp9(p): # convert Python object to Prover9 input
  if type(p)==frozenset or  type(p)==list:
    return [pyp9(elmt) for elmt in p]
  #print(str(p))
  return str(p)

def strorval(p):
  #return subterm as an evaluated string or if eval fails, just as a string
  if P9: return 'r\"'+str(p)+'\"'
  try:
    val = eval(str(p))
    return str(val)
  except:
    return 'r\"'+str(p)+'\"'

def converse(R):
  return frozenset((x[1],x[0]) for x in R if len(x)==2)

def power(s,t):
  #print(type(s),s,type(t),t)
  if type(s)==str:
    if t=="-1":
      return "O("+s+")"
  return s**t

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

def compatiblepreorders(A, precon=True, sym=False):
  signum={
  "-":"C(x,y)->C(-y,-x)",
  "~":"C(x,y)->C(~y,~x)",
  "*":"C(x,y)->C(x*z,y*z)&C(z*x,z*y)",
  "\\":"C(x,y)->C(y\ z,x\ z)&C(z\ x,z\ y)",
  "/":"C(x,y)->C(x/z,y/z)&C(z/y,z/x)",
  "^":"C(x,y)->C(x^z,y^z)&C(z^x,z^y)",
  "v":"C(x,y)->C(x v z,y v z)&C(z v x,z v y)",
  }
  m=A.cardinality
  compat = ["C(x,y)&C(y,z)->C(x,z)"]+(["x<=y->C(x,y)"] if precon else ["C(x,x)"])
  for o in A.operations.keys():
    if o in signum.keys(): compat += [signum[o]]
    elif type(A.operations[o])!=int: raise SyntaxError("Operation not handled")
  c=prover9(A.diagram("")+compat,[],100000,0,m,noniso=False)
  if sym:
    for x in c:
      for i in range(m):
        for j in range(m):
          if x.relations["C"][i][j]==0: x.relations["C"][j][i]=0
  return frozenset([rel2pairs(x.relations["C"]) for x in c])

def precongruences(A):
  if type(A)==Model: return compatiblepreorders(A)
  return [compatiblepreorders(x) for x in A]

def congruences(A):
  if type(A)==Model: return frozenset(eqrel2partition(x) for x in compatiblepreorders(A,False,True))
  return [frozenset(eqrel2partition(x) for x in compatiblepreorders(y,False,True)) for y in A]

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

def show(K): # show a list of Mace4 models using graphviz or show a set of subsets or partitions
  if type(K)==Model: K=[K]
  if type(K)==list and len(K)>0 and type(K[0])==Model:
    st = ""
    if "<=" in K[0].relations.keys(): st += "<=d "
    if "^" in K[0].operations.keys(): st += "^d "
    if "v" in K[0].operations.keys(): st += "v "
    if "*" in K[0].operations.keys(): st += "*d "
    if st!="" and st[-1]==" ": st = st[:-1]
    m4diag(K,st)
  elif type(K)==frozenset:
    if len(K)==0: raise Error("Can't show Hasse diagram of an empty set")
    k = list(K)
    S = range(len(K))
    if all(type(x)==frozenset for x in k[0]): 
      U = union(k[0])
      if all(all(type(y)==frozenset for y in x) and union(x)==U for x in k[1:]): #assume K is a set of partitions
        li = [[all(any(x<=y for y in k[j]) for x in k[i]) for i in S] for j in S]
      else: li = [[k[i]<=k[j] for i in S] for j in S]
    else: li = [[k[i]<=k[j] for i in S] for j in S]
    m4diag([Model(cardinality=len(k),relations={"<=":li})])
  elif type(K)==list:
    for x in K: show(x)
    
def check(structure,FOformula_list,info=False):
  FOformula_l=[FOformula_list] if type(FOformula_list)==str else FOformula_list
  for st in FOformula_l:
    lt = []
    if "<=" in st:
      if "+" in st: lt = ["x<=y <-> x+y=y"]
      if "*" in st: lt = ["x<=y <-> x*y=x"]
      if "v" in st: lt = ["x<=y <-> x v y=y"]
      if "^" in st: lt = ["x<=y <-> x^y=x"]
    li = prover9(structure.diagram("")+lt,[st],1000,0,structure.cardinality,one=True)
    if li!=[]:
      if info: return li+[st+" fails"]
      return False
  return True

def proofLa(P):
  #print(str(dir(P)))
  st = "\\begin{array}{rll}"
  for x in P.proof:
    st+=str(x[0])+"&"+p9la(x[1])+"&"+str(x[2])[1:-1]+"\\\\\n"
  return st+"\\end{array}"

def modelLa(A):
  n = A.cardinality
  o = A.operations
  r = A.relations
  st = "{\\scriptsize\\left["
  for rl in r.keys():
    #if type(o[fn])!=list: st+=fn+"="+str(o[fn])+",\ \n"
    if type(r[rl][0])!=list: 
      st+=p92la[rl]+" = \\{"+",".join(str(i) for i in range(n) if r[rl][i])+"\\},\ \n"
    else: st+="\\begin{array}{c|"+n*"c"+"}\n"+\
      p92lasym(rl)+"&"+"&".join(str(i) for i in range(n))+r"\\\hline"+"\n"+\
        (r"\\"+"\n").join(str(i)+"&"+"&".join((str(r[rl][i][j]) if r[rl][i][j] else "")
        for j in range(n)) for i in range(n))+"\\end{array},\ \n"
  for fn in o.keys():
    if type(o[fn])!=list: st+=fn+"="+str(o[fn])+",\ \n"
    elif type(o[fn][0])!=list: 
      st+="\\begin{array}{c}\n"+(r"\\"+"\n").join((str(i)+p92lasym(fn)\
        if fn in ["O","'"] else p92lasym(fn)+str(i))+"="+str(o[fn][i]) for i in range(n))+"\\end{array},\ \n"
    else: st+="\\begin{array}{c|"+n*"c"+"}\n"+\
      p92lasym(fn)+"&"+"&".join(str(i) for i in range(n))+r"\\\hline"+"\n"+\
        (r"\\"+"\n").join(str(i)+"&"+"&".join(str(o[fn][i][j]) 
        for j in range(n)) for i in range(n))+"\\end{array},\ \n"
  return st[:-4]+"\\right]}\n"

# Convert (a subset of) LaTeX input to valid Python+provers(+sympy later)
# Display LaTeX with calculated answers inserted
# Return LaTeX and/or Python code as a string

def nextmath(st,i): #find next j,k>=i such that st[j:k] is inline or display math
  j = st.find("$",i)
  if j==-1: return (-1,0,False)
  if st[j+1]=="$":
    k = st.find("$$",j+2)
    return (j+2,k,True)
  else:
    return (j+1,st.find("$",j+1),False)

def process(st, info=False, nocolor=False):
  # convert st (a LaTeX string) to Python/Prover9 code and evaluate it
  t=parse(st)
  if info:
    print(ast(t))
    print(t)
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
    if info: print(val)
    return ("" if nocolor else "\color{green}")+macros+st+("" if nocolor else "\color{blue}")+" = "+pyla(val)
  except:
    return ("" if nocolor else "\color{green}")+macros+st

def lapy(st, info=False, output=False, nocolor=False):
  st = re.sub("%.*?\n","\n",st) #remove LaTeX comments
  (j,k,d) = nextmath(st,0)
  out = st[0:j]
  while j!=-1 and k!=-1:
    out += process(st[j:k],info,nocolor)
    p = k
    (j,k,d) = nextmath(st,k+(2 if d else 1))
    out += st[p:j] if j!=-1 else st[p:]
  display(Markdown(out))
  if output: print(out)

def test(st, info=True):
  display(Math(st))
  t=parse(st)
  if info:
    print(ast(t))
    print(t)
  try:
    val=eval(str(t))
    if info: print(val)
    display(Math(pyla(val)));print()
  except:
    try:
      exec(str(t),globals())
    except:
      if info: print("no result")
    print()

P9=True # switch the parser into Prover9 mode
