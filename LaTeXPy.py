# Python program to parse LaTeX formulas and produce Python/Prover9 expressions

# Terms are read using Vaughn Pratt's top-down parsing algorithm
# by Peter Jipsen, version 2022-12-31 distributed under GPL v3 or later
!pip install provers
from provers import *
from IPython.display import *
import math, itertools, re

def is_postfix(t):
    return hasattr(t,'leftd') and len(t.a)==1

def w(subt, t): 
    # decide when to add parentheses during printing of terms
    return str(subt) if subt.lbp < t.lbp or subt.a==[] or \
        (subt.sy==t.sy and subt.lbp==t.lbp) or \
        (not hasattr(subt,'leftd') or not hasattr(t,'leftd')) or \
        (is_postfix(subt) and is_postfix(t)) else "("+str(subt)+")"

def w2(subt, t):
  #if subt.sy=='k' and t.sy=='join' or t.sy=='meet': print subt.lbp, t.lbp
  return str(subt) if subt.lbp < t.lbp or subt.a==[] \
        or (not hasattr(subt,'leftd') and subt.lbp==1200) \
        else "("+str(subt)+")"

def w3(subt, t): # 
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
         return w(self.a[0], self)+" "+self.sy+" "+w(self.a[1], self)
        else:
         return self.sy+"("+",".join([w(obj, self) for obj in self.a])+")"

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
      else "frozenset(["+",".join([strorval(y) for y in x.a])+"])" if len(x.a)<2 or x.a[1].sy!='\\dots'\
      else "frozenset(range("+str(x.a[0])+","+str(x.a[2])+"+1))"
    symbol("]")
    symbol("\\}")
    symbol(",")

    postfix("!",300).__repr__ =       lambda x: "math.factorial("+str(x.a[0])+")"
    postfix("'",300).__repr__ =       lambda x: str(x.a[0])+"'"
    prefix("\\ln",310).__repr__ =     lambda x: "math.log("+str(x.a[0])+")"
    prefix("i",310).__repr__ =        lambda x: "{"+str(x.a[0])+"^{-1}}" #P9 name for inverse
    preorinfix("\\sim",310).__repr__= lambda x: "~"+w(x.a[0],x)
    preorinfix("-",310).__repr__ =    lambda x: "-"+w(x.a[0],x)\
      if len(x.a)==1 else str(x.a[0])+" - "+w(x.a[1], x) #negative or minus
    infix(":", 450).__repr__ =        lambda x: str(x.a[0])+": "+w3(x.a[1],x) # for f:A\to B
    infix("^", 300).__repr__ =        lambda x: "converse("+str(x.a[0])+")"\
      if str(x.a[1].sy)=='\\smallsmile' else "i("+str(x.a[0])+")"\
      if P9 and str(x.a[1])=="-1" else  w2(x.a[0],x)+"\\wedge "+w2(x.a[1],x)\
      if P9 else w2(x.a[0],x)+"**"+w2(x.a[1],x) # power
    infix("_", 300).__repr__ =        lambda x: str(x.a[0])+"["+w(x.a[1],x)+"]" # sub
    infix("*", 311).__repr__ =        lambda x: w2(x.a[0],x)+"*"+w2(x.a[1],x) # times
    infix("\\cdot", 301).__repr__ =   lambda x: w2(x.a[0],x)+"*"+w2(x.a[1],x) # times
    infix("/", 313).__repr__ =        lambda x: w(x.a[0],x)+"/"+w(x.a[1],x) # over
    infix("\\backslash", 303).__repr__=lambda x: w(x.a[0],x)+"\ "+w(x.a[1],x) # under
    infix("+", 312).__repr__ =        lambda x: w2(x.a[0],x)+" + "+w2(x.a[1],x) # plus
    infix("\\wedge", 312).__repr__ =  lambda x: w2(x.a[0],x)+" ^ "+w2(x.a[1],x) # meet
    infix("\\vee", 313).__repr__ =    lambda x: w2(x.a[0],x)+" v "+w2(x.a[1],x) # join
    infix("v", 313).__repr__ =        lambda x: w2(x.a[0],x)+"\\vee "+w2(x.a[1],x) # join
    infix("\\to", 314).__repr__ =     lambda x: w(x.a[0],x)+" -> "+w(x.a[1],x)
    symbol("\\top").__repr__ =        lambda x: "T"
    symbol("\\bot").__repr__ =        lambda x: "0"
    
    infix("\\times", 322).__repr__ =  lambda x: "frozenset(itertools.product("+w(x.a[0],x)+","+w(x.a[1],x)+"))" #product
    infix("\\cap", 323).__repr__ =    lambda x: w(x.a[0],x)+" & "+w(x.a[1],x) # intersection
    infix("\\cup", 324).__repr__ =    lambda x: w(x.a[0],x)+" | "+w(x.a[1],x) # union
    infix("\\setminus", 325).__repr__=lambda x: w(x.a[0],x)+" - "+w(x.a[1],x) # setminus
    infix("\\oplus", 326).__repr__ =  lambda x: w(x.a[0],x)+" ^ "+w(x.a[1],x) # setminus
    prefix("\\bigcap",350).__repr__ = lambda x: "intersection("+str(x.a[0])+")" # intersection of a set of sets
    prefix("\\bigcup",350).__repr__ = lambda x: "union("+str(x.a[0])+")" # union of a set of sets
    prefix("\\mathcal",350).__repr__= lambda x: "powerset("+str(x.a[0].a[0])+")"\
      if str(x.a[0].sy)=="P" else "cal"+str(x.a[0]) # powerset
    infix(";", 303).__repr__ =        lambda x: "relcomposition("+w(x.a[0],x)+","+w(x.a[1],x)+")" # relation composition
    prefix("\\mathbf",350).__repr__ = lambda x: "mbf"+str(x.a[0].sy) # algebra or structure or theory
    prefix("\\mathbb",350).__repr__ = lambda x: "mbb"+str(x.a[0].sy) # blackboard bold
    prefix("\\text{Mod}",350).__repr__=lambda x: "[z for y in p9(pyp9("+str(x.a[0])+"),[],"+(str(x.a[2]) if len(x.a)>2\
      else "100")+",0,["+str(x.a[1])+"])[2:] for z in y]"
    prefix("\\text{Con}",350).__repr__=lambda x: "congruences("+str(x.a[0])+")" # set of congruences of an algebra
    prefix("\\text{Pre}",350).__repr__=lambda x: "precongruences("+str(x.a[0])+")" # set of precongruences of a po-algebra
    infix("\\vert", 365).__repr__ =   lambda x: w(x.a[1],x)+"%"+w(x.a[0],x)+"==0" # divides
    infix("\\in", 370).__repr__ =     lambda x: w(x.a[0],x)+" in "+w(x.a[1],x) # element of
    infix("\\subseteq", 370).__repr__=lambda x: w(x.a[0],x)+" <= "+w(x.a[1],x) # subset of
    infix("\\subset", 370).__repr__ = lambda x: w(x.a[0],x)+" < "+w(x.a[1],x) # proper subset of
    infix("=", 405).__repr__ =        lambda x: w(x.a[0],x)+(" = " if P9 else " == ")+w(x.a[1],x) # assignment or identity
    infix("\\ne", 405).__repr__ =     lambda x: w(x.a[0],x)+" != "+w(x.a[1],x) # nonequality
    infix("!=", 405).__repr__ =       lambda x: w(x.a[0],x)+"\\ne "+w(x.a[1],x) # nonequality
    infix("\\le", 405).__repr__ =     lambda x: w2(x.a[0],x)+" <= "+str(x.a[1])
    infix("<=", 405).__repr__ =       lambda x: w2(x.a[0],x)+"\\le "+str(x.a[1])
    infix("\\ge", 405).__repr__ =     lambda x: w2(x.a[0],x)+" >= "+str(x.a[1])
    infix("<", 405).__repr__ =        lambda x: w2(x.a[0],x)+" < "+str(x.a[1])
    infix(">", 405).__repr__ =        lambda x: w2(x.a[0],x)+" > "+str(x.a[1])
    prefix("\\neg",450).__repr__=     lambda x: "not "+w(x.a[0],x) # negation
    prefix("\\forall",450).__repr__ = lambda x: "all("+str(x.a[-1]).replace(" = "," == ")+\
            "".join(" for "+str(x) for x in x.a[:-1])+")" # universal quantifier
    prefix("\\exists",450).__repr__ = lambda x: "any("+str(x.a[-1]).replace(" = "," == ")+\
            "".join(" for "+str(x) for x in x.a[:-1])+")" # existential quantifier
    infix("\\text{or}", 503).__repr__=lambda x: w(x.a[0],x)+(" | " if P9 else " or ")+w(x.a[1],x) # disjunction
    #infix("||", 503).__repr__=        lambda x: w(x.a[0],x)+r"\ \text{or}\ "+w(x.a[1],x) # P9 disjunction to LaTeX
    infix("\\text{and}", 503).__repr__=lambda x: w(x.a[0],x)+(" & " if P9 else " and ")+w(x.a[1],x) # conjunction
    infix("&", 503).__repr__=         lambda x: w(x.a[0],x)+r"\ \text{and}\ "+w(x.a[1],x) # P9 conjunction to LaTeX
    infix("\\implies", 504).__repr__ =lambda x: w3(x.a[0],x)+(" -> " if P9 else " <= ")+w3(x.a[1],x) # implication
    infix("->", 504).__repr__ =       lambda x: w2(x.a[0],x)+"\\implies "+w2(x.a[1],x)
    infix("\\iff", 505).__repr__ =    lambda x: w3(x.a[0],x)+(" <-> " if P9 else " == ")+w3(x.a[1],x) # if and only if
    infix("\\mid", 550).__repr__ =    lambda x: str(x.a[0])+" mid "+str(x.a[1]) # such that
    infix("\\models", 550).__repr__ = lambda x: "check("+str(x.a[0])+",\""+str(x.a[1])+"\")" # check if A satisfies phi
    infix("\\vdash", 550).__repr__ =  lambda x: "p9(pyp9("+str(x.a[0])+"),[pyp9(\""+str(x.a[1])+"\")],2,60)[0]" # proves
    infix("\\nvdash", 550).__repr__ = lambda x: "p9(pyp9("+str(x.a[0])+"),[pyp9(\""+str(x.a[1])+"\")],10,0)[0]" # disproves
    prefix("show",310).__repr__ =     lambda x: "show("+str(x.a[0])+")" #show poset or (semi)lattice
    postfix("?", 600).__repr__ =      lambda x: str(x.a[0])+"?" # calculate value and show it
    symbol("(end)")

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
            if tok=="\\text": j = st.find("}",j)+1 #extend token to include {...} part
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
    token = next()
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
    st =  str(parse(p if p[0]!="_" else "\\"+p[1:]))
    if st[0]=="_": st = "\\"+st[1:]
    if newl and len(st)>=20: return "\\newline\n"+st
    #if newl and len(st)>=5: return " \\ "+st
    return st
  st =  str(p)
  #if newl and len(st)>=20: return "\\newline\n"+st
  return st

# Translate from Prover9 symbols to LaTeX symbols
p92la = {"*":"\\cdot", "^":"\\wedge", "v":"\\vee", "i":"{}^{-1}", "<=":"\\le", 
         "-":"-", "~":"\\sim", "f":"f", "g":"g",
         "&":"\\ \\text{and}\\ ", "|":"\\ \\text{or}\\ ",
         "->":"\\implies", "<->":"\\iff", "all":"\\forall", "exists":"\\exists"}

def p9la(st): # convert Prover9 ast to LaTeX string
  if st.find("#")==-1: return str(parse(st.replace("$","")))
  return str(parse(st[:st.find("#")]))+"\\text{ goal}"

def pyp9(p): # convert Python object to Prover9 input
  if type(p)==frozenset or  type(p)==list:
    return [pyp9(elmt) for elmt in p]
  return str(p)

def strorval(p):
  #return subterm as an evaluated string or if eval fails, just as a string
  try:
    val = eval(str(p))
    return str(val)
  except:
    return 'r\"'+str(p)+'\"'

def converse(R):
  return frozenset((x[1],x[0]) for x in R if len(x)==2)

def power(s,t):
  print(type(s),s,type(t),t)
  if type(s)==str:
    if t=="-1":
      return "i("+s+")"
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
    else: raise SyntaxError("Operation not handled")
  c=prover9(A.diagram("")+compat,[],100000,0,m,noniso=False)
  if sym:
    for x in c:
      for i in range(m):
        for j in range(m):
          if x.relations["C"][i][j]==0: x.relations["C"][j][i]=0
  return frozenset([rel2pairs(x.relations["C"]) for x in c])

def precongruences(A):
  return compatiblepreorders(A)

def congruences(A):
  return frozenset(eqrel2partition(x) for x in compatiblepreorders(A,False,True))

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
  if type(K)==list:
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
      p92la[rl]+"&"+"&".join(str(i) for i in range(n))+r"\\\hline"+"\n"+\
        (r"\\"+"\n").join(str(i)+"&"+"&".join((str(r[rl][i][j]) if r[rl][i][j] else "")
        for j in range(n)) for i in range(n))+"\\end{array},\ \n"
  for fn in o.keys():
    if type(o[fn])!=list: st+=fn+"="+str(o[fn])+",\ \n"
    elif type(o[fn][0])!=list: 
      st+="\\begin{array}{c}\n"+(r"\\"+"\n").join((str(i)+p92la[fn]\
        if fn in ["i","'"] else p92la[fn]+str(i))+"="+str(o[fn][i]) for i in range(n))+"\\end{array},\ \n"
    else: st+="\\begin{array}{c|"+n*"c"+"}\n"+\
      p92la[fn]+"&"+"&".join(str(i) for i in range(n))+r"\\\hline"+"\n"+\
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
          return st
        return ("" if nocolor else "\color{green}")+st
      return st
    ss = str(t).replace("==","=",1)
    try:
      exec(ss,globals())
    except:
      if info: print("no result")
      return st
    return ("" if nocolor else "\color{green}")+st
  tt = t.a[0]
  st = st.replace("?","")
  if tt.sy=="=":
    ss = str(tt).replace("==","=",1)
    try:
      exec(ss,globals())
    except:
      if info: print("no result")
      return st
    return ("" if nocolor else "\color{green}")+st+("" if nocolor else "\color{blue}")+" = "+pyla(eval(str(tt.a[0])))
  try:
    val=eval(str(tt))
    if info: print(val)
    return ("" if nocolor else "\color{green}")+st+("" if nocolor else "\color{blue}")+" = "+pyla(val)
  except:
    return ("" if nocolor else "\color{green}")+st

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

P9=True
