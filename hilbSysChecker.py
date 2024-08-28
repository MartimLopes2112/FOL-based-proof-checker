from functools import reduce

class Signature:

    def __init__(self, varChecker = lambda v: (len(v)>3 and v[:3]=='var') or v in ['x','y','z','n'],
                predChecker = lambda p: p in [('=',2),('∊',2),('p',1)],
                funcChecker = lambda f: f in [('f',1), ('c',0)],
                binaryPredicates = ['=','∊']) -> None:
        self.predChecker = predChecker
        self.funcChecker = funcChecker
        self.varChecker = varChecker
        self.binaryPredicates = binaryPredicates

    #For an n-ary symbol 'g', we define:
    #-Signature Form of g: ('g', n)
    #-Natural Form of g: g appearing in a term, variable, or atomic formula

    @staticmethod
    def __getSignatureFormOfG(G) -> tuple[str , int]:
        '''extends the functionality of the functions bellow to Term type arguments'''
        if type(G) == tuple:
            return G
        elif type(G)==Term:
            return (G.mainSymbol,len(G.args))
        elif type(G)==Formula:
            if G.fType != 'atomic': raise Exception(f'{G} must be an atomic formula')
            else:
                return (G.args[0],len(G.args[1]))
        elif type(G)==str:return (G,0)

        raise Exception(f'{G} has type {type(G)}, which is unavailable')

    def CheckPredicate(self,p):
        return self.predChecker(self.__getSignatureFormOfG(p))
    
    def CheckVariable(self,v):
        return self.varChecker(self.__getSignatureFormOfG(v)[0])
    
    def CheckFunction(self,f):
        return self.funcChecker(self.__getSignatureFormOfG(f))

class Term:

    def __init__(self,mainSymbol:str,args :list['Term'] = [],Sigma = Signature()) -> None:

        if args==[]:
            if not Sigma.CheckFunction(mainSymbol):
                self.isVariable = True
                if not Sigma.CheckVariable(mainSymbol):
                    raise Exception(f'Something is wrong with the definition of the variable {mainSymbol}')
            else:
                self.isVariable = False

            self.mainSymbol = mainSymbol
            self.args = []
            self.Sigma = Sigma
        else:

            self.isVariable = False
            self.Sigma = Sigma
            self.mainSymbol = mainSymbol
            self.args = args

            if not self.Sigma.CheckFunction((mainSymbol,len(args))):
                raise Exception(f'Something is wrong with the definition of the term {mainSymbol}({args})')
            for t in self.args:
                if type(t) != Term:
                    raise Exception(f'Something wrong with argument {t} of {mainSymbol}')
                
    def __eq__(self, value: object) -> bool:
        return type(value)== Term and value.mainSymbol == self.mainSymbol and value.args == self.args
    
    def __hash__(self) -> int:
        return hash((self.mainSymbol,*self.args))
    
    def swapOccurrences(self,x : 'Term',c : 'Term') -> 'Term':
        '''swaps every occurrence of x for the term c'''

        if not x.isVariable: raise Exception(f'{x} is not a variable')

        def aux_func(t:Term)->Term:
            if t.args == []:
                if t==x:
                    return c
                return t
            else:
                return t.swapOccurrences(x, c)

        return Term(self.mainSymbol, [aux_func(v) for v in self.args], self.Sigma)
    
    def variables(self)->set['Term']:
        def func_aux(t:'Term')->set['Term']:
            if not t.isVariable:
                return t.variables()
            return {t}
        
        return set().union(*map(func_aux,self.args))
    
    def text(self)->str:
        '''returns the term in text form'''
        if self.args == []:
            return self.mainSymbol
        else:
            return f'{self.mainSymbol}({reduce(lambda x,y: x+ ', '+ y, map(lambda x: x.text(), self.args))})'
       
class Formula:
    '''
    fType: ->, ~, forall, atomic\n
    args: list of maximal subformulas in case of -> and ~\n 
          [p,[x_1,...,x_n]] in the case of an n-ary atomic formula\n
          [A,varx] in the case of universal forall
    '''

    def __init__(self,fType : str,args : list = [],Sigma = Signature()) -> None:
        self.Sigma = Sigma
        self.fType = fType
        self.args = args

        if not fType in ['~','atomic','->','forall']: raise Exception(f'Invalid fType "{fType}"')

        if self.fType == 'atomic':
            if not self.Sigma.CheckPredicate((args[0],len(args[1]))):
                raise Exception(f'Something is wrong with the definition of the atomic formula {args}')
            for t in self.args[1]:
                if type(t) != Term:
                    raise Exception(f'{t} does not have type "Term"')
        elif self.fType == 'forall':
            if type(args[0]) != Formula or not Sigma.CheckVariable(args[1]):
                raise Exception(f'Something is wrong with the definition of the formula "for all {args[0]}, {args[1]}"')
            if type(args[1])!= Term: raise Exception(f'{args[1]} is not a Term, but a {type(args[1])}')
        else:
            for A in self.args:
                if type(A)!=Formula:
                    raise Exception("{A} is not a formula")
        return
                
    def __eq__(self, value: object) -> bool:return type(value) == Formula and self.args == value.args

    def __hash__(self) -> int:return hash((self.fType,*self.args))

    def swapFreeOccurrences(self,x :Term,t :Term)->'Formula':
        if self.fType == 'forall':
            if self.args[1] != x:
                return Formula('forall', [self.args[0].swapFreeOccurrences(x,t),self.args[1]])
            else: return self
        else:
            return Formula(self.fType,[self.args[0],[v.swapOccurrences(x,t) for v in self.args[1]]],self.Sigma)
    
    def freeVariables(self)->set:
        if self.fType == 'forall':
            return set(filter(lambda x: x != self.args[1],self.args[0].freeVariables()))
        elif self.fType == 'atomic':
            return set().union(map(lambda t: t.variables(), self.args[1]))
        else: return set().union(map(lambda A: A.freeVariables(), self.args[1]))

    def freeTermCheck(self,t: Term,x:Term)->bool:
        '''Checks whether every free occurrence of x in A is not in scope of a quantifier for variable of t'''
        
        def aux(curFormula: Formula,scope: set[Term])->bool:
            if curFormula.fType == 'forall':
                if curFormula.args[1] == x: return True
                return aux(curFormula.args[0],scope | {curFormula.args[1]})
            elif curFormula.fType == 'atomic':
                if any(map(lambda t: x in t.variables(), curFormula.args[1])):#checks if x occurs in curFormula
                    return set().intersection(scope, t.variables()) == set() #returns true iff the intersection of scope and var(t) is empty
                return True #if x doesn't occur in curFormula we're fine
            else:
                return all(map(lambda A:aux(A,scope), curFormula.args))
        
        return aux(self,set())


    def isThisObtainedBySwapping(self,A:'Formula',x:Term, t = None):
        '''Checks whether this formula is of the form [A]^x_t for some term t, returns t '''
        if self.fType != A.fType: return False
        if self.fType == 'forall':
            return not( (self.args[1] != A.args[1]
                         ) or (self.args[1] == x and self.args[0] != A.args[0]
                               ) or (self.args[1] != x and self.args[0] == A.args[0].swapFreeOccurrences(x,t)))
        if self.fType == 'atomic':
            pass
        else:
            return len(self.args[1]) == len(A.args[1]) and all(
                map(lambda i: self.args[1][i].isThisObtainedBySwapping(A.args[1][i],x,t), range(len(self.args[1]))))
        
    def text(self)->str:
        if self.fType == 'atomic':
            if len(self.args[1]) == 2:
                return f'{self.args[1][0].text()} {self.args[0]} {self.args[1][1].text()}'
            return f'{self.args[0]}({reduce(lambda x,y: x+ ', '+ y, map(lambda x: x.text(), self.args[1]))})'

        elif self.fType == '->':
            if self.args[0].fType in ['atomic', '~']:
                s = self.args[0].text()
            else: s = f'({self.args[0].text()})'
            s+='⇒'
            if self.args[1].fType in ['atomic', '~','forall']:
                s += self.args[1].text()
            else: s += f'({self.args[1].text()})'
            return s
        
        elif self.fType == '~':
            if self.args[0].fType in ['atomic', '~','forall']: #this declutters the expression
                return f'¬{self.args[0].text()}'
            return f'¬({self.args[0].text()})'
        else:
            if self.args[0].fType in ['atomic', '~','forall']:
                return f'∀{self.args[1].text()}, {self.args[0].text()}'
            return f'∀{self.args[1].text()}, ({self.args[0].text()})'

def __parBlock(i:int,L:str)-> tuple[int,int]:
    '''Finds least parenthesis block where ( appears at least in index i. Returns indexes of parenthesis'''
    try:
        l=L.index('(',i)
        openCount=1
        closeCount=0
        r=l
        while openCount!=closeCount:
            r=r+1
            if L[r]=='(':openCount+=1
            elif L[r]==')': closeCount+=1
        return (l,r)
    except ValueError:
        return (-1,-1)
    
def __stringStriptease(L:str)->list:
    '''strips L of parenthesis blocks and returns the list of indexes from L that survived the stripping'''
    K=L
    KIndexes = set(range(len(L)))
    P = __parBlock(0,K)
    while P != (-1,-1):
        K = K[:P[0]] + K[P[1]+1:]
        KIndexes= KIndexes & set(filter(lambda i: i<P[0] or  P[1]<i, range(len(L))))
        P = __parBlock(0,K)
    return [K,list(KIndexes)]

def __separateArgumentsAndMainSymbol(L:str)->list:
    '''Transforms "Mainsymbol(arg1,...,argn)" into ["MainSymbol",["arg1",...,"argn"]] '''
    P = __parBlock(0,L)
    argsStr,argsStrIndexes = __stringStriptease(L[P[0]+1:-1]) #string of arguments with "(...)" ommited, this also removes excessive commas

    #now i want to find the indexes of the commas that separate the arguments in the string L[P[0]+1:-1]:
    commaIndexes=[-1]  #of L[P[0]+1:-1] together with -1 and len(L[P[0]+1:-1])
    nextComma = argsStr.find(',',0)
    while nextComma!=-1:
        commaIndexes.append(argsStrIndexes[nextComma])
        nextComma=argsStr.find(',',nextComma+1)
    commaIndexes.append(len(L[P[0]+1:-1]))

    args = []
    for j in range(len(commaIndexes)-1):
        args.append(L[P[0]+1:-1][commaIndexes[j]+1:commaIndexes[j+1]])
    
    return [L[:P[0]],args]        

def ST(s:str,Sigma = Signature())->Term:
    '''returns Term expressed in string expression'''
    s=s.replace(' ','')

    if __parBlock(0,s) ==(-1,-1): #it's either a constant or a variable
        return Term(s,Sigma=Sigma)
    else:
        symbols = __separateArgumentsAndMainSymbol(s)
        return Term(symbols[0], list(map(ST,symbols[1])))

def SF(s:str,Sigma = Signature())->Formula:
    '''returns Formula expressed in string expression'''
    s=s.replace(' ','')

    par = __parBlock(0,s)
    ##look for superfluous parenthesis
    if par ==(0,len(s)-1): return SF(s[1:-1],Sigma=Sigma)

    ##Algorithm idea:
    # k := s stripped from blocks of parenthesis
    # 1.Look for a implication sign oustide parenthesis
    # 2.Look for negation/ forall/ predicate sign in the begining

    k,kIndexes = __stringStriptease(s)    

    if '->' in k:
        symbIndex = 0
        kIndexes.sort()
        for i in kIndexes:
            if i+1 in kIndexes and s[i:i+2] == '->':
                symbIndex = i
        ## ...->...
        #-----^------
        return Formula('->', [SF(s[:symbIndex],Sigma=Sigma),SF(s[symbIndex+2:],Sigma)])
    if '⇒' in k:
        for i in kIndexes:
            if s[i]=='⇒': symbIndex = i
        
        return Formula('->', [SF(s[:symbIndex],Sigma),SF(s[symbIndex+1:],Sigma)],Sigma)
    if s[0] in ['~','¬']:
        return Formula('~', [SF(s[1:],Sigma)],Sigma)
    if s[0] == '∀':
        commaInd = s.index(',')
        return Formula('forall', [SF(s[commaInd+1:],Sigma),ST(s[1:commaInd],Sigma)],Sigma)
    if len(s)>6 and s[:6]=='forall':
        commaInd = s.index(',')
        return Formula('forall', [SF(s[commaInd+1:],Sigma),ST(s[6:commaInd],Sigma)],Sigma)
    ##Só resta o caso em que é fórmula atómica
    #se o predicato for binário, é preciso procurá-lo no meio da fórmula
    for p in Sigma.binaryPredicates:
        if p in 

    
    #para o caso em que a fórmula é da forma p(x_1,...,x_n) faz-se:
    PredStr = __separateArgumentsAndMainSymbol(s)
    
    if not Sigma.CheckPredicate((PredStr[0],len(PredStr[1]))): raise Exception(f'Predicate {PredStr[0]} with {len(PredStr[1])} arguments does not exist!')

    return Formula('atomic',[PredStr[0],list(map(ST,PredStr[1]))],Sigma)

    

    




        
class DeductiveSystem:

    def __FOL_AXIOM_CHECKER(self,phi:Formula):
        if phi.fType=='->':
            subL, subR = phi.args
            subL:Formula
            subR:Formula

            #Ax1 and Ax3
            if subR.fType == '->':
                if subR.args[1] == subL: return True, 'FOL Ax. 1'
                elif subL == Formula('->',[Formula('~',subR.args[1],self.Sigma),
                                           Formula('~', subR.args[0],self.Sigma)],self.Sigma): return True, 'FOL Ax. 3'

            #Ax2
            if subL.fType == '->':
                if subL.args[1] == '->':
                    A, B, C = subL.args[0] , subL.args[1].args[0], subL.args[1].args[1]
                    if subR == Formula('->',
                         [Formula('->',[A,B],self.Sigma), Formula('->',[A,C],self.Sigma)],self.Sigma):
                        return True, 'FOL Ax. 2'

            ###FALTA AX4 E AX5
            if subL.fType=='forall':
                x = subL.args[1]
                #Ax4
                if subL.args[0].swapFreeOccurrences(x,x) == subR:
                    return True
                elif x in subL.freeVariables():
                    #recursion in the structures of subL and subR
                    pass
                    # (...)
            
    def __ZFC_AXIOM_CHECKER(self,phi:Formula):

        #Extensionality
        #sf('forall[varx](forall[vary](forall[varz]( in (varz,varx) )))',self.Sigma)
        pass

            



    def __init__(self,Sigma = Signature()) -> None:
        self.Sigma = Sigma
        pass
    
    




