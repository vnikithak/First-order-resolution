import copy

class Predicate:
    #this class represents a predicate including its name, arguments, negation

    def __init__(self, negate, pname, args):
        self.negate = negate
        self.pname = pname
        self.args = args

    def printPred(self):
        #print predicate as P(a,b)
        if self.negate == True: print('~', end="")
        print(self.pname + '(' + ','.join([arg for arg in self.args]) + ')', end="")
        print()

    def negatesen1(self):
        self.negate=not self.negate

    def contradict(self,other):
        #checks if 2 predicates are complements
        if self.negate==other.negate or self.pname!=other.pname:
            return False
        if len(self.args)!=len(other.args):
            return False
        for i in range(len(self.args)):
            if self.args[i]!=other.args[i]:
                return False
        return True

class Sentence:
    #represents a sentence of predicates
    def __init__(self,singlesen1,preds,numpred):
        self.singlesen1=singlesen1
        self.preds=preds
        self.numpred=numpred

    def printSentence(self):
        for lit in self.preds:
            if lit.negate == True: print('~', end="")
            print(lit.pname + '(' + ','.join([arg for arg in lit.args]) + ')', end="")
            if lit is not self.preds[-1]: print('|', end="")
        print()

def gensen1(s):
    neg=True
    if s[0]!='~':
        neg=False
    for i in range(len(s)):
        if s[i]=='(':
            left=i
        if s[i]==')':
            right=i
    if neg==True:
        name=s[1:left].strip()
    else:
        name=s[0:left].strip()
    args=s[left+1:right].strip().split(',')
    p=Predicate(neg,name,args)
    return p

def isVariable(v):
    if v.islower():
        return True
    else:
        return False

def genCNF(s):
    #generate a Conjunctive normal form for a sentence
    global counter
    var=[]
    t=[]
    left=-1
    preds=[]
    for i in range(len(s)):
        if s[i]=='=':
            left=i
    if left==-1:
        #denotes a single literal
        var={}
        pr=gensen1(s)
        preds.append(pr)
        for p in preds:
            args1=[]
            for a in p.args:
                if isVariable(a):
                    if a in var:
                        a=var[a]
                    else:
                        var[a]='x'+str(counter)
                        counter=counter+1
                        a=var[a]
            for q in p.args:
                if isVariable(q):
                    args1.append(var[q])
                else:
                    args1.append(q)
            p.args=args1
        sen=Sentence(True,preds,1)
    else:
    #denotes a combination of predicates
        num=0
        premise=s[0:left]
        premise=premise.strip()
        premise=premise.split('&')
        for i in premise:
            i=i.strip()
            num+=1
            p=gensen1(i)
            p.negate=not p.negate
            preds.append(p)
        num+=1
        consequent=s[left+2:len(s)].strip()
        p=gensen1(consequent)
        preds.append(p)
        var={}
        for p in preds:
            args1=[]
            for a in p.args:
                if isVariable(a):
                    if a in var:
                        a=var[a]
                    else:
                        var[a]='x'+str(counter)
                        counter=counter+1
                        a=var[a]
            for q in p.args:
                if isVariable(q):
                    args1.append(var[q])
                else:
                    args1.append(q)
            p.args=args1
        sen=Sentence(False,preds,num)
    return sen

def contradict(targ,uni):
    if (targ.pname==uni.pname) and (targ.negate == (not (uni.negate))) and (len(targ.args)==len(uni.args)):
        for i in range(len(targ.args)):
            if (not isVariable(targ.args[i])) and (not isVariable(uni.args[i])):
                if targ.args[i] != uni.args[i]:
                    return False
        return True
    else:
        return False

def contradictcheck(targ,uni):
    #to check if two predicates are complements and can be resolved
    if (targ.pname==uni.pname) and (targ.negate == (not (uni.negate))) and (len(targ.args)==len(uni.args)):
        for i in range(len(targ.args)):
            if (not isVariable(targ.args[i])) and (not isVariable(uni.args[i])):
                if targ.args[i] != uni.args[i]:
                    return False
            else:
                return False
        return True
    else:
        return False



def isVariable(v):
    #check if v is a variable for sake of resolution
    if v.islower():
        return True
    else:
        return False

def unification(targ,uni,sentencek,sentencet):
    #resolve sentences sentencek and sentencet by unifying predicates targ and uni
    result = []
    table= {}
    for i in range(len(targ.args)):
        if not isVariable(uni.args[i]) and isVariable(targ.args[i]):
            if targ.args[i] not in table:
                table[targ.args[i]] = uni.args[i]
            else:
                if table[targ.args[i]]!=uni.args[i]:
                    return False,None
        if not isVariable(targ.args[i]) and isVariable(uni.args[i]):
            if uni.args[i] not in table:
                table[uni.args[i]] = targ.args[i]
            else:
                if table[uni.args[i]]!=targ.args[i]:
                    return False,None
        if isVariable(targ.args[i]) and isVariable(uni.args[i]):
            if targ.args[i]!=uni.args[i]:
                if uni.args[i] not in table:
                    table[uni.args[i]]=targ.args[i]
                else:
                    if isVariable(table[uni.args[i]]) and table[uni.args[i]]!=targ.args[i]:
                        table[targ.args[i]]=table[uni.args[i]]
                    if not isVariable(table[uni.args[i]]) and table[uni.args[i]]!=targ.args[i]:
                        table[targ.args[i]]=table[uni.args[i]]
        if not isVariable(targ.args[i]) and not isVariable(uni.args[i]):
            if targ.args[i]==uni.args[i]:
                table[uni.args[i]]=targ.args[i]
            else:
                return False,None
    for pred in sentencek.preds:
        if pred!=uni:
            newpred=copy.deepcopy(pred)
            for i in range(len(newpred.args)):
                if newpred.args[i] in table:
                    newpred.args[i] = table[newpred.args[i]]
            result.append(newpred)
    for pred in sentencet.preds:
        if pred!=targ:
            newpred=copy.deepcopy(pred)
            for i in range(len(newpred.args)):
                if newpred.args[i] in table:
                    newpred.args[i] = table[newpred.args[i]]
            result.append(newpred)
    nump=len(result)
    if nump==0:
        return True,None
    if nump==1:
        singlepred=True
    else:
        singlepred=False
    s=Sentence(singlepred,result,nump)
    return True,s

KB = []
hashTable = {}
def resolution(hist,sen1):
    global KB
    global hashTable
    for i in range(len(sen1.preds)):
        j=i+1
        while(j<len(sen1.preds)):
            if sen1.preds[i]==sen1.preds[j]:
                sen1.preds.pop(j)
            else:
                j+=1
    i=0
    while(i<len(sen1.preds)):
        flag=False
        j=i+1
        while(j<len(sen1.preds)):
            if contradictcheck(sen1.preds[i],sen1.preds[j]):
                return False
            j+=1
        i+=1
    if hash(sen1) not in hist:
        hist.append(hash(sen1))
    else:
        return False
    for p in sen1.preds:
        if p.pname not in hashTable:
            return False
        for i in hashTable[p.pname]:
            for pr in i.preds:
                if contradict(p,pr)==True:
                    flag,s = unification(p,pr,i,sen1)
                    if flag==False:
                        continue
                    if flag==True and s is None:
                            return True
                    else:
                            boolean = True
                            newhist = hist
                            if not resolution(newhist,s):
                                    boolean = False
                                    break
                            if boolean:
                                return True
                    break
    return False

if __name__ == '__main__':
    counter=0
    readqueries=[]
    readsentences=[]
    queries=[]
    sentences=[]
    infile=open('input.txt', 'r')
    nqueries=int(infile.readline())
    for i in range(0,nqueries):
        queries.append(genCNF((infile.readline()).strip()))
    nsentences=int(infile.readline())
    for i in range(0,nsentences):
        sentences.append(genCNF((infile.readline()).strip()))
    for i in range(len(sentences)):
        for pred in sentences[i].preds:
            if pred.pname not in hashTable:
                hashTable[pred.pname] = list()
            hashTable[pred.pname].append(sentences[i])
    hist = []
    outfile=open('output.txt','w')
    for i in range(len(queries)):
        queries[i].preds[0].negate = not queries[i].preds[0].negate
        #sentences.append(queries[i])
        if queries[i].preds[0].pname not in hashTable:
            outfile.write("FALSE")
            continue
        hashTable[queries[i].preds[0].pname].append(queries[i])
        if(resolution([],queries[i])):
            outfile.write("TRUE")
        else:
            outfile.write("FALSE")
        if i!=len(queries)-1:
            outfile.write('\n')
        hashTable[queries[i].preds[0].pname].remove(queries[i])
    infile.close()
    outfile.close()
