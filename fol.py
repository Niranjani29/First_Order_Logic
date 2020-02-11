import copy
import re

GLOBALCOUNT = 0
KILL_LIMIT = 9000
PRECEDANCE = {'~':4, '&':3, '|':2, '=>':1}
UPPERCASE = ['A','B','C','D','E','F','G','H','I','J','K','L','M','N','O','P','Q','R','S','T','U','V','W','X','Y','Z']
LOWERCASE = ['a','b','c','d','e','f','g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v','w','x','y','z']
pred = {}
KBH = {}
KB = set()
traversal = ''

class pre():
    def __init__(self, pre):
        braceSplit = pre.split('(')
        self.neg = False
        self.name = braceSplit[0]
        self.preStr = pre
        if '~' in braceSplit[0]:
            self.name = braceSplit[0][1:]
            self.neg = True
        args = braceSplit[1][:-1]
        self.para = args.split(',')

    def negative(self):
        self.neg = not self.neg
        self.revision_preStr()

    def __eq__(self, pre):
        return self.__dict__ == pre.__dict__

    def __hash__(self):
        return hash(self.preStr)

    def unify_with_pre(self, pre):
        if self.name == pre.name and len(self.para) == len(pre.para):
            replaceIt = {}
            return unify(self.para, pre.para, replaceIt)
        else:
            return False

    def revision_preStr(self):
        self.preStr = '~'[not self.neg:] + self.name + '(' + ','.join(self.para) + ')'

    def substitute(self, replaceIt):
        if replaceIt:
            for index, arg in enumerate(self.para):
                if arg in replaceIt:
                    self.para[index] = replaceIt[arg]
            self.revision_preStr()
        return self

def unify(pre1_arg, pre2_arg, replaceIt):
    if replaceIt == False:
        return False
    elif pre1_arg == pre2_arg:
        return replaceIt
    elif isinstance(pre1_arg, str) and pre1_arg.islower():
        return unifyIt(pre1_arg, pre2_arg, replaceIt)
    elif isinstance(pre2_arg, str) and pre2_arg.islower():
        return unifyIt(pre2_arg, pre1_arg, replaceIt)
    elif isinstance(pre1_arg, list) and isinstance(pre2_arg, list):
        if pre1_arg and pre2_arg:
            return unify(pre1_arg[1:], pre2_arg[1:], unify(pre1_arg[0], pre2_arg[0], replaceIt))
        else:
            return replaceIt
    else:
        return False

def unifyIt(variable, x, replaceIt):
    if variable in replaceIt:
        return unify(replaceIt[variable], x, replaceIt)
    elif x in replaceIt:
        return unify(variable, replaceIt[x], replaceIt)
    else:
        replaceIt[variable] = x
        return replaceIt

class State():
    def __init__(self, st_str=None):
        if st_str:
            pre_list = st_str.split('|')
            pre_list = map(lambda x:pre(x), pre_list)
            self.pre_set = set(pre_list)
            st_str_list = map(lambda x: x.preStr, self.pre_set)
            self.st_str = '|'.join(st_str_list)
        else:
            self.st_str = None
            self.pre_set = None

    def init_from_string(self, st_str):
        pre_list = st_str.split('|')
        pre_list = map(lambda x:pre(x), pre_list)
        self.pre_set = set(pre_list)
        st_str_list = map(lambda x: x.preStr, self.pre_set)
        self.st_str = '|'.join(st_str_list)

    def init_from_pre_set(self, pre_set):
        self.pre_set = pre_set
        st_str_list = map(lambda x: x.preStr, pre_set)
        self.st_str = '|'.join(st_str_list)

    def __str__(self):
        return self.st_str

    def __eq__(self, statement):
        return self.pre_set==statement.pre_set

    def __hash__(self):
        return hash((''.join(sorted(self.st_str))))

    def isthereinKB(self, KB):
        if self in KB:
            return True
        return False

    def storekb(self, KB, knowledgebaseHash):
        KB.add(self)
        for pre in self.pre_set:
            if pre.name in knowledgebaseHash:
                knowledgebaseHash[pre.name].add(self)
            else:
                knowledgebaseHash[pre.name] = set([self])

    def resolve(self, statement):
        derived = set()
        for pre_1 in self.pre_set:
            for pre_2 in statement.pre_set:
                unification = False
                if (pre_1.neg ^ pre_2.neg) and pre_1.name==pre_2.name:
                    unification = pre_1.unify_with_pre(pre_2)
                if unification == False:
                    continue
                else:
                    rs1 = copy.deepcopy(self.pre_set)
                    rs2 = copy.deepcopy(statement.pre_set)
                    rs1 = filter(lambda x: False if x == pre_1 else True, rs1)
                    rs2 = filter(lambda x: False if x == pre_2 else True, rs2)
                    if not rs1 and not rs2:           # contradiction found
                        return False
                    rs1 = map(lambda x: x.substitute(unification), rs1)
                    rs2 = map(lambda x: x.substitute(unification), rs2)
                    newstmt = State()
                    newstmt.init_from_pre_set(set(rs1+rs2))
                    derived.add(newstmt)
        return derived

    def remodify(self, knowledgebaseHash):
        remodifyAll = set()
        for pre in self.pre_set:
            if pre.name in knowledgebaseHash:
                remodifyAll = remodifyAll.union(knowledgebaseHash[pre.name])
        return remodifyAll

class Node():
    def __init__(self, val):
        self.val = val
        self.negative = False
        self.op = True
        self.left = None
        self.right = None
        if val in pred:
            if '~' in pred[val]:
                self.negative = True
                pred[val] = pred[val][1:]
            self.op = False

def inorderExp(node):
    global traversal
    traversal = ''
    inorder(node)
    return traversal

def inorder(node):
    global traversal
    if node:
        inorder(node.left)
        if node.negative:
            traversal += '~' + node.val
        else:
            traversal += node.val
        inorder(node.right)

def replaceConst(count, solve):
    begin = count + 26
    str_constant = ''
    while begin >= 26:
        val = begin % 26
        if solve:
            str_constant = UPPERCASE[val] + str_constant
        else:
            str_constant = LOWERCASE[val] + str_constant
        begin //= 26
    if solve:
        str_constant = UPPERCASE[begin-1] + str_constant
    else:
        str_constant = LOWERCASE[begin-1] + str_constant
    return str_constant

def disjunction(node):
    if node:
        if node.val == '|':
            if node.left.val == '&' and node.right.val == '&':
                lconjunct = node.left
                rconjunct = node.right
                a = lconjunct.left
                b = lconjunct.right
                c = rconjunct.left
                d = rconjunct.right
                arev = copy.deepcopy(a)
                brev = copy.deepcopy(b)
                crev = copy.deepcopy(c)
                drev = copy.deepcopy(d)
                ldisjunct1 = Node('|')
                ldisjunct2 = Node('|')
                rdisjunct1 = Node('|')
                rdisjunct2 = Node('|')
                node.val = '&'
                lconjunct.left = ldisjunct1
                lconjunct.right = ldisjunct2
                rconjunct.left = rdisjunct1
                rconjunct.right = rdisjunct2
                ldisjunct1.left = a
                ldisjunct1.right = c
                ldisjunct2.left = arev
                ldisjunct2.right = d
                rdisjunct1.left = b
                rdisjunct1.right = crev
                rdisjunct2.left = brev
                rdisjunct2.right = drev
            elif node.left.op and not node.right.op and node.left.val == '&':
                c = node.left.right
                a = node.right
                arev = copy.deepcopy(a)
                right_or = Node('|')
                node.val = '&'
                node.left.val = '|'
                node.left.right = a
                node.right = right_or
                right_or.left = c
                right_or.right = arev
            elif not node.left.op and node.right.op and node.right.val == '&':
                a = node.left
                arev = copy.deepcopy(a)
                b = node.right.left
                left_or = Node('|')
                node.val = '&'
                node.right.val = '|'
                node.left = left_or
                left_or.left = a
                left_or.right = b
                node.right.left = arev
        disjunction(node.left)
        disjunction(node.right)

def inwardnegative(node):
    if node:
        if node.op and node.negative:
            node.left.negative = not node.left.negative
            node.right.negative = not node.right.negative
            if node.val == '&':
                node.val = '|'
            else:
                node.val = '&'
            node.negative = False
        inwardnegative(node.left)
        inwardnegative(node.right)

def eliminateImply(node):
    if node:
        eliminateImply(node.left)
        if node.op and node.val == '=>':
            node.val = '|'
            node.left.negative = not node.left.negative
        eliminateImply(node.right)

def treeFunc(statement):
    s = []
    r = re.compile('(~|&|\||=>|[A-Z][A-Z])')
    pres = r.findall(statement)
    for stamp in pres:
        if stamp in ['&', '|', '=>']:
            r = s.pop()
            l = s.pop()
            op = Node(stamp)
            op.left = l
            op.right = r
            s.append(op)
        elif stamp == '~':
            s[-1].negative = not s[-1].negative
        else:
            operand = Node(stamp)
            s.append(operand)
    return s[0]

def pexpExpression(statement):
    s = []
    r = re.compile('(~|&|\||=>|[A-Z][A-Z]|\(|\))')
    pres = r.findall(statement)
    pexp = ''
    for stamp in pres:
        if re.match('[A-Z][A-Z]', stamp):
            pexp += stamp
        elif stamp in ['~', '&', '|', '=>']:
            while len(s) != 0 and s[-1] not in ['(', ')'] and PRECEDANCE[s[-1]] >= PRECEDANCE[stamp]:
                pexp += s.pop()
            s.append(stamp)
        elif stamp == '(':      #skeptical
            s.append(stamp)
        elif stamp == ')':         #skeptical
            while s[-1] != '(':
                pexp += s.pop()
            s.pop()
    while s:
        pexp += s.pop()
    return pexp

def preToConst(statement):
    r = re.compile('~?[A-Z][A-Za-z]*\([a-zA-Z][a-zA-Z,]*\)')
    pres = r.findall(statement)
    pred = {}
    for i, pre in enumerate(set(pres)):
        xyz = replaceConst(i, True)
        pred[xyz] = pre
        statement = statement.replace(pre, xyz)
    return statement, pred

def replace_constant_by_pre(statement, pred):
    for a, b in pred.items():
        statement = statement.replace(a, b)
    return statement

def standardize_variables(statements):
    global GLOBALCOUNT
    standardize = []
    for statement in statements:
        dictOfVar = {}
        r = re.compile('\([a-zA-Z,]+\)')
        args = r.findall(statement)
        args = map(lambda x:x[1:-1], args)
        args = ','.join(args)
        args = args.split(',')
        args = filter(lambda y: y.islower(), args)
        args = list(set(args))
        for para in args:
            dictOfVar[para] = replaceConst(GLOBALCOUNT, False)
            GLOBALCOUNT += 1
        pres = statement.split('|')
        pre_list = []
        for pre in pres:
            parts = pre.split('(')
            args = parts[1][:-1].split(',')
            args = map(lambda x:dictOfVar[x] if x in dictOfVar else x, args)
            pre = parts[0] + '(' + ','.join(args) + ')'
            pre_list.append(pre)
        standardize.append('|'.join(pre_list))
    return standardize


def begin_program():
    query_statements = []
    knowledgebase = []
    with open('input.txt') as fin:
        f = list(fin)
    fin.close()
    noOfQueries = int(f[0].rstrip('\n'))
    for eachQuery in f[1:1+noOfQueries]:
        eachQuery = eachQuery.rstrip()
        query_statements.append(pre(eachQuery))
    noOfKB = int(f[1+noOfQueries].rstrip('\n'))
    for eachSentence in f[2+noOfQueries:2+noOfQueries+noOfKB]:
        eachSentence = eachSentence.rstrip()
        knowledgebase.append(eachSentence)
    knowledgebase = list(set(knowledgebase))
    return query_statements, knowledgebase

def makeKB(knowledgebase):
    global pred
    for statement in knowledgebase:
        pred.clear()
        statement, pred = preToConst(statement)
        statement = pexpExpression(statement)
        head = treeFunc(statement)
        eliminateImply(head)
        inwardnegative(head)
        disjunction(head)
        inord = inorderExp(head)
        statement = replace_constant_by_pre(inord, pred)
        statements = statement.split('&')
        statements = standardize_variables(statements)
        for conjuctiveNormal in statements:
            stateMent_obj = State(conjuctiveNormal)
            stateMent_obj.storekb(KB, KBH)

def resolve(KB, knowledgebaseHash, q):
    knowledgebase2 = set()
    knowledgebaseHash = {}
    q.storekb(knowledgebase2, knowledgebaseHash)
    q.storekb(KB, knowledgebaseHash)
    while True:
        previous = {}
        newST = set()
        if len(KB) > KILL_LIMIT: return False
        for st1 in KB:
            remodifyAll = st1.remodify(knowledgebaseHash)
            for st2 in remodifyAll:
                if st1 == st2:
                    continue
                temp1 = False
                temp2 = False
                if st2.st_str in previous:
                    temp1 = True
                    if st1.st_str in previous[st2.st_str]:
                        previous[st2.st_str].discard(st1.st_str)
                        continue
                if st1.st_str in previous:
                    temp2 = True
                    if st2.st_str in previous[st1.st_str]:
                        previous[st1.st_str].discard(st2.st_str)
                        continue

                if temp2:
                    previous[st1.st_str].add(st2.st_str)
                else:
                    previous[st1.st_str] = set([st2.st_str])
                output_resolving = st1.resolve(st2)
                if output_resolving == False:
                    return True
                newST = newST.union(output_resolving)
        if newST.issubset(KB):
            return False
        newST = newST.difference(KB)
        knowledgebase2 = set()
        knowledgebaseHash = {}
        for stateMent in newST:
            stateMent.storekb(knowledgebase2, knowledgebaseHash)
        KB = KB.union(newST)

def final_result(ans):
    output = 'TRUE' + '\n' if ans else 'FALSE' + '\n'
    return output


query_statements, knowledgebase = begin_program()
makeKB(knowledgebase)
output = []
for query_pre in query_statements:
    query_pre.negative()
    query_pre = State(query_pre.preStr)
    KB = copy.deepcopy(KB)
    knowledgebaseHash = copy.deepcopy(KBH)
    answer = resolve(KB, knowledgebaseHash, query_pre)
    output.append(final_result(answer))
with open('output.txt', 'w') as fout:
    for i in output:
        fout.write(i)
