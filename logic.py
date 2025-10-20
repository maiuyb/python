# logic.py
# --------
# Licensing Information:  You are free to use or extend these projects for
# educational purposes provided that (1) you do not distribute or publish
# solutions, (2) you retain this notice, and (3) you provide clear
# attribution to UC Berkeley, including a link to http://ai.berkeley.edu.
# 
# Attribution Information: The Pacman AI projects were developed at UC Berkeley.
# The core projects and autograders were primarily created by John DeNero
# (denero@cs.berkeley.edu) and Dan Klein (klein@cs.berkeley.edu).
# Student side autograding was added by Brad Miller, Nick Hay, and
# Pieter Abbeel (pabbeel@cs.berkeley.edu).


"""Representations and Inference for the CS 188 Logic Project

Code originally from https://code.google.com/p/aima-python/
Modified heavily with additional convenience classes and functions as well
as an interface to the pycosat (picoSAT wrapper) library.
https://pypi.python.org/pypi/pycosat.
Original package contained implementations of functions and data structures
for Knowledge bases and First-Order Logic.
"""

import itertools, re
from typing import Tuple
import agents
from logic_utils import *
import pycosat

#______________________________________________________________________________

class Expr:
    """A symbolic mathematical expression.  We use this class for logical
    expressions, and for terms within logical expressions. In general, an
    Expr has an op (operator) and a list of args.  The op can be:
      Null-ary (no args) op:
        A number, representing the number itself.  (e.g. Expr(42) => 42)
        A symbol, representing a variable or constant (e.g. Expr('F') => F)
      Unary (1 arg) op:
        '~', '-', representing NOT, negation (e.g. Expr('~', Expr('P')) => ~P)
      Binary (2 arg) op:
        '>>', '<<', representing forward and backward implication
        '+', '-', '*', '/', '**', representing arithmetic operators
        '<', '>', '>=', '<=', representing comparison operators
        '<=>', '^', representing logical equality and XOR
      N-ary (0 or more args) op:
        '&', '|', representing conjunction and disjunction
        A symbol, representing a function term or FOL proposition

    Exprs can be constructed with operator overloading: if x and y are Exprs,
    then so are x + y and x & y, etc.  Also, if F and x are Exprs, then so is
    F(x); it works by overloading the __call__ method of the Expr F.  Note
    that in the Expr that is created by F(x), the op is the str 'F', not the
    Expr F.   See http://www.python.org/doc/current/ref/specialnames.html
    to learn more about operator overloading in Python.

    WARNING: x == y and x != y are NOT Exprs.  The reason is that we want
    to write code that tests 'if x == y:' and if x == y were the same
    as Expr('==', x, y), then the result would always be true; not what a
    programmer would expect.  But we still need to form Exprs representing
    equalities and disequalities.  We concentrate on logical equality (or
    equivalence) and logical disequality (or XOR).  You have 3 choices:
        (1) Expr('<=>', x, y) and Expr('^', x, y)
            Note that ^ is bitwise XOR in Python (and Java and C++)
        (2) expr('x <=> y') and expr('x =/= y').
            See the doc string for the function expr.
        (3) (x % y) and (x ^ y).
            It is very ugly to have (x % y) mean (x <=> y), but we need
            SOME operator to make (2) work, and this seems the best choice.

    WARNING: if x is an Expr, then so is x + 1, because the int 1 gets
    coerced to an Expr by the constructor.  But 1 + x is an error, because
    1 doesn't know how to add an Expr.  (Adding an __radd__ method to Expr
    wouldn't help, because int.__add__ is still called first.) Therefore,
    you should use Expr(1) + x instead, or ONE + x, or expr('1 + x').
    一种符号数学表达式。我们使用此类来表示逻辑表达式以及逻辑表达式中的项。
    通常，一个Expr具有一个操作符（op）和一个参数列表（args）。操作符可以是：
    无参（无参数）操作符：
        一个数字，代表数字本身（例如，Expr(42) => 42）
        一个符号，代表变量或常量（例如，Expr('F') => F）
    一元（1个参数）操作符：
        '~'、'-'，分别代表“非”、否定（例如，Expr('~', Expr('P')) => ~P）
    二元（2个参数）操作符：
        '>>'、'<<'，代表正向和反向蕴涵
        '+'、'-'、'*'、'/'、'**'，代表算术运算符
        '<'、'>'、'>='、'<=',代表比较运算符
        '<=>'、'^'，代表逻辑等价和异或
    多元（0个或多个参数）操作符：
        '&'、'|'，代表合取和析取
        一个符号，代表函数项或一阶逻辑命题

    可以通过运算符重载来构造Expr：如果x和y是Expr，那么x + y和x & y等也是Expr。
    此外，如果F和x是Expr，那么F(x)也是Expr；这通过重载Expr F的__call__方法实现。
    请注意，在由F(x)创建的Expr中，操作符是字符串'F'，而非Expr F。
    有关Python中运算符重载的更多信息，请参见http://www.python.org/doc/current/ref/specialnames.html。

    警告：x == y和x != y并非Expr。原因是我们希望编写“if x == y:”这样的代码进行测试，
    而如果x == y等同于Expr('==', x, y)，那么结果将始终为真，这并非程序员所期望的。
    但我们仍然需要形成表示相等和不等的Expr。我们主要关注逻辑等价（或等值）和逻辑不等价（或异或）。您有3种选择：
        （1）Expr('<=>', x, y)和Expr('^', x, y)
            注意，^在Python（以及Java和C++）中是按位异或
        （2）Expr('x <=> y')和Expr('x =/= y')
            参见Expr函数的文档字符串
        （3）(x % y)和(x ^ y)
            用(x % y)表示(x <=> y)确实很不直观，但 我们需要某个运算符来使（2）生效，这似乎是最佳选择。

    警告：如果x是一个Expr，那么x + 1也是Expr，因为整数1会被构造函数强制转换为Expr。
    但1 + x是错误的，因为1不知道如何与Expr相加（向Expr添加__radd__方法也无济于事，因为int.__add__会被优先调用）。
    因此，您应该改用Expr(1) + x，或ONE + x，或expr('1 + x')。
"""
    
    # Initialize a counter object
    # 初始化一个计数器对象
    counter = 0
    def __init__(self, op, *args): 
        "Op is a string or number; args are Exprs (or are coerced to Exprs)."
        #操作符（Op）是一个字符串或数字；参数（args）是 Expr对象（或会被强制转换为Expr对象）。
        assert isinstance(op, str) or (isnumber(op) and not args)
        self.op = num_or_str(op)
        self.args = tuple(map(expr, args)) ## Coerce args to Exprs
        if not args and not is_prop_symbol(self.op):
            raise SyntaxError("Unacceptable symbol base name (%s). Name must start with an upper-case alphabetic character that and is not TRUE or FALSE. Furthermore, only the following are allowed: capital and lower case alphabetic, 0-9, _, \",\", [, and ]." % self.op)
        # Increment the counter when an object is created
        #当一个对象被创建时，将计数器加 1。
        type(self).counter += 1
        
    def __call__(self, *args):
        """Self must be a symbol with no args, such as Expr('F').  Create a new
        Expr with 'F' as op and the args as arguments.
        self 必须是一个无参数的符号，例如 Expr ('F')。创建一个新的 Expr，以 'F' 作为操作符（op），
        并将传入的参数作为该 Expr 的参数列表（args）。
        """
        assert is_symbol(self.op) and not self.args
        return Expr(self.op, *args)

    def __repr__(self):
        "Show something like 'P' or 'P(x, y)', or '~P' or '(P | Q | R)'"
        #展示类似 “P”“P (x, y)”“~P” 或 “(P | Q | R)” 这样的内容。
        if not self.args:         # Constant or proposition with arity 0    元数为 0 的常量或命题
            return str(self.op)
        elif is_symbol(self.op):  # Functional or propositional operator     函数运算符或命题运算符
            return '%s(%s)' % (self.op, ', '.join(map(repr, self.args)))
        elif len(self.args) == 1: # Prefix operator   前缀运算符
            return self.op + repr(self.args[0])
        else:                     # Infix operator     后缀运算符
            return '(%s)' % (' '+self.op+' ').join(map(repr, self.args))

    def __eq__(self, other):
        """
        x and y are equal iff their ops and args are equal.
        x 和 y 相等，当且仅当它们的操作符（op）和参数列表（args）都相等
        """
        return (other is self) or (isinstance(other, Expr)
            and self.op == other.op and self.args == other.args)

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        '''Need a hash method so Exprs can live in dicts.
        需要一个哈希方法（hashmethod），以便 Expr对象可以存放在字典（dicts）中
        '''
        return hash(self.op) ^ hash(tuple(self.args))

    # See http://www.python.org/doc/current/lib/module-operator.html
    # Not implemented: not, abs, pos, concat, contains, *item, *slice
    #未实现：非（not）、绝对值（abs）、正号（pos）、连接（concat）、包含（contains）、* 索引访问（item）、* 切片（slice）
    def __lt__(self, other):     return Expr('<',  self, other)
    def __le__(self, other):     return Expr('<=', self, other)
    def __ge__(self, other):     return Expr('>=', self, other)
    def __gt__(self, other):     return Expr('>',  self, other)
    def __add__(self, other):    return Expr('+',  self, other)
    def __sub__(self, other):    return Expr('-',  self, other)
    def __and__(self, other):    return Expr('& ',  self, other)
    def __div__(self, other):    return Expr('/',  self, other)
    def __truediv__(self, other):return Expr('/',  self, other)
    def __invert__(self):        return Expr('~',  self)
    def __lshift__(self, other): return Expr('<<', self, other)
    def __rshift__(self, other): return Expr('>>', self, other)
    def __mul__(self, other):    return Expr('*',  self, other)
    def __neg__(self):           return Expr('-',  self)
    def __or__(self, other):     return Expr('|',  self, other)
    def __pow__(self, other):    return Expr('**', self, other)
    def __xor__(self, other):    return Expr('^',  self, other)
    def __mod__(self, other):    return Expr('<=>',  self, other)

class PropSymbolExpr(Expr):
    """An extension of Expr intended to represent a symbol. This SymbolExpr
    is a convenience for naming symbols, especially symbols whose names
    indicate an indexed value (e.g. Position[x,y] or Fluent[t]).
    Symbol name must begin with a capital letter. This class helps to add
    brackets with enumerated indices to the end of the name.
    Expr 的一个扩展类，用于表示符号（symbol）。
    该 SymbolExpr 类为符号命名提供了便捷性，尤其适用于名称带有索引值的符号（例如 Position [x,y] 或 Fluent [t]）。
    符号名称必须以大写字母开头。此类可协助在名称末尾添加带有枚举索引的方括号。
    """
    # copied from logicPlan.py; preferably do this better
    #从 logicPlan.py 复制而来；最好能优化实现方式
    pacman_str = 'P'
    food_str = 'FOOD'
    wall_str = 'WALL'
    DIRECTIONS = {'North', 'South', 'East', 'West'}
    # rules
    double_index = {pacman_str, food_str, wall_str}
    time_index = {pacman_str, food_str} | DIRECTIONS
    all_checked = double_index | time_index

    def __init__(self, sym_str: str, *index: Tuple[int], time: int = None):
        """Constructor taking a propositional logic symbol name and an optional set of index values,
        creating a symbol with the base name followed by brackets with the specific
        indices.
        sym_str: String representing base name for symbol. Must begin with a capital letter.
        （该类的）构造函数接收一个命题逻辑符号名和一组可选的索引值，
        会创建一个 “基础名称后接带特定索引方括号” 的符号。其中，sym_str 是表示符号基础名称的字符串，且必须以大写字母开头。
        Examples:
        >>> red = PropSymbolExpr("R")
        >>> print(red)
        R
        >>> turnLeft7 = PropSymbolExpr("Left",7)
        >>> print(turnLeft7)
        Left[7]
        >>> pos_2_3 = PropSymbolExpr("P",2,3)
        >>> print(pos_2_3)
        P[2,3]
        """
        if not is_prop_symbol(sym_str):
            raise SyntaxError("Unacceptable symbol base name (%s). Name must start with an upper-case alphabetic character that and is not TRUE or FALSE. Furthermore, only the following are allowed: capital and lower case alphabetic, 0-9, _, \",\", [, and ]." % sym_str)
        if sym_str in self.all_checked:
            if sym_str in self.double_index:
                if len(index) != 2:
                    raise SyntaxError("Unexpected " + sym_str + " Symbol. Was expecting 2 coordinates.")
            elif len(index) != 0:
                raise SyntaxError("Unexpected " + sym_str + " Symbol. Was expecting 0 coordinates.")
            if sym_str in self.time_index:
                if time == None:
                    raise SyntaxError("Unexpected " + sym_str + " Symbol. Was expecting time stamp.")
            elif time != None:
                raise SyntaxError("Unexpected " + sym_str + " Symbol. Was expecting no time stamp.")
        self.sym_str = sym_str
        self.indicies = index
        self.time = time
        if len(index) > 0:
            if len(index) > 4:
                raise SyntaxError("Too many arguments to SymbolExpr constructor. SymbolExpr(symbol_str, [index1], [index2], [index3], [index4], time=[time]), or fewer indicies -- possibly 0.")
            if len(index) == 1:
                sym_str = '%s[%d]' % (sym_str, *index)
            elif len(index) == 2:
                sym_str = '%s[%d,%d]' % (sym_str, *index)
            elif len(index) == 3:
                sym_str = '%s[%d,%d,%d]' % (sym_str, *index)
            elif len(index) == 4:
                sym_str = '%s[%d,%d,%d,%d]' % (sym_str, *index)
        if time != None:
            sym_str = '%s_%d' % (sym_str, int(time))
        Expr.__init__(self, sym_str)
        
    def getBaseName(self):
        return self.sym_str
    
    def getIndex(self):
        return self.indicies
    
    def getTime(self):
        return self.time
    
def parseExpr(symbol):
    """A simple expression parser, takes in a PropSymbolExpr and returns 
       its deconstruction in the form ( sym_str, indices, time ).
       一个简单的表达式解析器，接收一个 PropSymbolExpr（命题符号表达式），
       并以（sym_str，indices，time）的形式返回其解构结果。
       Examples:
       >>> parseExpr("North[3]")
       ('North', None, (3))
       >>> parseExpr("A")
       (A, None, ())
       >>> parseExpr("P[3,4]_1")
       ('P', 1, (3, 4))
    """
    tokens = re.split(r"_", str(symbol))
    time = None
    if len(tokens) == 2:
        symbol = tokens[0]
        time = int(tokens[1])

    tokens = re.findall(r"[\w]+", str(symbol))
    if len(tokens) == 1:
        return (tokens[0], (), time)
    return (tokens[0], tuple(map(int,tokens[1:])), time)

def expr(s):
    """Create an Expr representing a logic expression by parsing the input
    string. Symbols and numbers are automatically converted to Exprs.
    In addition you can use alternative spellings of these operators:
      'x ==> y'   parses as   (x >> y)    # Implication
      'x <== y'   parses as   (x << y)    # Reverse implication
      'x <=> y'   parses as   (x % y)     # Logical equivalence
      'x =/= y'   parses as   (x ^ y)     # Logical disequality (xor)
    But BE CAREFUL; precedence of implication is wrong. expr('P & Q ==> R & S')
    通过解析输入字符串创建一个表示逻辑表达式的 Expr。
    符号和数字会被自动转换为 Expr。
    此外，你可以使用这些运算符的替代拼写：
    'x ==> y' 解析为 (x>> y) # 蕴涵
    'x <== y' 解析为 (x << y) # 反向蕴涵
    'x <=> y' 解析为 (x % y) # 逻辑等价
    'x =/= y' 解析为 (x ^ y) # 逻辑不等价（异或）
    但请注意：蕴涵运算符的优先级是错误的。例如 expr ('P & Q ==> R & S') 会按错误的优先级解析。
    is ((P & (Q >> R)) & S); so you must use expr('(P & Q) ==> (R & S)').
    >>> expr('P <=> Q(1)')
    (P <=> Q(1))
    >>> expr('P & Q | ~R(x, F(x))')
    ((P & Q) | ~R(x, F(x)))
    """
    if isinstance(s, Expr): return s
    if isnumber(s): return Expr(s)
    ## Replace the alternative spellings of operators with canonical spellings
    #将运算符的替代拼写替换为标准拼写
    s = s.replace('==>', '>>').replace('<==', '<<')
    s = s.replace('<=>', '%').replace('=/=', '^')
    ## Replace a symbol or number, such as 'P' with 'Expr("P")'
    #将符号或数字（例如 'P'）替换为 'Expr ("P")'。
    s = re.sub(r'([a-zA-Z0-9_.]+)', r'Expr("\1")', s)
    ## Now eval the string.  (A security hole; do not use with an adversary.)
    #现在对该字符串执行 eval 操作。（这存在安全漏洞，不要用于处理来自攻击者的输入。）
    return eval(s, {'Expr':Expr})

def is_symbol(s):
    "A string s is a symbol if it starts with an alphabetic char."
    #如果字符串s以字母字符开头，那么它就是一个符号。
    return isinstance(s, str) and s[:1].isalpha()

def is_var_symbol(s):
    "A logic variable symbol is an initial-lowercase string."
    #“逻辑变量符号是首字母小写的字符串。”
    return is_symbol(s) and s[0].islower()

def is_prop_symbol(s):
    """A proposition logic symbol is an initial-uppercase string other than
    TRUE or FALSE."""
    #命题逻辑符号是首字母大写的字符串，但不包括‘TRUE’和‘FALSE’这两个字符串。
    return is_symbol(s) and s[0].isupper() and s != 'TRUE' and s != 'FALSE' and re.match(r'[a-zA-Z0-9_\[\],]*$', s)

def variables(s):
    """Return a set of the variables in expression s.
    返回表达式 s 中所有变量组成的集合。
    >>> ppset(variables(F(x, A, y)))
    set([x, y])
    >>> ppset(variables(F(G(x), z)))
    set([x, z])
    >>> ppset(variables(expr('F(x, x) & G(x, y) & H(y, z) & R(A, z, z)')))
    set([x, y, z])
    """
    result = set([])
    def walk(s):
        if is_variable(s):
            result.add(s)
        else:
            for arg in s.args:
                walk(arg)
    walk(s)
    return result

def is_definite_clause(s):
    """returns True for exprs s of the form A & B & ... & C ==> D,
    where all literals are positive.  In clause form, this is
    ~A | ~B | ... | ~C | D, where exactly one clause is positive.
    当表达式 s 具有 A & B & ... & C ==> D 的形式，
    且所有文字（literal）均为肯定式时，返回 True。
    在子句形式中，该表达式等价于～A | ~B | ... | ~C | D，其中恰好有一个子句是肯定式。
    >>> is_definite_clause(expr('Farmer(Mac)'))
    True
    >>> is_definite_clause(expr('~Farmer(Mac)'))
    False
    >>> is_definite_clause(expr('(Farmer(f) & Rabbit(r)) ==> Hates(f, r)'))
    True
    >>> is_definite_clause(expr('(Farmer(f) & ~Rabbit(r)) ==> Hates(f, r)'))
    False
    >>> is_definite_clause(expr('(Farmer(f) | Rabbit(r)) ==> Hates(f, r)'))
    False
    """
    if is_symbol(s.op):
        return True
    elif s.op == '>>':
        antecedent, consequent = s.args
        return (is_symbol(consequent.op)
                and every(lambda arg: is_symbol(arg.op), conjuncts(antecedent)))
    else:
        return False

def parse_definite_clause(s):
    "Return the antecedents and the consequent of a definite clause."
    #返回一个确定子句（definite clause）的前件（antecedents）和后件（consequent）。
    assert is_definite_clause(s)
    if is_symbol(s.op):
        return [], s
    else:
        antecedent, consequent = s.args
        return conjuncts(antecedent), consequent

## Useful constant Exprs used in examples and code:
#以下是示例和代码中会用到的实用常量 Expr（表达式）：
class SpecialExpr(Expr):
    """Exists solely to allow the normal Expr constructor to assert valid symbol
    syntax while still having some way to create the constants 
    TRUE, FALSE, ZERO, ONE, and, TWO
    其存在的唯一目的是：在允许常规 Expr 构造函数验证符号语法合法性的同时，
    仍能提供一种方式来创建 TRUE、FALSE、ZERO、ONE、TWO 这些常量。
    """
    def __init__(self, op, *args):
        "Op is a string or number; args are Exprs (or are coerced to Exprs)."
        #操作符（Op）是一个字符串或数字；参数（args）是 Expr 对象（或会被强制转换为 Expr 对象）
        assert isinstance(op, str) or (isnumber(op) and not args)
        self.op = num_or_str(op)
        self.args = tuple(map(expr, args)) ## Coerce args to Exprs

TRUE, FALSE = tuple(map(SpecialExpr, ['TRUE', 'FALSE']))
ZERO, ONE, TWO = tuple(map(SpecialExpr, [0, 1, 2]))
A, B, C, D, E, F, G, P, Q  = tuple(map(Expr, 'ABCDEFGPQ'))

#______________________________________________________________________________
def prop_symbols(x):
    "Return a list of all propositional symbols in x."
    #返回 x 中所有命题符号组成的列表。
    if not isinstance(x, Expr):
        return []
    elif is_prop_symbol(x.op):
        return [x]
    else:
        return list(set(symbol for arg in x.args
                        for symbol in prop_symbols(arg)))

def pl_true(exp, model={}):
    """Return True if the propositional logic expression is true in the model,
    and False if it is false. If the model does not specify the value for
    every proposition, this may return None to indicate 'not obvious';
    this may happen even when the expression is tautological."""
    #如果命题逻辑表达式在模型中为真，则返回 True；
    # 如果为假，则返回 False。若模型未指定所有命题的值，可能会返回 None 表示 “不明确”；
    # 这种情况即使在表达式为重言式时也可能发生。
    op, args = exp.op, exp.args
    if exp == TRUE:
        return True
    elif exp == FALSE:
        return False
    elif is_prop_symbol(op):
        return model.get(exp)
    elif op == '~':
        p = pl_true(args[0], model)
        if p is None: return None
        else: return not p
    elif op == '|':
        result = False
        for arg in args:
            p = pl_true(arg, model)
            if p is True: return True
            if p is None: result = None
        return result
    elif op == '&':
        result = True
        for arg in args:
            p = pl_true(arg, model)
            if p is False: return False
            if p is None: result = None
        return result
    p, q = args
    if op == '>>':
        return pl_true(~p | q, model)
    elif op == '<<':
        return pl_true(p | ~q, model)
    pt = pl_true(p, model)
    if pt is None: return None
    qt = pl_true(q, model)
    if qt is None: return None
    if op == '<=>':
        return pt == qt
    elif op == '^':
        return pt != qt
    else:
        raise ValueError("illegal operator in logic expression" + str(exp))

#______________________________________________________________________________

## Convert to Conjunctive Normal Form (CNF)

def to_cnf(s):
    """Convert a propositional logical sentence s to conjunctive normal form.
    That is, to the form ((A | ~B | ...) & (B | C | ...) & ...) [p. 253]
    将命题逻辑语句 s 转换为合取范式（conjunctive normal form，CNF）。
    也就是说，转换为 ((A | ~B | ...) & (B | C | ...) & ...) 的形式（参见第 253 页）。
    >>> to_cnf("~(B|C)")
    (~B & ~C)
    >>> to_cnf("B <=> (P1|P2)")
    ((~P1 | B) & (~P2 | B) & (P1 | P2 | ~B))
    >>> to_cnf("a | (b & c) | d")
    ((b | a | d) & (c | a | d))
    >>> to_cnf("A & (B | (D & E))")
    (A & (D | B) & (E | B))
    >>> to_cnf("A | (B | (C | (D & E)))")
    ((D | A | B | C) & (E | A | B | C))
    """
    if isinstance(s, str): s = expr(s)
    s = eliminate_implications(s) # Steps 1, 2 from p. 253
    s = move_not_inwards(s) # Step 3
    s = distribute_and_over_or(s) # Step 4
    return s

def eliminate_implications(s):
    """Change >>, <<, and <=> into &, |, and ~. That is, return an Expr
    that is equivalent to s, but has only &, |, and ~ as logical operators.
    将 >>、<<和 <=> 转换为 &、| 和～。
    也就是说，返回一个与 s 等价的 Expr，但仅使用 &、| 和～作为逻辑运算符。
    >>> eliminate_implications(A >> (~B << C))
    ((~B | ~C) | ~A)
    >>> eliminate_implications(A ^ B)
    ((A & ~B) | (~A & B))
    """
    if not s.args or is_symbol(s.op): return s     ## (Atoms are unchanged.)
    args = tuple(map(eliminate_implications, s.args))
    a, b = args[0], args[-1]
    if s.op == '>>':
        return (b | ~a)
    elif s.op == '<<':
        return (a | ~b)
    elif s.op == '<=>':
        return (a | ~b) & (b | ~a)
    elif s.op == '^':
        assert len(args) == 2   ## TODO: relax this restriction
        return (a & ~b) | (~a & b)
    else:
        assert s.op in ('&', '|', '~')
        return Expr(s.op, *args)

def move_not_inwards(s):
    """Rewrite sentence s by moving negation sign inward.
    通过将否定符号向内移动来重写语句 s。
    >>> move_not_inwards(~(A | B))
    (~A & ~B)
    >>> move_not_inwards(~(A & B))
    (~A | ~B)
    >>> move_not_inwards(~(~(A | ~B) | ~~C))
    ((A | ~B) & ~C)
    """
    if s.op == '~':
        NOT = lambda b: move_not_inwards(~b)
        a = s.args[0]
        if a.op == '~': return move_not_inwards(a.args[0]) # ~~A ==> A
        if a.op =='&': return associate('|', tuple(map(NOT, a.args)))
        if a.op =='|': return associate('&', tuple(map(NOT, a.args)))
        return s
    elif is_symbol(s.op) or not s.args:
        return s
    else:
        return Expr(s.op, *map(move_not_inwards, s.args))

def distribute_and_over_or(s):
    """Given a sentence s consisting of conjunctions and disjunctions
    of literals, return an equivalent sentence in CNF.
    对于一个由文字的合取与析取组成的语句 s，返回一个等价的合取范式（CNF）语句。
    >>> distribute_and_over_or((A & B) | C)
    ((A | C) & (B | C))
    """
    if s.op == '|':
        s = associate('|', s.args)
        if s.op != '|':
            return distribute_and_over_or(s)
        if len(s.args) == 0:
            return FALSE
        if len(s.args) == 1:
            return distribute_and_over_or(s.args[0])
        conj = find_if((lambda d: d.op == '&'), s.args)
        if not conj:
            return s
        others = [a for a in s.args if a is not conj]
        rest = associate('|', others)
        return associate('&', [distribute_and_over_or(c|rest)
                               for c in conj.args])
    elif s.op == '&':
        return associate('&', map(distribute_and_over_or, s.args))
    else:
        return s

def associate(op, args):
    """Given an associative op, return an expression with the same
    meaning as Expr(op, *args), but flattened -- that is, with nested
    instances of the same op promoted to the top level.
    对于一个可结合的操作符（associative op），
    返回一个与 Expr(op, *args) 含义相同但经过扁平化处理的表达式 —— 即，将嵌套的相同操作符实例提升至顶层。
    >>> associate('&', [(A&B),(B|C),(B&C)])
    (A & B & (B | C) & B & C)
    >>> associate('|', [A|(B|(C|(A&B)))])
    (A | B | C | (A & B))
    """
    args = dissociate(op, args)
    if len(args) == 0:
        return _op_identity[op]
    elif len(args) == 1:
        return args[0]
    else:
        return Expr(op, *args)

_op_identity = {'&':TRUE, '|':FALSE, '+':ZERO, '*':ONE}

def conjoin(exprs, *args):
    """Given a list of expressions, returns their conjunction. Can be called either
    with one argument that is a list of expressions, or with several arguments that
    are each an expression.
    If exprs is a singular expression or contains only one expression, return that
    expression directly.
    If exprs is an empty list, throw an error.
    给定一个表达式列表，返回它们的合取式。调用方式有两种：
    一是传入一个包含多个表达式的列表作为参数，
    二是传入多个表达式作为独立参数。
    若表达式列表（exprs）是单个表达式，或仅包含一个表达式，则直接返回该表达式。
    若表达式列表为空，则抛出错误。
    >>> conjoin([(A&B),(B|C),(B&C)])
    (A & B & (B | C) & B & C)
    >>> conjoin((A&B), (B|C), (B&C))
    (A & B & (B | C) & B & C)
    >>> conjoin([A])
    A
    """
    if args:
        return conjoin([exprs] + list(args))
    if (type(exprs) != list):
        return exprs

    assert len(exprs) > 0, "List to conjoin cannot be empty."

    # It is a list. Enforce everything in the list is an Expr
    for expr in exprs:
        assert isinstance(expr, Expr), "An item in list to conjoin is not an Expr."

    if (len(exprs) == 1):
        return exprs[0]
    return associate('&', exprs)

def disjoin(exprs, *args):
    """Given a list of expressions, returns their disjunction. Can be called either
    with one argument that is a list of expressions, or with several arguments that
    are each an expression.
    If exprs is a singular expression or contains only one expression, return that
    expression directly.
    If exprs is an empty list, throw an error.
    给定一个表达式列表，返回它们的析取式。调用方式有两种：
    一是传入一个包含多个表达式的列表作为参数，
    二是传入多个表达式作为独立参数。
    若表达式列表（exprs）是单个表达式，或仅包含一个表达式，则直接返回该表达式。
    若表达式列表为空，则抛出错误。
    >>> disjoin([C, (A&B), (D&E)])
    (C | (A & B) | (D & E))
    >>> disjoin(C, (A&B), (D&E))
    (C | (A & B) | (D & E))
    >>> disjoin([C])
    D
    """
    if args:
        return disjoin([exprs] + list(args))
    if (type(exprs) != list):
        return exprs

    assert len(exprs) > 0, "List to disjoin cannot be empty."

    # It is a list. Enforce everything in the list is an Expr
    #这是一个列表。需确保列表中的所有元素都是Expr对象。
    for expr in exprs:
        assert isinstance(expr, Expr), "An item in list to disjoin is not an Expr."

    if (len(exprs) == 1):
        return exprs[0]
    return associate('|', exprs)

def dissociate(op, args):
    """Given an associative op, return a flattened list result such
    that Expr(op, *result) means the same as Expr(op, *args).
    对于一个可结合的操作符（associative op），
    返回一个经过扁平化处理的列表 result，使得 Expr(op, *result) 与 Expr(op, *args) 含义相同。
    """

    result = []
    def collect(subargs):
        for arg in subargs:
            if arg.op == op: collect(arg.args)
            else: result.append(arg)
    collect(args)
    return result

def conjuncts(s):
    """Return a list of the conjuncts in the sentence s.
    >>> conjuncts(A & B)
    [A, B]
    >>> conjuncts(A | B)
    [(A | B)]
    """
    return dissociate('&', [s])

def disjuncts(s):
    """Return a list of the disjuncts in the sentence s.
    >>> disjuncts(A | B)
    [A, B]
    >>> disjuncts(A & B)
    [(A & B)]
    """
    return dissociate('|', [s])

def is_valid_cnf(exp):
    if not isinstance(exp, Expr):
        print("Input is not an expression.")
        return False
    
    clauses = conjuncts(exp);
    
    for c in clauses:
        literals = disjuncts(c)
        
        for lit in literals:
            if len(lit.args) == 0:
                symbol = lit;
            elif len(lit.args) == 1:
                symbol = lit.args[0]
                
                if len(symbol.args) != 0:
                    print("Found a NOT outside of %s" % symbol)
                    return False
                
            else:
                print("Found %s where only a literal should be." % lit)
                return False
    
            symbol_str = str(symbol)
    
            if not is_symbol(symbol_str):
                print("%s is not a valid symbol." % symbol_str)
                return False
            elif not symbol_str[0].isupper():
                print("The symbol %s must begin with an upper-case letter." % symbol_str)
                return False
            elif symbol_str == 'TRUE':
                print("TRUE is not a valid symbol.")
                return False
            elif symbol_str == 'FALSE':
                print("FALSE is not a valid symbol.")
                return False
        
    return True

#______________________________________________________________________________
# pycosat python wrapper around PicoSAT software.
# https://pypi.python.org/pypi/pycosat

def pycoSAT(expr):
    """Check satisfiability of an expression.
    Given a CNF expression, returns a model that causes the input expression
    to be true. Returns false if it cannot find a satisfible model.
    A model is simply a dictionary with Expr symbols as keys with corresponding values
    that are booleans: True if that symbol is true in the model and False if it is
    false in the model.
    Calls the pycosat solver: https://pypi.python.org/pypi/pycosat
    检查一个表达式的可满足性。
    对于给定的合取范式（CNF）表达式，返回一个使其为真的模型。若无法找到可满足的模型，则返回 false。
    模型是一个字典，以 Expr 符号为键，对应的值为布尔值：若符号在模型中为真，则值为 True；若为假，则值为 False。
    该函数调用 pycosat 求解器（参见：https://pypi.python.org/pypi/pycosat）。
    >>> ppsubst(pycoSAT(A&~B))
    {A: True, B: False}
    >>> pycoSAT(P&~P)
    False
    """

    clauses = conjuncts(expr)

    # Load symbol dictionary
    symbol_dict = mapSymbolAndIndices(clauses)
    # Convert Expr to integers
    clauses_int = exprClausesToIndexClauses(clauses, symbol_dict)
    
    model_int = pycosat.solve(clauses_int)
    
    if model_int == 'UNSAT' or model_int == 'UNKNOWN':
        return False
    
    model = indexModelToExprModel(model_int, symbol_dict)
    
    return model

def mapSymbolAndIndices(clauses):
    """
    Create a dictionary that maps each clause to an integer index.
    Uses a bidirectional dictionary {key1:value1, value1:key1, ...} for quick
    access from symbol to index and index to symbol.
    创建一个将每个子句（clause）映射到整数索引的字典。
    同时使用一个双向字典（结构为 {key1:value1, value1:key1, ...}），
    以实现从符号（symbol）到索引（index）、以及从索引到符号的快速查找。
    """
    symbol_dict = {}
    idx = 1
    for clause in clauses:
        symbols = prop_symbols(clause)
        for symbol in symbols:
            if symbol not in symbol_dict:
                symbol_dict[symbol] = idx
                symbol_dict[idx] = symbol
                idx +=1

    return symbol_dict

def exprClausesToIndexClauses(clauses, symbol_dict):
    """
    Convert each Expr in a list of clauses (CNF) into its corresponding index in
    the symbol_dict (see mapSymbolAndIndices)
    将子句列表（CNF）中的每个 Expr 转换为其在 symbol_dict 中对应的索引（参见 mapSymbolAndIndices）。
    """
    clauses_int = []
    for c in clauses:
        c_disj = disjuncts(c)
            
        c_int = []
        for lit in c_disj:
            # If literal is symbol, convert to index and add it.
            # Otherwise it is ~symbol, in which case, we extract the symbol, 
            # convert it to index, and add the negative of the index
            #如果文字（literal）是符号（symbol），则将其转换为索引并添加。
            #否则，该文字是～symbol（符号的否定），这种情况下，我们提取出符号，
            #将其转换为索引，然后添加该索引的负值
            if len(lit.args) == 0:
                c_int += [symbol_dict[lit]]
            else:
                c_int += [-symbol_dict[lit.args[0]]]
        clauses_int += [c_int]

    return clauses_int

def indexModelToExprModel(model_int, symbol_dict):
    """
    Convert a model with indices into a model with the corresponding Expr in
    the symbol_dict (see mapSymbolAndIndices)
    将以索引（index）表示的模型，转换为以 symbol_dict 中对应 Expr 符号表示的模型（参见 mapSymbolAndIndices）。
    >>>
    """
    model = {}
    for lit_int in model_int:
        if lit_int > 0:
            model[symbol_dict[lit_int]] = True
        else:
            model[symbol_dict[-lit_int]] = False
            
    return model
