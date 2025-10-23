# logicPlan.py
# ------------
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


"""
In logicPlan.py, you will implement logic planning methods which are called by
Pacman agents (in logicAgents.py).
"""

from typing import Dict, List, Tuple, Callable, Generator, Any
import util
import sys
import logic
import game

from logic import conjoin, disjoin
from logic import PropSymbolExpr, Expr, to_cnf, pycoSAT, parseExpr, pl_true

import itertools
import copy
from logic import Expr, FALSE,TRUE

from typing import List, Tuple, Set, FrozenSet
from itertools import combinations
from game import Grid



pacman_str = 'P'
food_str = 'FOOD'
wall_str = 'WALL'
pacman_wall_str = pacman_str + wall_str
DIRECTIONS = ['North', 'South', 'East', 'West']
blocked_str_map = dict([(direction, (direction + "_blocked").upper()) for direction in DIRECTIONS])
geq_num_adj_wall_str_map = dict([(num, "GEQ_{}_adj_walls".format(num)) for num in range(1, 4)])
DIR_TO_DXDY_MAP = {'North':(0, 1), 'South':(0, -1), 'East':(1, 0), 'West':(-1, 0)}


#______________________________________________________________________________
# QUESTION 1

def sentence1() -> Expr:
    """Returns a Expr instance that encodes that the following expressions are all true.
       返回一个 Expr 实例，表示下面这些表达式全都成立（为真）
    A or B
    (not A) if and only if ((not B) or C)
    (not A) or (not B) or C
    """
    "*** BEGIN YOUR CODE HERE ***"
    A=Expr('A')
    B=Expr('B')
    C=Expr('C')

    expr1=A|B
    expr2=~A%((~B)|C)
    expr3=Expr('|',~A,~B,C)

    expr=Expr('&',expr1 , expr2 , expr3)
    return expr

    #util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"


def sentence2() -> Expr:
    """Returns a Expr instance that encodes that the following expressions are all true.
    
    C if and only if (B or D)
    A implies ((not B) and (not D))
    (not (B and (not C))) implies A
    (not D) implies C
    """
    "*** BEGIN YOUR CODE HERE ***"
    A = Expr('A')
    B = Expr('B')
    C = Expr('C')
    D = Expr('D')

    expr1=C%(B|D)
    expr2=A>>(~B&~D)
    expr3=~(B&~C)>>A
    expr4=~D>>C

    expr=Expr('&',expr1 , expr2 , expr3, expr4)
    return expr
    #util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"


def sentence3() -> Expr:
    """Using the symbols PacmanAlive_1 PacmanAlive_0, PacmanBorn_0, and PacmanKilled_0,
    created using the PropSymbolExpr constructor, return a PropSymbolExpr
    instance that encodes the following English sentences (in this order):

    Pacman is alive at time 1 if and only if Pacman was alive at time 0 and it was
    not killed at time 0 or it was not alive at time 0 and it was born at time 0.

    Pacman cannot both be alive at time 0 and be born at time 0.

    Pacman is born at time 0.
    使用符号 PacmanAlive_1、PacmanAlive_0、PacmanBorn_0 和 PacmanKilled_0
    （这些符号都是用 PropSymbolExpr 构造器创建的），
    返回一个 PropSymbolExpr 实例，要求它按如下顺序编码下面这些英语句子：

    1,Pacman 在时刻 1 处于存活状态，
    当且仅当 Pacman 在时刻 0 存活且在时刻 0 没有被杀死，或者在时刻 0 不存活且在时刻 0 被出生。

    2,Pacman 在时刻 0 不能既存活又被出生。

    3,Pacman 在时刻 0 被出生。
    """
    "*** BEGIN YOUR CODE HERE ***"
    PacmanAlive_1=PropSymbolExpr("PacmanAlive",time=1)
    PacmanAlive_0=PropSymbolExpr("PacmanAlive",time=0)
    PacmanBorn_0=PropSymbolExpr("PacmanBorn",time=0)
    PacmanKilled_0=PropSymbolExpr("PacmanKilled",time=0)

    expr1 = PacmanAlive_1%((PacmanAlive_0&~PacmanKilled_0)|(~PacmanAlive_0&PacmanBorn_0))
    expr2 = ~(PacmanAlive_0&PacmanBorn_0)
    expr3 = PacmanBorn_0

    expr=Expr('&',expr1 , expr2 , expr3)
    return expr
    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"

def findModel(sentence: Expr) -> Dict[Expr, bool]:
    """Given a propositional logic sentence (i.e. a Expr instance), returns a satisfying
    model if one exists. Otherwise, returns False.
    给定一个命题逻辑句子（即一个 Expr 实例），如果存在一个使其成立的模型，则返回该模型；否则，返回 False
    """
    cnf_sentence = to_cnf(sentence)
    return pycoSAT(cnf_sentence)

def findModelUnderstandingCheck() -> Dict[Expr, bool]:
    """Returns the result of findModel(Expr('a')) if lower cased expressions were allowed.
    You should not use findModel or Expr in this method.
    如果允许表达式使用小写字母，返回 findModel(Expr('a')) 的结果。
    你在这个方法里不应该使用 findModel 或 Expr。
    """
    #a = Expr('A')
    "*** BEGIN YOUR CODE HERE   ***"
    #print("a.__dict__ is:", a.__dict__)
    # might be helpful for getting ideas 可能有助于你的思维
    class expr:
        def __init__(self,name):
            self.name=name
        def __eq__(self,other):
            return isinstance(other,expr) and self.name==other.name
        def __hash__(self):
            return hash(self.name)
        def __repr__(self):
            return f"{self.name}"
    return {expr('a'):True}
    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"

def entails(premise: Expr, conclusion: Expr) -> bool:
    """Returns True if the premise entails the conclusion and False otherwise.
    如果前提蕴含结论，则返回 True，否则返回 False
    """
    "*** BEGIN YOUR CODE HERE ***"
    expr1 = premise & ~conclusion
    return not findModel(expr1)
    #util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"

def plTrueInverse(assignments: Dict[Expr, bool], inverse_statement: Expr) -> bool:
    """Returns True if the (not inverse_statement) is True given assignments and False otherwise.
    pl_true may be useful here; see logic.py for its description.
    如果在给定赋值的情况下，(not inverse_statement) 为真，则返回 True，否则返回 False。
    这里可以用 pl_true 函数；具体说明请参见 logic.py。
    """
    "*** BEGIN YOUR CODE HERE ***"
    return not pl_true(inverse_statement,assignments)
    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# QUESTION 2
def atLeastOne(literals: List[Expr]) -> Expr:
    """
    Given a list of Expr literals (i.e. in the form A or ~A), return a single
    Expr instance in CNF (conjunctive normal form) that represents the logic
    that at least one of the literals  ist is true.
    给定一个由 Expr 字面量（如 A 或 ~A）组成的列表，返回一个单一的 Expr 实例，表示“至少有一个字面量为真”的合取范式（CNF）公式
    >>> A = PropSymbolExpr('A');
    >>> B = PropSymbolExpr('B');
    >>> symbols = [A, B]
    >>> atleast1 = atLeastOne(symbols)
    >>> model1 = {A:False, B:False}
    >>> print(pl_true(atleast1,model1))
    False
    >>> model2 = {A:False, B:True}
    >>> print(pl_true(atleast1,model2))
    True
    >>> model3 = {A:True, B:True}
    >>> print(pl_true(atleast1,model2))
    True
    """
    "*** BEGIN YOUR CODE HERE ***"
    if not literals:
        return FALSE
    return disjoin(literals)
    #util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"


def atMostOne(literals: List[Expr]) -> Expr:
    """
    Given a list of Expr literals, return a single Expr instance in
    CNF (conjunctive normal form) that represents the logic that at most one of
    the expressions in the list is true.
    itertools.combinations may be useful here.
    给定一个 Expr 字面量列表，返回一个以 CNF（合取范式）表示的单个 Expr 实例，该实例表示“列表中最多有一个表达式为真”的逻辑。
    itertools.combinations 可能对此有帮助。
    """
    "*** BEGIN YOUR CODE HERE ***"
    n = len(literals)
    if n <= 1:
        return TRUE
    clauses = []
    for a, b in combinations(literals, 2):
        clause = Expr("|", Expr("~", a), Expr("~", b))
        clauses.append(clause)
    return conjoin(clauses)
    #util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"


def exactlyOne(literals: List[Expr]) -> Expr:
    """
    Given a list of Expr literals, return a single Expr instance in
    CNF (conjunctive normal form)that represents the logic that exactly one of
    the expressions in the list is true.
    将一个由 Expr 字面量组成的列表，返回一个以 CNF（合取范式）表示的单一 Expr 实例，
    该实例表示“列表中恰好有一个表达式为真”
    """
    "*** BEGIN YOUR CODE HERE ***"
    if not literals:
        return FALSE
    if len(literals) == 1:
        return literals[0]
    return Expr("&", atLeastOne(literals), atMostOne(literals))
    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"
#______________________________________________________________________________
# QUESTION 3

def pacmanSuccessorAxiomSingle(x: int, y: int, time: int, walls_grid: List[List[bool]] = None) -> Expr:
    now, last = time, time - 1
    possible_causes: List[Expr] = []
    if walls_grid[x][y + 1] != 1:
        possible_causes.append(PropSymbolExpr(pacman_str, x, y + 1, time=last)
                               & PropSymbolExpr('South', time=last))
    if walls_grid[x][y - 1] != 1:
        possible_causes.append(PropSymbolExpr(pacman_str, x, y - 1, time=last)
                               & PropSymbolExpr('North', time=last))
    if walls_grid[x + 1][y] != 1:
        possible_causes.append(PropSymbolExpr(pacman_str, x + 1, y, time=last)
                               & PropSymbolExpr('West', time=last))
    if walls_grid[x - 1][y] != 1:
        possible_causes.append(PropSymbolExpr(pacman_str, x - 1, y, time=last)
                               & PropSymbolExpr('East', time=last))
    if not possible_causes:
        return None
    "*** BEGIN YOUR CODE HERE ***"
    possible_causes_sent: Expr = conjoin(disjoin(possible_causes))
    return conjoin(PropSymbolExpr(pacman_str, x, y, time=now) % possible_causes_sent)

    #current_pos = PropSymbolExpr(pacman_str, x, y, time=now)
    #return current_pos % disjoin(possible_causes)
    "*** END YOUR CODE HERE ***"


def SLAMSuccessorAxiomSingle(x: int, y: int, time: int, walls_grid: List[List[bool]]) -> Expr:
    """
    Similar to `pacmanSuccessorStateAxioms` but accounts for illegal actions
    where the pacman might not move timestep to timestep.
    Available actions are ['North', 'East', 'South', 'West']
    """
    now, last = time, time - 1
    moved_causes: List[Expr] = []  # enumerate all possible causes for P[x,y]_t, assuming moved to having moved
    if walls_grid[x][y + 1] != 1:
        moved_causes.append(PropSymbolExpr(pacman_str, x, y + 1, time=last)
                            & PropSymbolExpr('South', time=last))
    if walls_grid[x][y - 1] != 1:
        moved_causes.append(PropSymbolExpr(pacman_str, x, y - 1, time=last)
                            & PropSymbolExpr('North', time=last))
    if walls_grid[x + 1][y] != 1:
        moved_causes.append(PropSymbolExpr(pacman_str, x + 1, y, time=last)
                            & PropSymbolExpr('West', time=last))
    if walls_grid[x - 1][y] != 1:
        moved_causes.append(PropSymbolExpr(pacman_str, x - 1, y, time=last)
                            & PropSymbolExpr('East', time=last))
    if not moved_causes:
        return None

    moved_causes_sent: Expr = conjoin(
        [~PropSymbolExpr(pacman_str, x, y, time=last), ~PropSymbolExpr(wall_str, x, y), disjoin(moved_causes)])

    failed_move_causes: List[Expr] = []  # using merged variables, improves speed significantly
    auxilary_expression_definitions: List[Expr] = []
    for direction in DIRECTIONS:
        dx, dy = DIR_TO_DXDY_MAP[direction]
        wall_dir_clause = PropSymbolExpr(wall_str, x + dx, y + dy) & PropSymbolExpr(direction, time=last)
        wall_dir_combined_literal = PropSymbolExpr(wall_str + direction, x + dx, y + dy, time=last)
        failed_move_causes.append(wall_dir_combined_literal)
        auxilary_expression_definitions.append(wall_dir_combined_literal % wall_dir_clause)

    failed_move_causes_sent: Expr = conjoin([
        PropSymbolExpr(pacman_str, x, y, time=last),
        disjoin(failed_move_causes)])

    return conjoin([PropSymbolExpr(pacman_str, x, y, time=now) % disjoin(
        [moved_causes_sent, failed_move_causes_sent])] + auxilary_expression_definitions)

def exactlyOne(literals):
    # 至少一个为真
    atLeastOne = disjoin(literals)
    # 任何两个不能同时为真
    atMostOne = conjoin([~li | ~lj for i, li in enumerate(literals) for j, lj in enumerate(literals) if i < j])
    return atLeastOne & atMostOne
def pacphysicsAxioms(t: int, all_coords: List[Tuple], non_outer_wall_coords: List[Tuple], walls_grid: List[List] = None,
                     sensorModel: Callable = None, successorAxioms: Callable = None) -> Expr:
    """
        给定：
        t：时间步
        all_coords：整个问题空间所有 (x, y) 坐标的列表
        non_outer_wall_coords：整个问题空间所有 (x, y) 坐标的列表，排除了最外层边界（这些才是吃豆人实际可能所在的格子）
        walls_grid：二维数组，元素为 -1/0/1 或 T/F。仅用于 successorAxioms，不要用于推断吃豆人可能的位置。
        sensorModel(t, non_outer_wall_coords) -> Expr：生成传感器模型公理的函数。如果为 None，则不提供，不应调用。
        successorAxioms(t, walls_grid, non_outer_wall_coords) -> Expr：生成后继状态公理的函数。如果为 None，则不提供，不应调用。
        返回一个包含如下全部内容的逻辑语句：
        - 对于所有 (x, y) ∈ all_coords： 如果 (x, y) 位置有墙，则吃豆人不能在 (x, y) 位置
        - 在时间步 t，吃豆人恰好在一个格子上
        - 在时间步 t，吃豆人恰好执行一个动作
        - 调用 sensorModel(...) 的结果，除非为 None
        - 调用 successorAxioms(...) 的结果，描述吃豆人在本时间步如何到达各个位置。要考虑特殊情况，若为 None 不调用
    """
    pacphysics_sentences = []

    "*** BEGIN YOUR CODE HERE ***"
    for x, y in all_coords:
        pacphysics_sentences.append(
            PropSymbolExpr(wall_str, x, y) >> ~PropSymbolExpr(pacman_str, x, y, time=t)
        )

    pacphysics_sentences.append(
        exactlyOne([PropSymbolExpr(pacman_str, x, y, time=t) for (x, y) in non_outer_wall_coords]))

    pacphysics_sentences.append(exactlyOne([PropSymbolExpr(action, time=t) for action in DIRECTIONS]))

    if sensorModel is not None:
        pacphysics_sentences.append(sensorModel(t, non_outer_wall_coords))

    if successorAxioms is not None and walls_grid is not None and t > 0:
        pacphysics_sentences.append(successorAxioms(t, walls_grid, non_outer_wall_coords))
    return conjoin(pacphysics_sentences)
"*** END YOUR CODE HERE ***"




def checkLocationSatisfiability(x1_y1: Tuple[int, int], x0_y0: Tuple[int, int], action0, action1, problem):
    """
给定：

x1_y1 = (x1, y1)：候选的位置，时刻 t = 1
x0_y0 = (x0, y0)：Pacman 在时刻 t = 0 的位置
action0：在时刻 t = 0 时 Pacman 的动作，取自 DIRECTIONS 中的四个动作之一
action1：用于确保与自动评分程序（autograder）解答一致
problem：一个 logicAgents.LocMapProblem 的实例
注意：

没有 sensorModel，因为我们对世界是完全知道的
在需要的地方，后继公理（successorAxioms）应当使用 allLegalSuccessorAxioms
返回：

一个模型，使得 Pacman 在时刻 t = 1 位于 (x1, y1)
一个模型，使得 Pacman 在时刻 t = 1 不位于 (x1, y1)
    """
    walls_grid = problem.walls
    walls_list = walls_grid.asList()
    all_coords = list(itertools.product(range(problem.getWidth() + 2), range(problem.getHeight() + 2)))
    non_outer_wall_coords = list(itertools.product(range(1, problem.getWidth() + 1), range(1, problem.getHeight() + 1)))
    KB = []
    x0, y0 = x0_y0
    x1, y1 = x1_y1

    # We know which coords are walls:
    map_sent = [PropSymbolExpr(wall_str, x, y) for x, y in walls_list]
    KB.append(conjoin(map_sent))

    "*** BEGIN YOUR CODE HERE ***"
    KB.append(PropSymbolExpr(pacman_str, x0, y0, time=0))

    KB.append(PropSymbolExpr(action0, time=0))
    KB.append(PropSymbolExpr(action1, time=1))

    for (wx, wy) in walls_list:
        KB.append(~PropSymbolExpr(pacman_str, wx, wy, time=0))
        KB.append(~PropSymbolExpr(pacman_str, wx, wy, time=1))
    KB.append(exactlyOne([PropSymbolExpr(pacman_str, x, y, time=0) for (x, y) in non_outer_wall_coords]))
    KB.append(exactlyOne([PropSymbolExpr(pacman_str, x, y, time=1) for (x, y) in non_outer_wall_coords]))
    
    KB.append(exactlyOne([PropSymbolExpr(a, time=0) for a in DIRECTIONS]))
    KB.append(exactlyOne([PropSymbolExpr(a, time=1) for a in DIRECTIONS]))

    physics_1 = pacphysicsAxioms(1, all_coords, non_outer_wall_coords, walls_grid, None, None)
    if isinstance(physics_1, list):
        KB.extend(physics_1)
    else:
        KB.append(physics_1)

    KB.append(allLegalSuccessorAxioms(1, walls_grid, non_outer_wall_coords))

    KB_model1 = KB + [PropSymbolExpr(pacman_str, x1, y1, time=1)]
    KB_model2 = KB + [~PropSymbolExpr(pacman_str, x1, y1, time=1)]

    model1 = findModel(conjoin(KB_model1))
    model2 = findModel(conjoin(KB_model2))

    return (model1, model2)
    "*** END YOUR CODE HERE ***"
#______________________________________________________________________________
# QUESTION 4

def positionLogicPlan(problem) -> List:
    """
    给定一个 PositionPlanningProblem 的实例，返回一条到达目标的动作序列。
可用动作包括 ['North', 'East', 'South', 'West']。
注意：STOP 不是可用动作。
概述：逐步增加知识库，每个时间步都进行模型查询。不要使用 pacphysicsAxioms。
    """
    walls_grid = problem.walls
    width, height = problem.getWidth(), problem.getHeight()
    walls_list = walls_grid.asList()#墙列表
    x0, y0 = problem.startState#开始位置
    xg, yg = problem.goal      #结束位置
    
    # Get lists of possible locations (i.e. without walls) and possible actions
    #获取所有可能的位置（即没有墙的位置）以及所有可能的动作列表
    all_coords = list(itertools.product(range(width + 2), range(height + 2)))#所有位置
    non_wall_coords = [loc for loc in all_coords if loc not in walls_list]#所有没有墙的位置
    actions = [ 'North', 'South', 'East', 'West' ]
    KB = []
    "*** BEGIN YOUR CODE HERE ***"
    KB.append(f"PacmanAt({x0},{y0},0)")

    # 2. 对每个时间步t，逐步扩展知识库
    for t in range(50):
        # 2.1 添加唯一性约束：t时刻，吃豆人只能在唯一一个非墙格子
        KB.append(f"exactlyOne({','.join([f'PacmanAt({x},{y},{t})' for (x, y) in non_wall_coords])})")

        # 2.2 如果已能到达目标，则提取并返回动作序列
        model = findModel(KB)
        if model and model.get(f'PacmanAt({xg},{yg},{t})', False):
            return extractActionSequence(model, actions)

        # 2.3 添加运动模型约束：吃豆人从t到t+1的所有可能位置和动作
        for (x, y) in non_wall_coords:
            for action in actions:
                KB.append(positionSuccessorAxiomSingle(x, y, t, action, walls_grid))

    # 若无法到达目标，返回空
    return []
    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# QUESTION 5

def foodLogicPlan(problem) -> List:
    """
   给定一个 FoodPlanningProblem 的实例，返回一个能够帮助 Pacman 吃掉所有食物的动作列表。
    可用的动作有 ['North', 'East', 'South', 'West']。
   注意，STOP 不是可用动作。
     综述：逐步添加知识，并在每个时间步查询一次模型。不要使用 pacphysicsAxioms。
    """
    walls = problem.walls
    width, height = problem.getWidth(), problem.getHeight()
    walls_list = walls.asList()
    (x0, y0), food = problem.start
    food = food.asList()
    all_coords = list(itertools.product(range(width + 2), range(height + 2)))

    non_wall_coords = [loc for loc in all_coords if loc not in walls_list]
    actions = [ 'North', 'South', 'East', 'West' ]

    KB = []

    "*** BEGIN YOUR CODE HERE ***"
    KB.append(PropSymbolExpr('P', x0, y0, time=0))
    for (fx, fy) in food:
        KB.append(PropSymbolExpr('F', fx, fy, time=0))
    max_time = width * height * max(1, len(food))
    for t in range(max_time + 1):
        for (wx, wy) in walls_list:
            KB.append(~PropSymbolExpr('P', wx, wy, time=t))

    def exactlyOne(literals):
        at_least_one = disjoin(literals)
        at_most_one = conjoin([~a | ~b for i, a in enumerate(literals) for b in literals[i + 1:]])
        return at_least_one & at_most_one

    for t in range(1, max_time + 1):
        KB.append(exactlyOne([PropSymbolExpr(a, time=t) for a in actions]))

    def positionSuccessorAxiom(x, y, t):
        possible_causes = []
        if (x, y) not in walls_list:
            if (x, y - 1) in non_wall_coords:
                possible_causes.append(PropSymbolExpr('P', x, y - 1, time=t - 1) & PropSymbolExpr('North', time=t))
            if (x, y + 1) in non_wall_coords:
                possible_causes.append(PropSymbolExpr('P', x, y + 1, time=t - 1) & PropSymbolExpr('South', time=t))
            if (x - 1, y) in non_wall_coords:
                possible_causes.append(PropSymbolExpr('P', x - 1, y, time=t - 1) & PropSymbolExpr('East', time=t))
            if (x + 1, y) in non_wall_coords:
                possible_causes.append(PropSymbolExpr('P', x + 1, y, time=t - 1) & PropSymbolExpr('West', time=t))
        if possible_causes:
            return PropSymbolExpr('P', x, y, time=t) % disjoin(possible_causes)
        else:
            return None

    def foodSuccessorAxiom(x, y, t):
        eaten = PropSymbolExpr('P', x, y, time=t) & ~PropSymbolExpr('F', x, y, time=t)
        still = PropSymbolExpr('F', x, y, time=t - 1) & ~PropSymbolExpr('P', x, y, time=t)
        return PropSymbolExpr('F', x, y, time=t) % (
                    PropSymbolExpr('F', x, y, time=t - 1) & ~PropSymbolExpr('P', x, y, time=t))

    for t in range(1, max_time + 1):
        for (x, y) in non_wall_coords:
            axiom = positionSuccessorAxiom(x, y, t)
            if axiom is not None:
                KB.append(axiom)
        for (fx, fy) in food:
            KB.append(foodSuccessorAxiom(fx, fy, t))
        KB_goal = KB + [~PropSymbolExpr('F', fx, fy, time=t) for (fx, fy) in food]
        model = findModel(conjoin(KB_goal))
        if model:
            action_list = []
            for k in range(1, t + 1):
                for action in actions:
                    if model.get(PropSymbolExpr(action, time=k), False):
                        action_list.append(action)
                        break
            return action_list
    return []
    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# QUESTION 6

def localization(problem, agent) -> Generator:
    '''
    problem: a LocalizationProblem instance
    agent: a LocalizationLogicAgent instance
    '''
    walls_grid = problem.walls
    walls_list = walls_grid.asList()
    all_coords = list(itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)))
    non_outer_wall_coords = list(itertools.product(range(1, problem.getWidth()+1), range(1, problem.getHeight()+1)))

    KB = []

    "*** BEGIN YOUR CODE HERE ***"
    util.raiseNotDefined()

    for t in range(agent.num_timesteps):
        "*** END YOUR CODE HERE ***"
        yield possible_locations

#______________________________________________________________________________
# QUESTION 7

def mapping(problem, agent) -> Generator:
    '''
    problem: a MappingProblem instance
    agent: a MappingLogicAgent instance
    '''
    pac_x_0, pac_y_0 = problem.startState
    KB = []
    all_coords = list(itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)))
    non_outer_wall_coords = list(itertools.product(range(1, problem.getWidth()+1), range(1, problem.getHeight()+1)))

    # map describes what we know, for GUI rendering purposes. -1 is unknown, 0 is open, 1 is wall
    known_map = [[-1 for y in range(problem.getHeight()+2)] for x in range(problem.getWidth()+2)]

    # Pacman knows that the outer border of squares are all walls
    outer_wall_sent = []
    for x, y in all_coords:
        if ((x == 0 or x == problem.getWidth() + 1)
                or (y == 0 or y == problem.getHeight() + 1)):
            known_map[x][y] = 1
            outer_wall_sent.append(PropSymbolExpr(wall_str, x, y))
    KB.append(conjoin(outer_wall_sent))

    "*** BEGIN YOUR CODE HERE ***"
    util.raiseNotDefined()

    for t in range(agent.num_timesteps):
        "*** END YOUR CODE HERE ***"
        yield known_map

#______________________________________________________________________________
# QUESTION 8

def slam(problem, agent) -> Generator:
    '''
    problem: a SLAMProblem instance
    agent: a SLAMLogicAgent instance
    '''
    pac_x_0, pac_y_0 = problem.startState
    KB = []
    all_coords = list(itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)))
    non_outer_wall_coords = list(itertools.product(range(1, problem.getWidth()+1), range(1, problem.getHeight()+1)))

    # map describes what we know, for GUI rendering purposes. -1 is unknown, 0 is open, 1 is wall
    known_map = [[-1 for y in range(problem.getHeight()+2)] for x in range(problem.getWidth()+2)]

    # We know that the outer_coords are all walls.
    outer_wall_sent = []
    for x, y in all_coords:
        if ((x == 0 or x == problem.getWidth() + 1)
                or (y == 0 or y == problem.getHeight() + 1)):
            known_map[x][y] = 1
            outer_wall_sent.append(PropSymbolExpr(wall_str, x, y))
    KB.append(conjoin(outer_wall_sent))

    "*** BEGIN YOUR CODE HERE ***"
    util.raiseNotDefined()

    for t in range(agent.num_timesteps):
        "*** END YOUR CODE HERE ***"
        yield (known_map, possible_locations)


# Abbreviations
plp = positionLogicPlan
loc = localization
mp = mapping
flp = foodLogicPlan
# Sometimes the logic module uses pretty deep recursion on long expressions
sys.setrecursionlimit(100000)

#______________________________________________________________________________
# Important expression generating functions, useful to read for understanding of this project.


def sensorAxioms(t: int, non_outer_wall_coords: List[Tuple[int, int]]) -> Expr:
    all_percept_exprs = []
    combo_var_def_exprs = []
    for direction in DIRECTIONS:
        percept_exprs = []
        dx, dy = DIR_TO_DXDY_MAP[direction]
        for x, y in non_outer_wall_coords:
            combo_var = PropSymbolExpr(pacman_wall_str, x, y, x + dx, y + dy, time=t)
            percept_exprs.append(combo_var)
            combo_var_def_exprs.append(combo_var % (
                PropSymbolExpr(pacman_str, x, y, time=t) & PropSymbolExpr(wall_str, x + dx, y + dy)))

        percept_unit_clause = PropSymbolExpr(blocked_str_map[direction], time = t)
        all_percept_exprs.append(percept_unit_clause % disjoin(percept_exprs))

    return conjoin(all_percept_exprs + combo_var_def_exprs)


def fourBitPerceptRules(t: int, percepts: List) -> Expr:
    """
    Localization and Mapping both use the 4 bit sensor, which tells us True/False whether
    a wall is to pacman's north, south, east, and west.
    """
    assert isinstance(percepts, list), "Percepts must be a list."
    assert len(percepts) == 4, "Percepts must be a length 4 list."

    percept_unit_clauses = []
    for wall_present, direction in zip(percepts, DIRECTIONS):
        percept_unit_clause = PropSymbolExpr(blocked_str_map[direction], time=t)
        if not wall_present:
            percept_unit_clause = ~PropSymbolExpr(blocked_str_map[direction], time=t)
        percept_unit_clauses.append(percept_unit_clause) # The actual sensor readings
    return conjoin(percept_unit_clauses)


def numAdjWallsPerceptRules(t: int, percepts: List) -> Expr:
    """
    SLAM uses a weaker numAdjWallsPerceptRules sensor, which tells us how many walls pacman is adjacent to
    in its four directions.
        000 = 0 adj walls.
        100 = 1 adj wall.
        110 = 2 adj walls.
        111 = 3 adj walls.
    """
    assert isinstance(percepts, list), "Percepts must be a list."
    assert len(percepts) == 3, "Percepts must be a length 3 list."

    percept_unit_clauses = []
    for i, percept in enumerate(percepts):
        n = i + 1
        percept_literal_n = PropSymbolExpr(geq_num_adj_wall_str_map[n], time=t)
        if not percept:
            percept_literal_n = ~percept_literal_n
        percept_unit_clauses.append(percept_literal_n)
    return conjoin(percept_unit_clauses)


def SLAMSensorAxioms(t: int, non_outer_wall_coords: List[Tuple[int, int]]) -> Expr:
    all_percept_exprs = []
    combo_var_def_exprs = []
    for direction in DIRECTIONS:
        percept_exprs = []
        dx, dy = DIR_TO_DXDY_MAP[direction]
        for x, y in non_outer_wall_coords:
            combo_var = PropSymbolExpr(pacman_wall_str, x, y, x + dx, y + dy, time=t)
            percept_exprs.append(combo_var)
            combo_var_def_exprs.append(combo_var % (PropSymbolExpr(pacman_str, x, y, time=t) & PropSymbolExpr(wall_str, x + dx, y + dy)))

        blocked_dir_clause = PropSymbolExpr(blocked_str_map[direction], time=t)
        all_percept_exprs.append(blocked_dir_clause % disjoin(percept_exprs))

    percept_to_blocked_sent = []
    for n in range(1, 4):
        wall_combos_size_n = itertools.combinations(blocked_str_map.values(), n)
        n_walls_blocked_sent = disjoin([
            conjoin([PropSymbolExpr(blocked_str, time=t) for blocked_str in wall_combo])
            for wall_combo in wall_combos_size_n])
        # n_walls_blocked_sent is of form: (N & S) | (N & E) | ...
        percept_to_blocked_sent.append(
            PropSymbolExpr(geq_num_adj_wall_str_map[n], time=t) % n_walls_blocked_sent)

    return conjoin(all_percept_exprs + combo_var_def_exprs + percept_to_blocked_sent)


def allLegalSuccessorAxioms(t: int, walls_grid: List[List], non_outer_wall_coords: List[Tuple[int, int]]) -> Expr:
    """walls_grid can be a 2D array of ints or bools."""
    all_xy_succ_axioms = []
    for x, y in non_outer_wall_coords:
        xy_succ_axiom = pacmanSuccessorAxiomSingle(
            x, y, t, walls_grid)
        if xy_succ_axiom:
            all_xy_succ_axioms.append(xy_succ_axiom)
    return conjoin(all_xy_succ_axioms)


def SLAMSuccessorAxioms(t: int, walls_grid: List[List], non_outer_wall_coords: List[Tuple[int, int]]) -> Expr:
    """walls_grid can be a 2D array of ints or bools."""
    all_xy_succ_axioms = []
    for x, y in non_outer_wall_coords:
        xy_succ_axiom = SLAMSuccessorAxiomSingle(
            x, y, t, walls_grid)
        if xy_succ_axiom:
            all_xy_succ_axioms.append(xy_succ_axiom)
    return conjoin(all_xy_succ_axioms)

#______________________________________________________________________________
# Various useful functions, are not needed for completing the project but may be useful for debugging


def modelToString(model: Dict[Expr, bool]) -> str:
    """Converts the model to a string for printing purposes. The keys of a model are 
    sorted before converting the model to a string.
    
    model: Either a boolean False or a dictionary of Expr symbols (keys) 
    and a corresponding assignment of True or False (values). This model is the output of 
    a call to pycoSAT.
    """
    if model == False:
        return "False" 
    else:
        # Dictionary
        modelList = sorted(model.items(), key=lambda item: str(item[0]))
        return str(modelList)


def extractActionSequence(model: Dict[Expr, bool], actions: List) -> List:
    """
    Convert a model in to an ordered list of actions.
    model: Propositional logic model stored as a dictionary with keys being
    the symbol strings and values being Boolean: True or False
    Example:
    >>> model = {"North[2]":True, "P[3,4,0]":True, "P[3,3,0]":False, "West[0]":True, "GhostScary":True, "West[2]":False, "South[1]":True, "East[0]":False}
    >>> actions = ['North', 'South', 'East', 'West']
    >>> plan = extractActionSequence(model, actions)
    >>> print(plan)
    ['West', 'South', 'North']
    """
    plan = [None for _ in range(len(model))]
    for sym, val in model.items():
        parsed = parseExpr(sym)
        if type(parsed) == tuple and parsed[0] in actions and val:
            action, _, time = parsed
            plan[time] = action
    #return list(filter(lambda x: x is not None, plan))
    return [x for x in plan if x is not None]


# Helpful Debug Method
def visualizeCoords(coords_list, problem) -> None:
    wallGrid = game.Grid(problem.walls.width, problem.walls.height, initialValue=False)
    for (x, y) in itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)):
        if (x, y) in coords_list:
            wallGrid.data[x][y] = True
    print(wallGrid)


# Helpful Debug Method
def visualizeBoolArray(bool_arr, problem) -> None:
    wallGrid = game.Grid(problem.walls.width, problem.walls.height, initialValue=False)
    wallGrid.data = copy.deepcopy(bool_arr)
    print(wallGrid)

class PlanningProblem:
    """
    This class outlines the structure of a planning problem, but doesn't implement
    any of the methods (in object-oriented terminology: an abstract class).

    You do not need to change anything in this class, ever.
    """

    def getStartState(self):
        """
        Returns the start state for the planning problem.
        """
        util.raiseNotDefined()

    def getGhostStartStates(self):
        """
        Returns a list containing the start state for each ghost.
        Only used in problems that use ghosts (FoodGhostPlanningProblem)
        """
        util.raiseNotDefined()
        
    def getGoalState(self):
        """
        Returns goal state for problem. Note only defined for problems that have
        a unique goal state such as PositionPlanningProblem
        """
        util.raiseNotDefined()
