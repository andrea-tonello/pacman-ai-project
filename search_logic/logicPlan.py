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
    
    A or B
    (not A) if and only if ((not B) or C)
    (not A) or (not B) or C
    """
    "*** BEGIN YOUR CODE HERE ***"
    A = Expr('A'); B = Expr('B'); C = Expr('C')

    first = A | B
    second = ~A % (~B | C)
    third = disjoin([~A, ~B, C])

    return conjoin([first, second, third])
    "*** END YOUR CODE HERE ***"



def sentence2() -> Expr:
    """Returns a Expr instance that encodes that the following expressions are all true.
    
    C if and only if (B or D)
    A implies ((not B) and (not D))
    (not (B and (not C))) implies A
    (not D) implies C
    """
    "*** BEGIN YOUR CODE HERE ***"
    A = Expr('A'); B = Expr('B'); C = Expr('C'); D = Expr('D')

    first = C % (B | D)
    second = Expr('>>', A, (~B & ~D))
    third = Expr('>>', Expr('~', (B & ~C)), A)
    fourth = Expr('>>', ~D, C)
    
    return conjoin([first, second, third, fourth])
    "*** END YOUR CODE HERE ***"


def sentence3() -> Expr:
    """Using the symbols PacmanAlive_1 PacmanAlive_0, PacmanBorn_0, and PacmanKilled_0,
    created using the PropSymbolExpr constructor, return a PropSymbolExpr
    instance that encodes the following English sentences (in this order):

    Pacman is alive at time 1 if and only if Pacman was alive at time 0 and it was
    not killed at time 0 or it was not alive at time 0 and it was born at time 0.

    Pacman cannot both be alive at time 0 and be born at time 0.

    Pacman is born at time 0.
    """
    "*** BEGIN YOUR CODE HERE ***"
    PacmanAlive_0 = PropSymbolExpr('PacmanAlive', time=0)
    PacmanAlive_1 = PropSymbolExpr('PacmanAlive', time=1)
    PacmanBorn_0 = PropSymbolExpr('PacmanBorn', time=0)
    PacmanKilled_0 = PropSymbolExpr('PacmanKilled', time=0)

    first = PacmanAlive_1 % ((PacmanAlive_0 & ~PacmanKilled_0) | (~PacmanAlive_0 & PacmanBorn_0))
    second = Expr('~', (PacmanAlive_0 & PacmanBorn_0))
    third = PacmanBorn_0

    return conjoin(first, second, third)
    "*** END YOUR CODE HERE ***"

def findModel(sentence: Expr) -> Dict[Expr, bool]:
    """Given a propositional logic sentence (i.e. a Expr instance), returns a satisfying
    model if one exists. Otherwise, returns False.
    """
    cnf_sentence = to_cnf(sentence)
    return pycoSAT(cnf_sentence)


# OUTPUT for findModel(sentenceX())
    # sentence1 -> {A: False, B: True, C: True}
    # sentence2 -> False -> No satisfying model exists!
    # sentence3 -> {PacmanAlive_1: True, PacmanAlive_0: False, PacmanKilled_0: False, PacmanBorn_0: True}

class LowercaseExpr:
    def __init__(self, char):
        self.char = char

    def __repr__(self):
        return str(self.char).lower()   # represents whichever character as his lowercase counterpart, if possible
    
def findModelUnderstandingCheck() -> Dict[Expr, bool]:
    """Returns the result of findModel(Expr('a')) if lower cased expressions were allowed.
    You should not use findModel or Expr in this method.
    """
    a = Expr('A')
    "*** BEGIN YOUR CODE HERE ***"
    key_a = LowercaseExpr('a')
    return {key_a: True}
    # print("a.__dict__ is:", a.__dict__) # might be helpful for getting ideas
    "*** END YOUR CODE HERE ***"


def entails(premise: Expr, conclusion: Expr) -> bool:
    """Returns True if the premise entails the conclusion and False otherwise.
    """
    "*** BEGIN YOUR CODE HERE ***"
    # A entails B iff A & ~B is unsatisfiable -> findModel must return False
    sentence = premise & Expr('~', conclusion)
    
    if findModel(sentence) is False:
        return True
    else:
        return False
    "*** END YOUR CODE HERE ***"

def plTrueInverse(assignments: Dict[Expr, bool], inverse_statement: Expr) -> bool:
    """Returns True if the (not inverse_statement) is True given assignments and False otherwise.
    pl_true may be useful here; see logic.py for its description.
    """
    "*** BEGIN YOUR CODE HERE ***"
    NotIS = Expr('~', inverse_statement)
    res = pl_true(NotIS, assignments)   # assignment for not inverse_statement

    if res is True:
        return True
    else:
        return False
    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# QUESTION 2

def atLeastOne(literals: List[Expr]) -> Expr:
    """
    Given a list of Expr literals (i.e. in the form A or ~A), return a single 
    Expr instance in CNF (conjunctive normal form) that represents the logic 
    that at least one of the literals list is true.
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
    # As soon as I find one literal with a valid True assignment, return the disjunction of all the literals

    for lit in literals:
        
        assignment = findModel(lit)
        result = pl_true(lit, assignment)
        
        if result is True:
            return disjoin(literals)

    "*** END YOUR CODE HERE ***"


def atMostOne(literals: List[Expr]) -> Expr:
    """
    Given a list of Expr literals, return a single Expr instance in 
    CNF (conjunctive normal form) that represents the logic that at most one of 
    the expressions in the list is true.
    itertools.combinations may be useful here.
    """
    "*** BEGIN YOUR CODE HERE ***"
    # Let's say I have these literals: T F F F F. I want to build a cnf sentence that is True.
    # if I create a conjunction of every combination of 2-literal-disjunctions, with each literal negated, I'll get
    #     (~T | ~F) & (~F | ~F) & (~F | ~F)... == True
    # if my list was instead T F T F F (so more than one literal is True), I would get
    #     (~T | ~F) & (~F | ~F) & (~T | ~T)... == False
    
    literals_comb = list(itertools.combinations(literals,2))
    sentence = []

    for lit1, lit2 in literals_comb:
        sentence.append(Expr('~', lit1) | Expr('~', lit2))
    return conjoin(sentence)

    "*** END YOUR CODE HERE ***"


def exactlyOne(literals: List[Expr]) -> Expr:
    """
    Given a list of Expr literals, return a single Expr instance in 
    CNF (conjunctive normal form)that represents the logic that exactly one of 
    the expressions in the list is true.
    """
    "*** BEGIN YOUR CODE HERE ***"
    # I just need to conjoin atLeastOne ad atMostOne: if 0 literals are True, then atLeastOne will be False;
    # if more than one literal is True, then atMostOne will be False. So the only way for (atLeastOne & atMostOne)
    # to be True is to have exactly one literal set to True
    
    atLeastOneSentence = atLeastOne(literals)
    atMostOneSentence = atMostOne(literals)

    return atLeastOneSentence & atMostOneSentence
    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# QUESTION 3

def pacmanSuccessorAxiomSingle(x: int, y: int, time: int, walls_grid: List[List[bool]]=None) -> Expr:
    """
    Successor state axiom for state (x,y,t) (from t-1), given the board (as a 
    grid representing the wall locations).
    Current <==> (previous position at time t-1) & (took action to move to x, y)
    Available actions are ['North', 'East', 'South', 'West']
    Note that STOP is not an available action.
    """
    now, last = time, time - 1
    possible_causes: List[Expr] = [] # enumerate all possible causes for P[x,y]_t
    # the if statements give a small performance boost and are required for q4 and q5 correctness
    if walls_grid[x][y+1] != 1:
        possible_causes.append( PropSymbolExpr(pacman_str, x, y+1, time=last)
                            & PropSymbolExpr('South', time=last))
    if walls_grid[x][y-1] != 1:
        possible_causes.append( PropSymbolExpr(pacman_str, x, y-1, time=last) 
                            & PropSymbolExpr('North', time=last))
    if walls_grid[x+1][y] != 1:
        possible_causes.append( PropSymbolExpr(pacman_str, x+1, y, time=last) 
                            & PropSymbolExpr('West', time=last))
    if walls_grid[x-1][y] != 1:
        possible_causes.append( PropSymbolExpr(pacman_str, x-1, y, time=last) 
                            & PropSymbolExpr('East', time=last))
    if not possible_causes:
        return None
    
    "*** BEGIN YOUR CODE HERE ***"
    return PropSymbolExpr(pacman_str, x, y, time=now) % disjoin(possible_causes)
    # Pacman is allowed to be in (x,y) if and only he came from one of the possible causes
    "*** END YOUR CODE HERE ***"


def SLAMSuccessorAxiomSingle(x: int, y: int, time: int, walls_grid: List[List[bool]]) -> Expr:
    """
    Similar to `pacmanSuccessorStateAxioms` but accounts for illegal actions
    where the pacman might not move timestep to timestep.
    Available actions are ['North', 'East', 'South', 'West']
    """
    now, last = time, time - 1
    moved_causes: List[Expr] = [] # enumerate all possible causes for P[x,y]_t, assuming moved to having moved
    if walls_grid[x][y+1] != 1:
        moved_causes.append( PropSymbolExpr(pacman_str, x, y+1, time=last)
                            & PropSymbolExpr('South', time=last))
    if walls_grid[x][y-1] != 1:
        moved_causes.append( PropSymbolExpr(pacman_str, x, y-1, time=last) 
                            & PropSymbolExpr('North', time=last))
    if walls_grid[x+1][y] != 1:
        moved_causes.append( PropSymbolExpr(pacman_str, x+1, y, time=last) 
                            & PropSymbolExpr('West', time=last))
    if walls_grid[x-1][y] != 1:
        moved_causes.append( PropSymbolExpr(pacman_str, x-1, y, time=last) 
                            & PropSymbolExpr('East', time=last))
    if not moved_causes:
        return None

    moved_causes_sent: Expr = conjoin([~PropSymbolExpr(pacman_str, x, y, time=last) , ~PropSymbolExpr(wall_str, x, y), disjoin(moved_causes)])

    failed_move_causes: List[Expr] = [] # using merged variables, improves speed significantly
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

    return conjoin([PropSymbolExpr(pacman_str, x, y, time=now) % disjoin([moved_causes_sent, failed_move_causes_sent])] + auxilary_expression_definitions)


def pacphysicsAxioms(t: int, all_coords: List[Tuple], non_outer_wall_coords: List[Tuple], walls_grid: List[List] = None, sensorModel: Callable = None, successorAxioms: Callable = None) -> Expr:
    """
    Given:
        t: timestep
        all_coords: list of (x, y) coordinates of the entire problem
        non_outer_wall_coords: list of (x, y) coordinates of the entire problem,
            excluding the outer border (these are the actual squares pacman can
            possibly be in)
        walls_grid: 2D array of either -1/0/1 or T/F. Used only for successorAxioms.
            Do NOT use this when making possible locations for pacman to be in.
        sensorModel(t, non_outer_wall_coords) -> Expr: function that generates
            the sensor model axioms. If None, it's not provided, so shouldn't be run.
        successorAxioms(t, walls_grid, non_outer_wall_coords) -> Expr: function that generates
            the sensor model axioms. If None, it's not provided, so shouldn't be run.
    Return a logic sentence containing all of the following:
        - for all (x, y) in all_coords:
            If a wall is at (x, y) --> Pacman is not at (x, y)
        - Pacman is at exactly one of the squares at timestep t.
        - Pacman takes exactly one action at timestep t.
        - Results of calling sensorModel(...), unless None.
        - Results of calling successorAxioms(...), describing how Pacman can end in various
            locations on this time step. Consider edge cases. Don't call if None.
    """
    pacphysics_sentences = []

    "*** BEGIN YOUR CODE HERE ***"
    # given timestep t:

    # if there's a wall at (x,y), pacman is not at (x,y)
    for x,y in all_coords:
        pacphysics_sentences.append(Expr('>>', PropSymbolExpr(wall_str, x, y), ~PropSymbolExpr(pacman_str, x, y, time=t)))
    
    # pacman is at exactly one (x,y) in non_outer_walls_coords
    literals_position = []
    for x,y in non_outer_wall_coords:
        literals_position.append(PropSymbolExpr(pacman_str, x, y, time=t))
    pacphysics_sentences.append(exactlyOne(literals_position))
    
    # pacman can only perform one action
    literals_action = []
    for action in DIRECTIONS:
        literals_action.append(PropSymbolExpr(action, time=t))
    pacphysics_sentences.append(exactlyOne(literals_action))
    
    # axioms for the sensor
    if sensorModel is not None:
        useful_return1 = sensorModel(t, non_outer_wall_coords)
        pacphysics_sentences.append(useful_return1)
    
    # axioms for the successor (available at t >= 1)
    if t>0 and successorAxioms is not None:
        useful_return2 = successorAxioms(t, walls_grid, non_outer_wall_coords)
        pacphysics_sentences.append(useful_return2)

    "*** END YOUR CODE HERE ***"

    return conjoin(pacphysics_sentences)


def checkLocationSatisfiability(x1_y1: Tuple[int, int], x0_y0: Tuple[int, int], action0, action1, problem):
    """
    Given:
        - x1_y1 = (x1, y1), a potential location at time t = 1
        - x0_y0 = (x0, y0), Pacman's location at time t = 0
        - action0 = one of the four items in DIRECTIONS, Pacman's action at time t = 0
        - action1 = to ensure match with autograder solution
        - problem = an instance of logicAgents.LocMapProblem
    Note:
        - there's no sensorModel because we know everything about the world
        - the successorAxioms should be allLegalSuccessorAxioms where needed
    Return:
        - a model where Pacman is at (x1, y1) at time t = 1
        - a model where Pacman is not at (x1, y1) at time t = 1
    """
    walls_grid = problem.walls
    walls_list = walls_grid.asList()
    all_coords = list(itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)))
    non_outer_wall_coords = list(itertools.product(range(1, problem.getWidth()+1), range(1, problem.getHeight()+1)))
    KB = []
    x0, y0 = x0_y0
    x1, y1 = x1_y1

    # We know which coords are walls:
    map_sent = [PropSymbolExpr(wall_str, x, y) for x, y in walls_list]
    KB.append(conjoin(map_sent))

    "*** BEGIN YOUR CODE HERE ***"

    # adding physics axioms for each timestep
    KB.append(pacphysicsAxioms(0, all_coords, non_outer_wall_coords, walls_grid=walls_grid, sensorModel=None, successorAxioms=allLegalSuccessorAxioms))
    KB.append(pacphysicsAxioms(1, all_coords, non_outer_wall_coords, walls_grid=walls_grid, sensorModel=None, successorAxioms=allLegalSuccessorAxioms))
    
    KB.append(PropSymbolExpr(pacman_str, x0, y0, time=0))   # pacman's initial condition
    KB.append(PropSymbolExpr(action0, time=0))     # pacman takes action0
    KB.append(PropSymbolExpr(action1, time=1))     # pacman takes action1

    knowledge_check = conjoin(KB)

    # pacman is (or isn't) at (x1, y1) at time 1 given current knowledge
    model_1 = findModel(conjoin([PropSymbolExpr(pacman_str, x1, y1, time=1), knowledge_check]))
    model_2 = findModel(conjoin([~PropSymbolExpr(pacman_str, x1, y1, time=1), knowledge_check]))

    return (model_1, model_2)
    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# QUESTION 4

def positionLogicPlan(problem) -> List:
    """
    Given an instance of a PositionPlanningProblem, return a list of actions that lead to the goal.
    Available actions are ['North', 'East', 'South', 'West']
    Note that STOP is not an available action.
    Overview: add knowledge incrementally, and query for a model each timestep. Do NOT use pacphysicsAxioms.
    """
    walls_grid = problem.walls
    width, height = problem.getWidth(), problem.getHeight()
    walls_list = walls_grid.asList()
    x0, y0 = problem.startState
    xg, yg = problem.goal
    
    # Get lists of possible locations (i.e. without walls) and possible actions
    all_coords = list(itertools.product(range(width + 2), 
            range(height + 2)))
    non_wall_coords = [loc for loc in all_coords if loc not in walls_list]
    actions = [ 'North', 'South', 'East', 'West' ]
    KB = []

    "*** BEGIN YOUR CODE HERE ***"

    KB.append(PropSymbolExpr(pacman_str, x0, y0, time=0))   # pacman's initial condition
    
    for t in range(50):
        
        print(t)
        
        # pacman can only be at exactly one of the locations
        literals_position = []
        for x,y in non_wall_coords:
            literals_position.append(PropSymbolExpr(pacman_str, x, y, time=t))
        KB.append(exactlyOne(literals_position))

        # is there a satisfying model for what we know so far?
        # Goal: to be in position (xg, yg) at time t
        knowledge_check = conjoin(KB)
        model_t = findModel(conjoin([PropSymbolExpr(pacman_str, xg, yg, time=t), knowledge_check]))
        
        # if such model exists: return a coherent set of actions
        if model_t:
            return extractActionSequence(model_t, actions)
        
        # pacman can only perform one action per timestep t
        literals_action = []
        for action in DIRECTIONS:
            literals_action.append(PropSymbolExpr(action, time=t))
        KB.append(exactlyOne(literals_action))

        # transition model
        for x,y in non_wall_coords:
            KB.append(pacmanSuccessorAxiomSingle(x, y, t+1, walls_grid))
    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# QUESTION 5

def foodLogicPlan(problem) -> List:
    """
    Given an instance of a FoodPlanningProblem, return a list of actions that help Pacman
    eat all of the food.
    Available actions are ['North', 'East', 'South', 'West']
    Note that STOP is not an available action.
    Overview: add knowledge incrementally, and query for a model each timestep. Do NOT use pacphysicsAxioms.
    """
    walls_grid = problem.walls
    width, height = problem.getWidth(), problem.getHeight()
    walls_list = walls_grid.asList()
    (x0, y0), food = problem.start
    food = food.asList()

    # Get lists of possible locations (i.e. without walls) and possible actions
    all_coords = list(itertools.product(range(width + 2), range(height + 2)))

    non_wall_coords = [loc for loc in all_coords if loc not in walls_list]
    actions = [ 'North', 'South', 'East', 'West' ]

    KB = []

    "*** BEGIN YOUR CODE HERE ***"

    KB.append(PropSymbolExpr(pacman_str, x0, y0, time=0))   # pacman's initial condition
    
    for x,y in food:                                        # food's initial condition
        KB.append(PropSymbolExpr(food_str, x, y, time=0))   

    for t in range(50):
        
        print(t)
        
        # food initialization
        literals_food = []
        for x,y in food:
            literals_food.append(PropSymbolExpr(food_str, x, y, time=t))
        
        # pacman can only be at exactly one of the locations
        literals_position = []
        for x,y in non_wall_coords:
            literals_position.append(PropSymbolExpr(pacman_str, x, y, time=t))
        KB.append(exactlyOne(literals_position))

        knowledge_check = conjoin(KB)
        # "All food has been eaten" == True <=> all food positions are False;
        # To obtain a True statement from an all-False set of statements, create a disjunction of the statements and negate it
        # T == ~(F | F | ... | F)
        model_t = findModel(conjoin([~disjoin(literals_food), knowledge_check]))
        if model_t:
            return extractActionSequence(model_t, actions)
        
        # pacman can only perform one action per timestep t
        literals_action = []
        for action in DIRECTIONS:
            literals_action.append(PropSymbolExpr(action, time=t))
        KB.append(exactlyOne(literals_action))

        # transition model
        for x,y in non_wall_coords:
            KB.append(pacmanSuccessorAxiomSingle(x, y, t+1, walls_grid))

        for x,y in non_wall_coords:
        # given position (x,y):
        # food is not there at time t+1  <=>  the food wasn't there at time t  |  Pacman was already there at time t (so he already ate it)
            food_successor_axiom = ~PropSymbolExpr(food_str, x, y, time=t+1) % disjoin([~PropSymbolExpr(food_str, x, y, time=t), PropSymbolExpr(pacman_str, x, y, time=t)])
            KB.append(food_successor_axiom)
                    
    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# HELPER FUNCTIONS

def world_building(KB: List, type: bool, agent, t: int, all_coords: List[Tuple], non_outer_wall_coords: List[Tuple], walls_grid: List[List]):
    """
    Returns an updated KB with the necessary axioms, actions and percepts at time t
    type == 0: localization and mapping problem
    type == 1: SLAM problem.
    """
    KB.append(PropSymbolExpr(agent.actions[t], time=t))     # action taken by Pacman

    percepts = agent.getPercepts()
    
    if type == 0:
        # defining axioms and percepts for a localization and mapping problem
        KB.append(pacphysicsAxioms(t, all_coords, non_outer_wall_coords, walls_grid, sensorModel=sensorAxioms, successorAxioms=allLegalSuccessorAxioms))
        percept_rules = fourBitPerceptRules(t, percepts)
    
    else:
        # defining axioms and percepts for a SLAM problem
        KB.append(pacphysicsAxioms(t, all_coords, non_outer_wall_coords, walls_grid, sensorModel=SLAMSensorAxioms, successorAxioms=SLAMSuccessorAxioms))
        percept_rules = numAdjWallsPerceptRules(t, percepts)
    
    KB.append(percept_rules)

    return KB


def provable_locations(KB: List, t: int, non_outer_wall_coords: List[Tuple]):
    """
    Returns, at time t, an updated KB with proven Pacman positions and a list of possible Pacman locations
    """
    possible_locations = []

    for x,y in non_outer_wall_coords:
        
        # the whole KB must entail the statement that Pacman is (or isn't) at (x,y) for us to prove that
        # he is (or isn't) actually at (x,y)
        pacman_at_xy = entails(conjoin(KB), PropSymbolExpr(pacman_str, x, y, time=t))
        pacman_notat_xy = entails(conjoin(KB), ~PropSymbolExpr(pacman_str, x, y, time=t))

        # the possible locations for Pacman are those that have a satisfying model
        if findModel(conjoin([conjoin(KB), PropSymbolExpr(pacman_str, x, y, time=t)])):
            possible_locations.append((x,y))
        
        if pacman_at_xy is True:
            KB.append(PropSymbolExpr(pacman_str, x, y, time=t))    
        if pacman_notat_xy is True:
            KB.append(~PropSymbolExpr(pacman_str, x, y, time=t))

    return KB, possible_locations


def provable_walls(KB: List, known_map, non_outer_wall_coords: List[Tuple]):
    """
    Returns an updated KB with proven wall positions and an accordingly updated map
    """
    for x,y in non_outer_wall_coords:

        # the whole KB must entail the statement that the wall is (or isn't) at (x,y) for us to prove that
        # it is (or isn't) actually at (x,y)
        wall_at_xy = entails(conjoin(KB), PropSymbolExpr(wall_str, x, y))
        wall_notat_xy = entails(conjoin(KB), ~PropSymbolExpr(wall_str, x, y))

        if wall_at_xy is True:
            KB.append(PropSymbolExpr(wall_str, x, y))
            known_map[x][y] = 1     # 1 -> there's a wall at (x,y)
        if wall_notat_xy is True:
            KB.append(~PropSymbolExpr(wall_str, x, y))
            known_map[x][y] = 0     # 0 -> there isn't a wall at (x,y)
    
    return KB, known_map

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
    
    # walls positions initilization
    for x,y in walls_list:
        KB.append(PropSymbolExpr(wall_str, x, y))

    non_wall_coords = [loc for loc in all_coords if loc not in walls_list]
    for x,y in non_wall_coords:
        KB.append(~PropSymbolExpr(wall_str, x, y))


    for t in range(agent.num_timesteps):

        KB = world_building(KB, 0, agent, t, all_coords, non_outer_wall_coords, walls_grid)

        KB, possible_locations = provable_locations(KB, t, non_outer_wall_coords)
        
        agent.moveToNextState(agent.actions[t])

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

    KB.append(PropSymbolExpr(pacman_str, pac_x_0, pac_y_0, time=0))     # pacman's initial location
    
    # check if there's a wall at (x0, y0)
    wall_at_x0y0 = entails(conjoin(KB), PropSymbolExpr(wall_str, pac_x_0, pac_y_0))
    wall_notat_x0y0 = entails(conjoin(KB), ~PropSymbolExpr(wall_str, pac_x_0, pac_y_0))

    if wall_at_x0y0 is True:    # if I proved there's a wall at x0, y0, add that information to KB and map
        KB.append(PropSymbolExpr(wall_str, pac_x_0, pac_y_0))
        known_map[pac_x_0][pac_y_0] = 1
    
    if wall_notat_x0y0 is True:     # if I proved there isn't a wall at x0, y0, add that information to KB and map
        KB.append(~PropSymbolExpr(wall_str, pac_x_0, pac_y_0))
        known_map[pac_x_0][pac_y_0] = 0


    for t in range(agent.num_timesteps):

        KB = world_building(KB, 0, agent, t, all_coords, non_outer_wall_coords, walls_grid=problem.walls)

        KB, known_map = provable_walls(KB, known_map, non_outer_wall_coords)
        
        agent.moveToNextState(agent.actions[t])

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
    
    KB.append(PropSymbolExpr(pacman_str, pac_x_0, pac_y_0, time=0))     # pacman's initial location

    # check if there's a wall at (x0, y0)
    wall_at_x0y0 = entails(conjoin(KB), PropSymbolExpr(wall_str, pac_x_0, pac_y_0))
    wall_notat_x0y0 = entails(conjoin(KB), ~PropSymbolExpr(wall_str, pac_x_0, pac_y_0))

    if wall_at_x0y0 is True:    # if I proved there's a wall at x0, y0, add that information to KB and map
        KB.append(PropSymbolExpr(wall_str, pac_x_0, pac_y_0))
        known_map[pac_x_0][pac_y_0] = 1
    
    if wall_notat_x0y0 is True:     # if I proved there isn't a wall at x0, y0, add that information to KB and map
        KB.append(~PropSymbolExpr(wall_str, pac_x_0, pac_y_0))
        known_map[pac_x_0][pac_y_0] = 0


    for t in range(agent.num_timesteps):

        KB = world_building(KB, 1, agent, t, all_coords, non_outer_wall_coords, walls_grid=known_map)

        KB, known_map = provable_walls(KB, known_map, non_outer_wall_coords)

        KB, possible_locations = provable_locations(KB, t, non_outer_wall_coords)

        agent.moveToNextState(agent.actions[t])

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


