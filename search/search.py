# search.py
# ---------
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
In search.py, you will implement generic search algorithms which are called by
Pacman agents (in searchAgents.py).
"""

import util

class SearchProblem:
    """
    This class outlines the structure of a search problem, but doesn't implement
    any of the methods (in object-oriented terminology: an abstract class).

    You do not need to change anything in this class, ever.
    """

    def getStartState(self):
        """
        Returns the start state for the search problem.
        """
        util.raiseNotDefined()

    def isGoalState(self, state):
        """
          state: Search state

        Returns True if and only if the state is a valid goal state.
        """
        util.raiseNotDefined()

    def getSuccessors(self, state):
        """
          state: Search state

        For a given state, this should return a list of triples, (successor,
        action, stepCost), where 'successor' is a successor to the current
        state, 'action' is the action required to get there, and 'stepCost' is
        the incremental cost of expanding to that successor.
        """
        util.raiseNotDefined()

    def getCostOfActions(self, actions):
        """
         actions: A list of actions to take

        This method returns the total cost of a particular sequence of actions.
        The sequence must be composed of legal moves.
        """
        util.raiseNotDefined()


def tinyMazeSearch(problem):
    """
    Returns a sequence of moves that solves tinyMaze.  For any other maze, the
    sequence of moves will be incorrect, so only use this for tinyMaze.
    """
    from game import Directions
    s = Directions.SOUTH
    w = Directions.WEST
    return  [s, s, w, s, w, w, s, w]


# EXERCISE 1 --------------------------------------------------------------------------------------------------------------

def depthFirstSearch(problem):

    # since I'm taking an iterative approach, I'll be using a stack
    stack = util.Stack()
    visited_nodes = []
    path = []
    
    # root inizialization + check for trivial solution
    start = problem.getStartState()
    
    if problem.isGoalState(start):
        return []

    stack.push((start, []))

    # while the stack is not empty:
    while(stack.isEmpty() is False):

        # the top node is visited and popped out of the stack
        node, path = stack.pop()
        visited_nodes.append(node)

        if problem.isGoalState(node):
            return path
        
        # if the adjacent successors are not visited, they are pushed in the stack
        successors = problem.getSuccessors(node)

        for s in successors:
            if s[0] not in visited_nodes:   # s[0] is the next state
                new_path = path + [s[1]]    # s[1] is the action
                stack.push((s[0], new_path))       
        
    return path

# OUTPUTS:

# 1) python3 pacman.py -l mediumMaze -p SearchAgent
    # Total cost: 130, Search nodes expanded: 146, Score: 380

# 2) python3 pacman.py -l bigMaze -p SearchAgent
    # Total cost: 210, Search nodes expanded: 390, Score: 300


# EXERCISE 2 --------------------------------------------------------------------------------------------------------------

def breadthFirstSearch(problem):

    # bfs needs a queue instead of a stack
    queue = util.Queue()
    visited_nodes = []
    path = []

    # root inizialization + check for trivial solution
    start = problem.getStartState()

    if problem.isGoalState(start):
        return []

    queue.push((start, []))

    # while the queue is not empty:
    while(queue.isEmpty() is False):

        # the top node is visited and popped out of the queue
        node, path = queue.pop()
        visited_nodes.append(node)

        if problem.isGoalState(node):
            return path
        
        # if the adjacent successors are not visited, they are pushed in the queue
        successors = problem.getSuccessors(node)

        queue_items = queue.list    # nodes that are already in the queue
        
        for s in successors:
            if s[0] not in visited_nodes and s[0] not in (item[0] for item in queue_items):
                new_path = path + [s[1]]
                queue.push((s[0], new_path))
                
    return path

# OUTPUTS:

# 1) python3 pacman.py -l mediumMaze -p SearchAgent -a fn=bfs
    # Total cost: 68, Search nodes expanded: 269, Score: 442

# 2) python3 pacman.py -l bigMaze -p SearchAgent -a fn=bfs
    # Total cost: 210, Search nodes expanded: 620, Score: 300 


# EXERCISE 3 --------------------------------------------------------------------------------------------------------------

def uniformCostSearch(problem):

    # initialize the priority queue
    queue = util.PriorityQueue()
    visited_nodes = []
    path = []

    # root inizialization + check for trivial solution
    start = problem.getStartState()

    if problem.isGoalState(start):
        return path

    queue.push((start, []), 0)

    # while the priority queue is not empty:
    while(queue.isEmpty() is False):
        
        # the top node is visited and popped out of the queue
        node, path = queue.pop()
        visited_nodes.append(node)
        
        if problem.isGoalState(node):
            return path

        # if the adjacent successors are not visited, they are pushed in the queue with a specific order based on cost of action
        successors = problem.getSuccessors(node)
        
        queue_items = queue.heap

        for s in successors:
            new_path = path + [s[1]]
            
            if s[0] not in visited_nodes and s[0] not in (state[2][0] for state in queue_items):    
                priority = problem.getCostOfActions(new_path)
                queue.push((s[0], new_path), priority)

            elif s[0] not in visited_nodes and s[0] in (state[2][0] for state in queue_items):
                for item in queue_items:
                    if item[2][0] == s[0]:
                        prev_priority = problem.getCostOfActions(item[2][1])

                new_priority = problem.getCostOfActions(new_path)

                if prev_priority > new_priority:
                    queue.update((s[0], new_path), new_priority)
            
    return path

# OUTPUTS:

# 1) python3 pacman.py -l mediumMaze -p SearchAgent -a fn=ucs
    # Total cost: 68, Search nodes expanded: 269, Score: 442

# 2) python3 pacman.py -l mediumDottedMaze -p StayEastSearchAgent
    # Total cost: 1, Search nodes expanded: 186, Score: 646

# 3) python3 pacman.py -l mediumScaryMaze -p StayWestSearchAgent
    # Search nodes expanded: 108, Score: 418



def nullHeuristic(state, problem=None):
    """
    A heuristic function estimates the cost from the current state to the nearest
    goal in the provided SearchProblem.  This heuristic is trivial.
    """
    return 0


# EXERCISE 4 --------------------------------------------------------------------------------------------------------------

def aStarSearch(problem, heuristic=nullHeuristic):

    # initialize the priority queue
    queue = util.PriorityQueue()
    visited_nodes = []
    path = []

    # root inizialization + check for trivial solution
    start = problem.getStartState()

    if problem.isGoalState(start):
        return []

    queue.push((start, []), heuristic)

    # while the queue is not empty:
    while(queue.isEmpty() is False):
        node, path = queue.pop()
        
        # the top node is visited and popped out of the queue
        if node not in visited_nodes:
            visited_nodes.append(node)

            if problem.isGoalState(node):
                return path
            
            # if the adjacent successors are not visited, they are pushed in the queue with a specific order based on cost of action
            # and an estimation of the cost of the path from the successor node to the goal
            successors = problem.getSuccessors(node)
            
            for s in successors:
                if s[0] not in visited_nodes:
                    new_path = path + [s[1]]
                    queue.push((s[0], new_path), heuristic(s[0], problem) + problem.getCostOfActions(new_path))
                    
    return path

# OUTPUTS
   
# 1) python3 pacman.py -l bigMaze -z 0.5 -p SearchAgent -a fn=astar,heuristic=manhattanHeuristic
    # Total cost: 210, Search nodes expanded: 549, Score: 300


dfs = depthFirstSearch
bfs = breadthFirstSearch
ucs = uniformCostSearch
astar = aStarSearch


