import itertools
import z3
import numpy as np
import random
import copy
import time
import matplotlib.pyplot as plt


# Sudoku Class
class Sudoku:
    # Creating an empty matrix with None everywhere
    _grid = None
    # The solver
    _solver = None
    # Set of chars that is could be placed in a position
    # ***
    _valid_charset = set([int(x) for x in range(0, 10)])
    # Type of sudoku
    # ***
    _nums = [[0 for _ in range(9)] for _ in range(9)]
    _distinct = True
    _classic = True
    _no_num = True

    def __init__(self, sudoku_array, classic, distinct, no_num):
        # a 1-D sudoku_array
        self._solver = z3.Solver()
        self._classic = classic
        self._distinct = distinct
        self._no_num = no_num
        # Create variables
        if not no_num:
            self._grid = [[z3.Int('cell_%d_%d' % (r + 1, c + 1)) for c in range(9)] for r in range(9)]
            # self._grid = [[None for _ in range(9)] for _ in range(9)]
            for r in range(9):
                for c in range(9):
                    # This line is so cool. This line gives a 9*9 matrix with each position
                    # variable cell_i_j
                    v = z3.Int('cell_%d_%d' % (r + 1, c + 1))
                    self._grid[r][c] = v
        else:
            self._grid = [[[z3.Bool('cell_%d_%d_%d' % (r + 1, c + 1, num + 1)) for num in range(9)] for c in range(9)]
                          for r in range(9)]

        assert (len(sudoku_array) >= 81), "Invalid sudoku string provided! (length)"
        self.load_numbers(sudoku_array[:81])
        # Add constraints for classic sudoku
        self.load_constraints()


    def v(self,r,c):
        return int(self._nums[r][c])-1

    def load_numbers(self, sudoku_array):
        """
        assign each number in the matrix
        :param sudoku_array: np.matrix
        :return: None
        """
        for r in range(9):
            for c in range(9):
                x = sudoku_array[r * 9 + c]
                assert (x in self._valid_charset), "Invalid sudoku string provided! (invalid character \'{}\')".format(
                    x)
                # ***
                if x != 0:
                    self._nums[r][c] = int(x)
                    if self._no_num:
                        self._solver.add(self._grid[r][c][x])
                    else:
                        self._solver.add(self._grid[r][c] == int(x))

    def load_constraints(self):
        # Digits from 1-9
        if not self._no_num:
            for r in range(9):
                for c in range(9):
                    v = self._grid[r][c]
                    self._solver.add(v >= 1)
                    self._solver.add(v <= 9)

            # Distinct digits in row/column
            for i in range(9):
                if self._distinct:
                    self._solver.add(z3.Distinct(self._grid[i]))  # Row
                    self._solver.add(z3.Distinct([self._grid[r][i] for r in range(9)]))  # Column
                else:
                    self._solver.add(
                        z3.And([z3.PbEq([(self._grid[i][j] == k, 1) for j in range(9)], 1) for k in range(1, 10)]))  # Row
                    self._solver.add(
                        z3.And([z3.PbEq([(self._grid[j][i] == k, 1) for j in range(9)], 1) for k in range(1, 10)]))
                    # Distinct digits in boxes
            offset = list(itertools.product(range(0, 3), range(0, 3)))
            for r in range(0, 9, 3):
                for c in range(0, 9, 3):
                    box = [self._grid[r + dy][c + dx] for dy, dx in offset]
                    self._solver.add(z3.Distinct(box))
        else:
            pass
            # TODO implement distinct for no_num
        # Assert major diagonal distinct
        # Major diagonal 1
        self._solver.add(z3.Distinct([self._grid[r][r + 4] for r in range(4)]))
        # Major diagonal 2
        self._solver.add(z3.Distinct([self._grid[r][r + 1] for r in range(8)]))
        # Major diagonal 3
        self._solver.add(z3.Distinct([self._grid[r + 1][r] for r in range(8)]))
        # Major diagonal 4
        self._solver.add(z3.Distinct([self._grid[r + 4][r] for r in range(4)]))
        # # Assert minor diagonal distinct
        # Minor diagonal 1
        self._solver.add(z3.Distinct([self._grid[r][-r - 5] for r in range(4)]))
        # Minor diagonal 2
        self._solver.add(z3.Distinct([self._grid[r][-r - 2] for r in range(8)]))
        # Minor diagonal 3
        self._solver.add(z3.Distinct([self._grid[r + 1][-r - 1] for r in range(8)]))
        # Minor diagonal 4
        self._solver.add(z3.Distinct([self._grid[r + 4][-r - 1] for r in range(4)]))
        # Assert minor diagonal distinct

    def solve(self):
        if self._solver.check() == z3.sat:
            m = self._solver.model()
            for r in range(9):
                for c in range(9):
                    self._nums[r][c] = m.evaluate(self._grid[r][c])
            # solved_puzzle.append(self._nums)
            return True
        else:
            return False


# function for solving puzzle param: classic, distinct, per_col
def solving_sudoku(classic: bool, distinct: bool, per_col: bool, no_num: bool):
    '''
    Solve a full sudoku

    :param no_num:
    :param classic:
    :param distinct:
    :param per_col:
    :return: 2D list of solved suodoku
    '''
    if not no_num:
        # variable cell_i_j
        _grid = [[z3.Int('cell_%d_%d' % (r + 1, c + 1)) for r in range(9)] for c in range(9)]
    else:
        # variable cell_i_j_num
        _grid = [[[z3.Bool('cell_%d_%d_%d' % (r + 1, c + 1, num+1)) for num in range(9)] for c in range(9)] for r in range(9)]
    # The solver
    _solver = z3.Solver()
    # Empty grid
    _nums = [['.' for _ in range(9)] for _ in range(9)]

    # build restrictions
    if not no_num:
        for r in range(9):
            for c in range(9):
                v = _grid[r][c]
                _solver.add(v >= 1)
                _solver.add(v <= 9)
        # *** Check
        if distinct:
            _solver.add(z3.And([z3.Distinct([_grid[r][c] for r in range(9)]) for c in range(9)]))  # Cols distinct
            _solver.add(z3.And([z3.Distinct(_grid[i]) for i in range(9)]))  # Rows distinct
        else:
            _solver.add(z3.And([z3.And([z3.PbEq([(_grid[i][j] == k, 1) for j in range(9)], 1) for k in range(1, 10)]) for i in range(9)]))  # Row
            _solver.add(z3.And([z3.And([z3.PbEq([(_grid[j][i] == k, 1) for j in range(9)], 1) for k in range(1, 10)]) for i in range(9)]))
            # Distinct digits in boxes
    else:
        # How to add distinct??
        _solver.add(z3.And([z3.PbEq([(_grid[i][j][k] == True, 1) for k in range(9)], 1) for i in range(9) for j in range(9)]))  # one of 1-9 per cell
        _solver.add(z3.And([z3.PbEq([(_grid[k][j][i] == True, 1) for k in range(9)], 1) for i in range(9) for j in range(9)]))  # Col distinct
        _solver.add(z3.And([z3.PbEq([(_grid[j][k][i] == True, 1) for k in range(9)], 1) for i in range(9) for j in range(9)]))  # Row distinct

        # 3D grid with _grid[r][c][num1-9]

    offset = list(itertools.product(range(0, 3), range(0, 3)))
    for r in range(0, 9, 3):
        for c in range(0, 9, 3):
            box = [_grid[r + dy][c + dx] for dy, dx in offset]
            _solver.add(z3.Distinct(box))
    # Assert major diagonal distinct
    if not classic:
        # Major diagonal 1
        _solver.add(z3.Distinct([_grid[r][r + 4] for r in range(4)]))
        # Major diagonal 2
        _solver.add(z3.Distinct([_grid[r][r + 1] for r in range(8)]))
        # Major diagonal 3
        _solver.add(z3.Distinct([_grid[r + 1][r] for r in range(8)]))
        # Major diagonal 4
        _solver.add(z3.Distinct([_grid[r + 4][r] for r in range(4)]))
        # # Assert minor diagonal distinct
        # Minor diagonal 1
        _solver.add(z3.Distinct([_grid[r][-r - 5] for r in range(4)]))
        # Minor diagonal 2
        _solver.add(z3.Distinct([_grid[r][-r - 2] for r in range(8)]))
        # Minor diagonal 3
        _solver.add(z3.Distinct([_grid[r + 1][-r - 1] for r in range(8)]))
        # Minor diagonal 4
        _solver.add(z3.Distinct([_grid[r + 4][-r - 1] for r in range(4)]))
    # Assert minor diagonal distinct
    if _solver.check() == z3.sat:
        # Start by filling the first index
        if not no_num:
            if per_col:
                for i in range(9):
                    for j in range(9):
                        x = [k for k in range(1, 10)]
                        random.shuffle(x)
                        tryVal = x.pop()
                        while _solver.check(_grid[i][j] == int(tryVal)) != z3.sat:
                            if len(x) == 0:
                                print('Tried all values, no luck')
                                return None
                            tryVal = x.pop()
                        _nums[i][j] = int(tryVal)
                        _solver.add(_grid[i][j] == tryVal)
                print("Already solved and appended to the list")
                return _nums

            else:
                # Start by filling the number 1,2,3...9
                for num in range(1, 10):
                    if num == 9:
                        for r in range(9):
                            for c in range(9):
                                if _nums[r][c] == '.':
                                    _nums[r][c] = int(num)
                                    _solver.add(_grid[r][c] == num)
                    cols = [i for i in range(9)]
                    for r in range(9):
                        for c in cols:
                            if _nums[r][c] == '.':
                                z3r = _solver.check(_grid[r][c] == int(num))
                                if z3r == z3.sat:
                                    _nums[r][c] = int(num)
                                    _solver.add(_grid[r][c] == num)
                                    cols.remove(c)
                                    break
                                else:
                                    if z3r != z3.unsat:
                                        raise "Z3 error"
                print("Already solved and appended to the list")
                return _nums
        # no_num
        else:
            if per_col:
                for i in range(9):
                    for j in range(9):
                        x = [k for k in range(9)]
                        random.shuffle(x)
                        tryVal = x.pop()
                        while _solver.check(_grid[i][j][tryVal]) != z3.sat:
                            if len(x) == 0:
                                print('Tried all values, no luck')
                                return None
                            tryVal = x.pop()
                        _nums[i][j] = int(tryVal)
                        _solver.add(_grid[i][j][tryVal])
                print("Already solved and appended to the list")
                return _nums

            else:
                # Start by filling the number 1,2,3...9
                for num in range(9):
                    if num == 9:
                        for r in range(9):
                            for c in range(9):
                                if _nums[r][c] == '.':
                                    _nums[r][c] = int(num)+1
                                    _solver.add(_grid[r][c][num])
                    cols = range(9)
                    for r in range(9):
                        for c in cols:
                            if _nums[r][c] == '.':
                                z3r = _solver.check(_grid[r][c][num])
                                if z3r == z3.sat:
                                    _nums[r][c] = int(num)+1
                                    _solver.add(_grid[r][c][num])
                                    cols.remove(c)
                                    break
                                else:
                                    if z3r != z3.unsat:
                                        raise "Z3 error"
                print("Already solved and appended to the list")

    else:
        print('Error in one of the constraints')
        return None


# function for generating puzzle param: classic
# Check if the puzzle is still solveable
def check_puzzle_solvable(lst, classic: bool, distinct: bool, no_num: bool):
    s = Sudoku(lst.reshape(-1), classic, distinct,no_num)
    return s.solve()


def generate_puzzle(solved_sudokus, classic: bool, distinct: bool, no_num: bool):
    '''
    Generates puzzle with holes
    :param solved_sudokus: MUST BE a 3D list
    :param classic:
    :param distinct:
    :return: a list of time required for generating each puzzle
    '''
    time_rec = []
    for puzzle in solved_sudokus:
        st = time.time()
        for i in range(9):
            for j in range(9):
                poss_num = [x for x in range(1, 10)]
                curr_num = puzzle[i][j]
                poss_num.remove(curr_num)
                # try every number except the current one
                replace = True
                for ele in poss_num:
                    puzzle[i][j] = ele
                    if check_puzzle_solvable(puzzle, classic, distinct,no_num):
                        replace = False
                        break
                if replace:
                    puzzle[i][j] = 0
        et = time.time()
        time_rec.append(et - st)
        print('Successfully generated one puzzle')
    return time_rec


# *** Add is_num
def gen_solve_sudoku(classic: bool, distinct: bool, per_col: bool, no_num: bool, num_iter: int):
    '''
    Creates a solved sudoku, then generate a sudoku puzzle. returns time for each

    :param no_num:
    :param classic:
    :param distinct:
    :param per_col:
    :param num_iter:
    :return: (gen_time,solve_time) 1D lists of time
    '''
    ret_solv_time = []
    store_solved_sudoku = []
    for i in range(num_iter):
        st = time.time()
        ret = solving_sudoku(classic, distinct, per_col, no_num)
        et = time.time()
        store_solved_sudoku.append(ret)
        ret_solv_time.append(et - st)

    store_holes = copy.deepcopy(store_solved_sudoku)
    store_holes = np.array(store_holes)
    ret_holes_time = generate_puzzle(store_holes, classic, distinct,no_num)
    return ret_solv_time, ret_holes_time
# Record time to generate solved sudokus and sudokus with holes.
# Record time to generate solved argyle sudokus and sudokus with holes.

# argyle_solved_time

# per_col only required when generating


# Loop and saving:

# # Creating list a possible combinations
# a = [[bool1,bool2] for bool1 in (True, False) for bool2 in (True, False)]
# print(a)
# # creating paths for it
# for ele in a:j
#     bol1, bol2 = ("First True" if ele[0] else "First False",
#                   "Second True" if ele[1] else "Second False")
#     print(bol1 + "and" + bol2)
