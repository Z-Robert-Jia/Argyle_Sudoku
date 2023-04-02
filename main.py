import itertools
import z3  # if this fails, run 'python -m pip install z3-solver'
import numpy as np
import random
import copy
import time
import matplotlib.pyplot as plt
from typing import List


# Sudoku Class
class Sudoku:
    # Creating an empty matrix with None everywhere
    _grid = None
    # The solver
    _solver = None
    # Set of chars that is could be placed in a position
    _valid_charset = set([int(x) for x in range(0, 10)])
    # Type of sudoku
    _distinct = True
    _classic = True
    _no_num = True
    _per_col = True
    _log_path = None

    def __init__(self, sudoku_array: List[int], classic: bool, distinct: bool, per_col: bool, no_num: bool, log_path=""):
        """
        Only write a logFile when a path is provided
        Type hint for List[int] might not work
        :param sudoku_array:
        :param classic:
        :param distinct:
        :param per_col:
        :param no_num:
        :param log_path:
        """
        # a 1-D sudoku_array
        self._solver = z3.Solver()
        self._solver.set("timeout", 500000)
        # self._solver.from_file("fileName")
        self._classic = classic
        self._distinct = distinct
        self._no_num = no_num
        self._per_col = per_col
        self._nums = [[0 for _ in range(9)] for _ in range(9)]
        self._log_path = log_path


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

        assert (len(sudoku_array) == 81), "Invalid sudoku string provided! (length)"
        self.load_numbers(sudoku_array[:81])

        # Add constraints for classic sudoku

    def v(self, r, c):
        return int(self._nums[r][c]) - 1

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
                if x != 0:
                    self._nums[r][c] = int(x)

    def load_constraints(self):
        # *** Remove
        print("Entered load_constraints")
        # Every digit
        digits = [self._grid[r][c] for c in range(9) for r in range(9)]
        # row1-9
        rows = [self._grid[r] for r in range(9)]
        # col1-9
        cols = [[self._grid[r][c] for r in range(9)] for c in range(9)]
        # box 1st-9th
        offset = list(itertools.product(range(0, 3), range(0, 3)))
        boxes = []
        # Load existing numbers
        for r in range(9):
            for c in range(9):
                if self._nums[r][c] != 0:
                    if self._no_num:
                        self._solver.add(self._grid[r][c][self._nums[r][c] - 1])
                    else:
                        self._solver.add(self._grid[r][c] == int(self._nums[r][c]))

        for r in range(0, 9, 3):
            for c in range(0, 9, 3):
                boxes.append([self._grid[r + dy][c + dx] for dy, dx in offset])

        if self._no_num:
            # pbeq ONLY, no_num 3D grid
            self._solver.add(z3.And([z3.PbEq([(self._grid[i][j][k], 1) for k in range(9)], 1) for i in range(9) for j in
                                     range(9)]))  # digit
            self._solver.add(z3.And([z3.PbEq([(self._grid[k][i][j], 1) for k in range(9)], 1) for i in range(9) for j in
                                     range(9)]))  # Col distinct
            self._solver.add(z3.And([z3.PbEq([(self._grid[j][k][i], 1) for k in range(9)], 1) for i in range(9) for j in
                                     range(9)]))  # Row distinct
            self._solver.add(
                z3.And([z3.PbEq([(box[k][j], 1) for k in range(9)], 1) for j in range(9) for box in boxes]))  # box
        else:  # numbers  2D grid
            # Restrict digits in between 1-9
            for digit in digits:
                self._solver.add(z3.And(digit >= 1, digit <= 9))  # Digit
            if self._distinct:  # distinct, numbers 2D grid
                self._solver.add(z3.And([z3.Distinct(row) for row in rows]))  # rows
                self._solver.add(z3.And([z3.Distinct(col) for col in cols]))  # cols
                self._solver.add(z3.And([z3.Distinct(box) for box in boxes]))  # box

            else:  # pbeq, numbers, 2D grid
                for row in rows:
                    self._solver.add(z3.And([z3.PbEq([(row[i] == k, 1) for i in range(9)], 1) for k in range(1, 10)]))
                for col in cols:
                    self._solver.add(z3.And([z3.PbEq([(col[i] == k, 1) for i in range(9)], 1) for k in range(1, 10)]))
                for box in boxes:
                    self._solver.add(z3.And([z3.PbEq([(box[i] == k, 1) for i in range(9)], 1) for k in range(1, 10)]))

        # Argyle-----
        if not self._classic:
            argile_hints = [[self._grid[r][r + 4] for r in range(4)]  # Major diagonal 1
                , [self._grid[r][r + 1] for r in range(8)]  # ??
                , [self._grid[r + 1][r] for r in range(8)]
                , [self._grid[r + 4][r] for r in range(4)]
                , [self._grid[r][-r - 5] for r in range(4)]
                , [self._grid[r][-r - 2] for r in range(8)]
                , [self._grid[r + 1][-r - 1] for r in range(8)]
                , [self._grid[r + 4][-r - 1] for r in range(4)]
                            ]
            if self._no_num:
                self._solver.add(
                    z3.And([z3.PbLe([(digit[k], 1) for k in range(9)], 1) for arg in argile_hints for digit in arg]))
                pass
            else:
                if self._distinct:
                    self._solver.add(z3.And([z3.Distinct(arg) for arg in argile_hints]))
                else:
                    self._solver.add(z3.And(
                        [z3.PbLe([(digit == k, 1) for k in range(9)], 1) for arg in argile_hints for digit in arg]))

    def solve(self):
        self.load_constraints()
        z3_check = self.solver.check()

        if z3_check == z3.sat:
            # m = self._solver.model()
            # for r in range(9):
            #     for c in range(9):
            #         self._nums[r][c] = m.evaluate(self._grid[r][c])
            return True
        else:
            return False

    def removable(self, i, j, test_num):
        '''
        Now testing one index by one index. How to use push and pop
        to test to whole grid without reloading constraints
        Test if test_num is unique and could be removed
        --Replacement: check_puzzle_solvable function

        :param test_num: 1-9
        :return: a boolean indicating if test_num could be removed
        '''
        self._nums[i][j] = 0
        self.load_constraints()
        removable = True
        # x = [i for i in range(1,10)]
        # x.pop(test_num-1)
        if self._no_num:
            if self._solver.check(self._grid[i][j][test_num - 1] == False) == z3.sat:
                removable = False
        else:
            if self._solver.check(self._grid[i][j] != int(test_num)) == z3.sat:
                removable = False
        return removable

    def gen_solved_sudoku(self):
        '''
        produce a solved FULL sudoku
        --Replacement: solving_sudoku function

        :return: 2D list of a solved sudoku
        '''
        # ****
        self.load_constraints()
        print("Finished loading constraints")
        if self._solver.check() == z3.sat:
            if self._per_col:
                # Fill by index
                for i in range(9):
                    print(f"Filling row {i}")
                    for j in range(9):
                        x = [k for k in range(1, 10)]
                        random.shuffle(x)
                        tryVal = x.pop()
                        if self._no_num:
                            check_condition = lambda tryVal: self._solver.check(self._grid[i][j][tryVal - 1]) != z3.sat
                        else:
                            check_condition = lambda tryVal: self._solver.check(
                                self._grid[i][j] == int(tryVal)) != z3.sat

                        while check_condition(tryVal):
                            if check_condition(tryVal) == z3.unknown:
                                if self._log_path:
                                    self.write_to_file(self._log_path)
                                else:
                                    print("TimeOut and a logPath is not provided")
                                raise f'TimeOut while solving the row {i} col{j}'
                            if len(x) == 0:
                                raise 'Tried all values, no luck, check gen_solved_sudoku'
                            tryVal = x.pop()

                        self._nums[i][j] = int(tryVal)
                        if self._no_num:
                            self._solver.add(self._grid[i][j][tryVal - 1])
                        else:
                            self._solver.add(self._grid[i][j] == tryVal)

                    print(f'Finished with the row {i} col{j}')
            else:  # not per_col
                # Start by filling the number 1,2,3...9
                for num in range(1, 10):
                    print(f'Filling number {num}')
                    if num == 9:
                        for r in range(9):
                            for c in range(9):
                                if self._nums[r][c] == 0:
                                    self._nums[r][c] = int(num)
                                    if self._no_num:
                                        self._solver.add(self._grid[r][c][num - 1])
                                    else:
                                        self._solver.add(self._grid[r][c] == int(num))
                    else:
                        cols = [i for i in range(9)]
                        for r in range(9):
                            random.shuffle(cols)
                            for c in cols:
                                if self._nums[r][c] == 0:
                                    if self._no_num:
                                        condition = self._grid[r][c][num - 1]
                                    else:
                                        condition = self._grid[r][c] == int(num)
                                    z3r = self._solver.check(condition)
                                    if z3r == z3.sat:
                                        self._nums[r][c] = int(num)
                                        self._solver.add(condition)
                                        cols.remove(c)
                                        break
                                    else:
                                        if z3r == z3.unknown:
                                            if self._log_path:
                                                self.write_to_file(self._log_path)
                                            else:
                                                print("TimeOut and a logPath is not provided")
                                            raise f'TimeOut while filling the number {num}'
                                elif self._nums[r][c] == num:
                                    cols.remove(c)


            print("Generated a solved sudoku")
            print(self._nums)
            return self._nums
        elif self._solver.check() == z3.unknown:
            if self._log_path:
                self.write_to_file(self._log_path)
            else:
                 print("TimeOut and a logPath is not provided")
            raise 'TimeOut while loading constraints'
        else:
            # @sj this error message last time was written by me =-=
            raise 'Error from gen_solved_sudoku function in "load_constraints"'

    def write_to_file(self,file_path: str = "logFile") -> None:
        """
        CHANGE file_path
        :param file_path:
        :return:
        """
        print(self._nums)
        with open(self._log_path, 'w') as f:
            s = ''.join(str(ele) for rows in self._nums for ele in rows)
            f.write(s)

    def read_from_file(self,file_path="logFile") -> str:
        with open('file_path', 'r') as f:
            s = f.read()
        return s


def generate_puzzle(solved_sudokus, classic: bool, distinct: bool, per_col: bool, no_num: bool):
    '''
    Generates puzzle with holes

    :param solved_sudokus: MUST BE a 3D list
    :param classic:
    :param distinct:
    :return: a list of time required for generating each puzzle
    '''
    time_rec = []
    for puzzle in solved_sudokus:
        # **** REMOVE
        print(f'Solving puzzle: ')
        print(puzzle)
        st = time.time()
        for i in range(9):
            for j in range(9):
                s = Sudoku(puzzle.reshape(-1), classic, distinct, per_col, no_num)
                if s.removable(i, j, puzzle[i][j]):
                    puzzle[i][j] = 0
        et = time.time()
        time_rec.append(et - st)
        print('Successfully generated one puzzle')
        # **** REMOVE
        print(puzzle)
    # **** REMOVE
    np.save('sudoku_puzzle', solved_sudokus)
    return time_rec


def gen_solve_sudoku(classic: bool, distinct: bool, per_col: bool, no_num: bool, num_iter: int, log_path="logFile"):
    '''
    First creates a solved sudoku, then generate a sudoku puzzle. returns time for each

    :param classic:
    :param distinct:
    :param per_col:
    :param no_num:
    :param num_iter:
    :return: (solve_time, gen_time) 1D lists of time
    '''
    ret_solv_time = []
    store_solved_sudoku = []
    for i in range(num_iter):
        empty_list = [0 for i in range(9) for j in range(9)]
        st = time.time()
        s = Sudoku(empty_list, classic, distinct, per_col, no_num)
        ret = s.gen_solved_sudoku()
        et = time.time()
        store_solved_sudoku.append(ret)
        ret_solv_time.append(et - st)
    np.save('solved_sudoku', store_solved_sudoku)
    store_holes = copy.deepcopy(store_solved_sudoku)
    store_holes = np.array(store_holes)
    print("Start generating puzzles")
    ret_holes_time = generate_puzzle(store_holes, classic, distinct, per_col, no_num)
    return ret_solv_time, ret_holes_time


def fake_gen_solve_sudoku(classic: bool, distinct: bool, per_col: bool, no_num: bool, num_iter: int):
    # DO NOT USE THIS. JUST FOR TESTING
    conditions = (classic, distinct, per_col, no_num, num_iter)
    fake_time = np.array([1.12312, 2.12312])
    return (conditions, fake_time)

def generate_hard_sudokus(classic: bool, distinct: bool, per_col: bool, no_num: bool, log_path="logFile"):
    # Hard way
    empty_list = [0 for i in range(9) for j in range(9)]
    try:
        # @sj Not sure if this try-except always work!
        s = Sudoku(empty_list, classic, distinct, per_col, no_num, log_path=log_path)
        # log the hard instance to log_path
        ret = s.gen_solved_sudoku()
    except:
        print("TimeOut, attempting to continue to solve it with faster method")
    # Easy way
    with open(log_path, 'r') as f:
        half_solved_str = f.read()
    half_solved_list = list(map(int,list(half_solved_str)))
    st = time.time()
    s2 = Sudoku(half_solved_list, classic, False, per_col, True)
    s2.gen_solved_sudoku()
    et = time.time()
    print(f'Time taken for the fast way: {et-st}')


if __name__ == "__main__":
    # Test classic case
    # classic, distinct, per_col, no_num

    # print(gen_solve_sudoku(False, True, False, False, 2))

    generate_hard_sudokus(False, True, False, False,log_path="testLog.txt")

    # store_holes = np.load('solved_sudoku.npy')
    # ret_holes_time = generate_puzzle(store_holes, True, True, False, False)
    print("Process finished")
