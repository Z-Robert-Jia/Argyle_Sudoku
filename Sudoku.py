import itertools
import os.path

import z3  # if this fails, run 'python -m pip install z3-solver'
import numpy as np
import random
from copy import deepcopy
import time
import matplotlib.pyplot as plt
from typing import List
from pathlib import Path


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
    hard_smt_logPath = None
    hard_sudoku_logPath = None
    _prefill = False

    def __init__(self, sudoku_array: List[int], classic: bool, distinct: bool, per_col: bool, no_num: bool,
                 prefill: bool, hard_smt_logPath="", hard_sudoku_logPath="",print_progress=False):
        """
        Only write a logFile when a path is provided
        Type hint for List[int] might not work
        :param sudoku_array:
        :param classic:
        :param distinct:
        :param per_col:
        :param no_num:
        :param hard_smt_logPath:
        """
        # a 1-D sudoku_array
        self._solver = z3.Solver()
        self._timeout = 5000
        self._incTimeOut = self._timeout
        self._solver.set("timeout", self._timeout)
        # self._solver.from_file("fileName")
        self._classic = classic
        self._distinct = distinct
        self._no_num = no_num
        self._per_col = per_col
        self._nums = [[0 for _ in range(9)] for _ in range(9)]
        self.hard_smt_logPath = hard_smt_logPath
        self.hard_sudoku_logPath = hard_sudoku_logPath
        self._prefill = prefill
        self._penalty = 0
        self.condition_tpl = (self._classic,self._distinct,self._per_col,self._no_num,self._prefill)
        self._print_progress = print_progress

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
        # print("Entered load_constraints")
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
            [self._solver.add(z3.PbEq([(self._grid[i][j][k], 1) for k in range(9)], 1))
             for i in range(9) for j in range(9)]  # digit
            [self._solver.add(z3.PbEq([(self._grid[k][i][j], 1) for k in range(9)], 1))
             for i in range(9) for j in range(9)]  # Col distinct
            [self._solver.add(z3.PbEq([(self._grid[j][k][i], 1) for k in range(9)], 1))
             for i in range(9) for j in range(9)]  # Row distinct
            [self._solver.add(z3.PbEq([(box[k][j], 1) for k in range(9)], 1))
             for j in range(9) for box in boxes]  # box
        else:  # numbers  2D grid
            # Restrict digits in between 1-9
            for digit in digits:
                self._solver.add(digit >= 1)
                self._solver.add(digit <= 9)  # Digit
            if self._distinct:  # distinct, numbers 2D grid
                [self._solver.add(z3.Distinct(row)) for row in rows]  # rows
                [self._solver.add(z3.Distinct(row)) for row in cols]  # cols
                [self._solver.add(z3.Distinct(row)) for row in boxes]  # boxes
            else:  # pbeq, numbers, 2D grid
                [self._solver.add(z3.PbEq([(row[i] == k, 1) for i in range(9)], 1))
                 for k in range(1, 10) for row in rows]
                [self._solver.add(z3.PbEq([(row[i] == k, 1) for i in range(9)], 1))
                 for k in range(1, 10) for row in cols]
                [self._solver.add(z3.PbEq([(row[i] == k, 1) for i in range(9)], 1))
                 for k in range(1, 10) for row in boxes]
        # Argyle-----
        if not self._classic:
            argyle_hints = [[self._grid[r][r + 4] for r in range(4)]  # Major diagonal 1
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
                    z3.And([z3.PbLe([(digit[k], 1) for digit in arg], 1) for arg in argyle_hints for k in range(9)]))
                pass
            else:
                if self._distinct:
                    self._solver.add(z3.And([z3.Distinct(arg) for arg in argyle_hints]))
                else:
                    self._solver.add(z3.And(
                        [z3.PbLe([(digit == k, 1) for digit in arg], 1) for arg in argyle_hints for k in range(9)]))

    def solve(self):
        self.load_constraints()
        z3_check = self._solver.check()

        if z3_check == z3.sat:
            # m = self._solver.model()
            # for r in range(9):
            #     for c in range(9):
            #         self._nums[r][c] = m.evaluate(self._grid[r][c])
            return True
        else:
            return False

    def removable(self, i, j, test_num) -> (bool, int):
        '''
        Now testing one index by one index. How to use push and pop
        to test to whole grid without reloading constraints
        Test if test_num is unique and could be removed
        --Replacement: check_puzzle_solvable function

        :param test_num: 1-9
        :return: (removable: bool, penalty: int)
        '''
        self._nums[i][j] = 0
        self.load_constraints()
        # x = [i for i in range(1,10)]
        # x.pop(test_num-1)
        condition = self.check_not_removable(i, j, test_num)
        if condition == z3.sat:
            return False, 0
        elif condition == z3.unknown:
            # Try solving with faster method
            condition = self.new_solver().check_not_removable(i, j, test_num)
            if condition == z3.unknown:
                raise f"Timeout happened twice when checking if {i} {j} {test_num} is removable"
            else:
                if self._print_progress:
                    print(f'unsolvable problem checking removable was {condition} for ({i},{j}) is {test_num}')
                self.write_to_smt_and_sudoku_file((i,j),test_num,condition)
                return condition != z3.sat, 1
        return True, 0

    def new_solver(self):
        """
        Try checking index[i][j] == Tryval with alternative approach
        :param i:
        :param j:
        :param tryVal:
        :return:
        """
        # @sj **** Might need to change this
        s_new = Sudoku([c for r in self._nums for c in r], self._classic, False,
                       self._per_col, not self._no_num, self._prefill)
        s_new._timeout = 0
        s_new._solver.set("timeout", 0)
        s_new.load_constraints()
        self._penalty += 1
        return s_new

    def check_condition(self, i, j, tryVal):
        start = time.time()
        res = self._solver.check(self._grid[i][j][tryVal - 1] if self._no_num else self._grid[i][j] == int(tryVal))
        end = time.time()
        if self._timeout == 0: return res
        if end - start < (self._timeout - 100) / 1000 and res == z3.unknown:
            raise 'Probably somebody hit ctrl-c, aborting'
        elif self._print_progress and end - start > self._timeout / 10000 and res != z3.unknown:
            print('One check took more than 10% of timeout, but completed')
        return res

    def check_not_removable(self, i, j, tryVal):
        res = self._solver.check(
            self._grid[i][j][tryVal - 1] == False if self._no_num else self._grid[i][j] != int(tryVal))
        return res

    def add_constaint(self,i, j, tryVal):
        self._nums[i][j] = int(tryVal)
        if self._no_num:
            self._solver.add(self._grid[i][j][tryVal - 1])
        else:
            self._solver.add(self._grid[i][j] == tryVal)

    def gen_solved_sudoku(self):
        '''
        produce a solved FULL sudoku
        --Replacement: solving_sudoku function

        :return: 2D list of a solved sudoku
        '''
        # ****
        self.load_constraints()
        # if self._solver.check() == z3.sat:
        if self._per_col:
            # Fill by index
            for i in range(9):
                # print(f"Filling row {i}")
                if i == 0 and self._prefill:
                    testlst = [k for k in range(1, 10)]
                    random.shuffle(testlst)
                for j in range(9):
                    if self._nums[i][j] != 0:
                        continue
                    if i == 0 and self._prefill:
                        tryVal = testlst.pop()
                        check = z3.sat
                    else:
                        x = [k for k in range(1, 10)]
                        random.shuffle(x)
                        tryVal = x.pop()
                        check = self.check_condition(i, j, tryVal)
                    while check != z3.sat:
                        if check == z3.unknown:

                            # raise f'TimeOut while solving the row {i} col{j}'
                            # *** Might need to change this part when solving sudokus
                            s_new = self.new_solver()
                            check = s_new.check_condition(i, j, tryVal)

                            # Record to log path
                            if self.hard_smt_logPath:
                                self.write_to_smt_and_sudoku_file((i,j),tryVal,check)
                            else:
                                print("TimeOut and a logPath is not provided")

                            if check == z3.unknown:
                                raise 'Timeout happened twice, don\'t know how to continue!'
                            elif self._print_progress:
                                print(f'unsolvable problem was {check} for ({i},{j}) is {tryVal}')
                        else:  # check == z3.unsat
                            assert (check == z3.unsat)
                            if len(x) == 0:
                                print(f'check: {check} {i},{j},{tryVal}')
                                print(f'Current row: {self._nums}')
                                raise 'Tried all values, no luck, check gen_solved_sudoku'
                            tryVal = x.pop()
                            check = self.check_condition(i, j, tryVal)
                    self._nums[i][j] = int(tryVal)
                    if self._no_num:
                        self._solver.add(self._grid[i][j][tryVal - 1])
                    else:
                        self._solver.add(self._grid[i][j] == tryVal)

                if self._print_progress:
                    print(f'Finished with row {i} and filled \n {self._nums[i]}')
        else:  # not per_col
            # Start by filling the number 1,2,3...9
            for num in range(1, 10):
                if self._print_progress:
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
                                # z3r = self.check_condition(r,c,num)
                                condition = self.check_condition(r, c, num)
                                if condition == z3.sat:
                                    self.add_constaint(r,c,num)
                                    break
                                else:
                                    if condition == z3.unknown:
                                        s_new = self.new_solver()
                                        check = s_new.check_condition(r, c, num)

                                        if self.hard_smt_logPath:
                                            self.write_to_smt_and_sudoku_file((r, c), num, check)
                                        else:
                                            print("TimeOut and a logPath is not provided")

                                        if check == z3.unknown:
                                            raise 'Timeout happened twice, don\'t know how to continue!'
                                        elif self._print_progress:
                                            print(f'unsolvable problem was {check} for ({r},{c}) is {num}')
                                        if check == z3.sat:
                                            self.add_constaint(r,c,num)
                                            # self._solver.add(condition)
                                            cols.remove(c)
                                            break

                                        # raise f'TimeOut while filling the number {num}'
                                        # s_new = Sudoku([c for r in self._nums for c in r], self._classic,
                                        #                self._distinct,
                                        #                self._per_col, not self._no_num)
                                        # res = s_new.check_condition(r, c, num)
                                        # if res != z3.unknown:
                                        #     s_new.gen_solved_sudoku()
                                        #     tryVal = s_new._nums[i][j]
                                        #     print(f'Filled row {i} col {j} with alternative appraoch')
                                        #     self._timeout += self._incTimeOut
                                        #     self._solver.set("timeout", self._timeout)
                                        #
                                        #     break  # Fill the position with number
                                        #
                                        # else:
                                        #     raise 'Timeout happened twice, don\'t know how to continue!'

                            elif self._nums[r][c] == num:
                                cols.remove(c)
        if self._print_progress:
            print("Generated a solved sudoku")
            print(self._nums)
        return self._nums, self._penalty
        # elif self._solver.check() == z3.unknown:
        #     if self._log_path:
        #         self.write_to_file(self._log_path)
        #     else:
        #          print("TimeOut and a logPath is not provided")
        #     raise 'TimeOut while loading constraints'
        # else:
        #     # @sj this error message last time was written by me =-=
        #     raise 'Error from gen_solved_sudoku function in "load_constraints"'

    def write_to_file(self, file_path: str = "logFile") -> None:
        """
        CHANGE file_path. Write self._nums to the file
        :param file_path:
        :return:
        """
        if self._print_progress:
            print(self._nums)
        with open(self.hard_smt_logPath, 'w') as f:
            s = ''.join(str(ele) for rows in self._nums for ele in rows)
            f.write(s)


    def read_from_file(self, file_path="logFile") -> str:
        """
        Read from a file with self._nums
        :param file_path:
        :return:
        """
        with open('file_path', 'r') as f:
            s = f.read()
        return s

    def write_to_smt_and_sudoku_file(self, pos, value, sat):
        """Write self._solver as a smt file to _log_path

        When reading the constraints:
        t = z3.Solver()
        t.from_file(_log_path)
        print(t, t.check())
        """
        # check directory exist
        par_dir = Path(self.hard_smt_logPath).parent
        if not os.path.exists(par_dir):
            os.makedirs(par_dir)
        time_str = time.strftime("%m_%d_%H_%M_%S") + str(time.time())
        with open(self.hard_smt_logPath+time_str, 'w') as myfile:
            print(self._solver.to_smt2(), file=myfile)

        # check directory exist
        par_dir = Path(self.hard_sudoku_logPath).parent
        if not os.path.exists(par_dir):
            os.makedirs(par_dir)
        with open(self.hard_sudoku_logPath + time_str, 'a+') as myfile:
            sudoku_lst = ''.join(str(ele) for rows in self._nums for ele in rows)
            print(f'{sudoku_lst}\t{self.condition_tpl}\t{pos}\t{value}\t{sat}\n', file=myfile)



def generate_puzzle(solved_sudokus, classic: bool, distinct: bool, per_col: bool, no_num: bool, prefill: bool,
                    log_path="",print_progress=False):
    """
    Generates puzzle with holes

    :param print_progress:
    :param log_path:
    :param solved_sudokus: MUST BE a 3D list
    :param classic:
    :param distinct:
    :return: [[time_rec], [penalty_lst]] list of lists
    """
    time_rec = []
    penalty_lst = []
    for puzzle in solved_sudokus:
        if print_progress:
            print(f'Solving puzzle: ')
            print(puzzle)
        st = time.time()
        penalty = 0
        for i in range(9):
            for j in range(9):
                s = Sudoku(puzzle.reshape(-1), classic, distinct, per_col, no_num, prefill, log_path=log_path)
                removable, temp_penalty = s.removable(i, j, puzzle[i][j])
                if removable:
                    puzzle[i][j] = 0
                penalty += temp_penalty
        et = time.time()
        time_rec.append(et - st)
        penalty_lst.append(penalty)
        print('Successfully generated one puzzle')
        # **** REMOVE
        print(puzzle)
    # **** REMOVE
    # np.save('sudoku_puzzle', solved_sudokus)
    assert len(time_rec) == len(penalty_lst), "Bug in generate_puzzle"

    return time_rec, penalty_lst


def gen_solve_sudoku(classic: bool, distinct: bool, per_col: bool, no_num: bool, prefill: bool, num_iter=1,
                     log_path="logFile"):
    '''
    First creates a solved sudoku, then generate a sudoku puzzle. returns time for each

    :param prefill:
    :param classic:
    :param distinct:
    :param per_col:
    :param no_num:
    :param num_iter:
    :return: (solve_time, solve_penalty, gen_time, gen_penalty) all are 1D lists
    '''
    ret_solve_time = []
    store_solved_sudoku = []
    solve_penalty = []
    for i in range(num_iter):
        empty_list = [0 for i in range(9) for j in range(9)]
        st = time.time()
        s = Sudoku(empty_list, classic, distinct, per_col, no_num, prefill, log_path=log_path)
        nums, penalty = s.gen_solved_sudoku()
        et = time.time()
        store_solved_sudoku.append(nums)
        ret_solve_time.append(et - st)
        solve_penalty.append(penalty)
    # np.save('solved_sudoku', store_solved_sudoku)
    store_holes = deepcopy(store_solved_sudoku)
    store_holes = np.array(store_holes)
    print("Start generating puzzles")
    ret_holes_time, holes_penalty = generate_puzzle(store_holes, classic, distinct, per_col, no_num, prefill)
    assert len(ret_solve_time) == len(solve_penalty), "error in gen_solve_sudoku"
    return ret_solve_time, solve_penalty, ret_holes_time, holes_penalty


def append_list_to_file(file_path, lst: list[int]):
    par_dir = Path(file_path).parent
    if not os.path.exists(par_dir):
        os.makedirs(par_dir)
    with open(file_path, 'a+') as f:
        f.write(str(lst) + "\n")


def gen_full_sudoku(*constraints, hard_smt_logPath='smt-logFiles/', store_sudoku_path="",hard_sudoku_logPath="") -> (float, int):
    """
    append generated full sudoku to the designated path as a string
    
    :param hard_smt_log_path:
    :param constraints: classic, distinct, percol, no_num, prefill
    :param store_sudoku_path:
    :return: (time, penalty)
    """
    empty_list = [0 for i in range(9) for j in range(9)]
    st = time.time()
    s = Sudoku(empty_list, *constraints, hard_smt_logPath=hard_smt_logPath, hard_sudoku_logPath=hard_sudoku_logPath)
    nums, penalty = s.gen_solved_sudoku()
    et = time.time()
    # Write to file
    append_list_to_file(store_sudoku_path, sum(nums, []))  # flatten 2D nums into 1D
    return et - st, penalty


def gen_holes_sudoku(solved_sudoku: list[int], *constraints, hard_smt_logPath='smt-logFiles/', store_sudoku_path="",
                     hard_sudoku_logPath="",print_progress=False):
    """
    Reads sudokus as a string from store_sudoku_path
    :param solved_sudoku: 1D list of an already solved sudoku grid
    :param hard_instances_log_path:
    :param constraints: classic, distinct, percol, no_num, prefill
    :param store_sudoku_path:
    :return: (time, penalty)
    """
    if print_progress:
        print(f'Solving puzzle: ')
        print(solved_sudoku)
    st = time.time()
    penalty = 0
    for i in range(9):
        for j in range(9):
            s = Sudoku(solved_sudoku, *constraints, hard_smt_logPath=hard_smt_logPath,
                       hard_sudoku_logPath=hard_sudoku_logPath)
            removable, temp_penalty = s.removable(i, j, solved_sudoku[i*9+j])
            if removable:
                solved_sudoku[i * 9 + j] = 0
            penalty += temp_penalty
    et = time.time()
    time_rec = et - st

    penalty = penalty
    if print_progress:
        print('Successfully generated one puzzle')
        print(solved_sudoku)
    # np.save('sudoku_puzzle', solved_sudokus)
    append_list_to_file(store_sudoku_path, solved_sudoku)
    return time_rec, penalty


if __name__ == "__main__":
    # Test classic case
    # classic, distinct, per_col, no_num
    solve_time, solve_penalty, gen_time, gen_penalty = gen_solve_sudoku(False, True, True, False, True, num_iter=100,
                                                                        log_path='DataCollection/')

    # print(gen_solve_sudoku(classic=False, distinct=True, per_col=True, no_num=False, prefill=True, num_iter=2,
    #                        log_path="DataCollection/"))

    # generate_hard_sudokus(classic=False, distinct=True, per_col=True, no_num=False,log_path="DataCollection/")

    # empty_list = [0 for i in range(9) for j in range(9)]
    # s = Sudoku(empty_list, classic=False, distinct=True, per_col=True, no_num=False, log_path="DataCollection/")
    # s.gen_solved_sudoku()

    # store_holes = np.load('solved_sudoku.npy')
    # ret_holes_time = generate_puzzle(store_holes, True, True, False, False)
    print("Process finished")
