# Temporary file to verify the output of the program
# import display as display
import numpy as np


def to_output(lst):
    print(np.reshape(lst,-1))

def join_grid(str):
    lst = [int(ele) for ele in str if ele.isnumeric()]
    print(lst)
    return lst


# sudoku_puzzle = np.load('sudoku_puzzle.npy')
# to_output(solved_sudokus)
# to_output(sudoku_puzzle)
# First
def display_results(load = 'True'):
    if load:
        sudoku_puzzle = np.load('sudoku_puzzle.npy')
        solved_sudokus = np.load('solved_sudoku.npy')
        print('Solved Sudoku1: ')
        to_output(solved_sudokus[0])
        print('Sudoku Puzzle1:')
        to_output(sudoku_puzzle[0])
        # Second
        print('Solved Sudoku2: ')
        to_output(solved_sudokus[1])
        print('Sudoku Puzzle2:')
        to_output(sudoku_puzzle[1])
        print(solved_sudokus[0] == solved_sudokus[1])

    else:
        sudoku = join_grid(
'''[9 1 5 6 7 2 4 8 3]
 [7 6 2 3 8 4 5 9 1]
 [8 3 4 5 9 1 2 6 7]
 [4 5 9 8 3 6 7 1 2]
 [1 8 7 4 2 9 3 5 6]
 [3 2 6 1 5 7 8 4 9]
 [6 9 3 2 4 8 1 7 5]
 [2 7 8 9 1 5 6 3 4]
 [5 4 1 7 6 3 9 2 8]''')
        print('Sudoku: ')
        to_output(sudoku)

display_results(True)