import Sudoku

lst = [1, 5, 9, 7, 6, 4, 2, 3, 8]
for i in range(72):
    lst.append(0)

for i in range(100):
    solver = Sudoku.Sudoku(lst, False, True, True, False, True, log_path='DataCollection/')
    solver.gen_solved_sudoku()


