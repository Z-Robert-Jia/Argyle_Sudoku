import os
import time
import zipfile

import Sudoku

full_iter = 3000
holes_iter = 100
# Read from file
# Override
total_time_per_condition = 5 * 60 * 10000000
curr_line_path = 'curr_line.txt'
try:
    with open(curr_line_path,'r') as f:
        curr_line = eval(f.readline())
except IOError:
    curr_line = {}  # Keep track of which full sudoku to continue_reading with

total_solve = {}


def write_file(condition_name, arr_time):
    file_path = condition_name + "-" + time.strftime("%Y_%m_%d_%H_%M_%S")
    with zipfile.ZipFile(f'../{file_path}.zip', 'w') as my_zip:
        files = os.listdir('.')
        for f in files:
            my_zip.write(f)
        # *** When we read the txt, could we still convert it back to an array?
        with my_zip.open(f"{condition_name}.txt", "w") as new_hello:
            new_hello.write(bytes(f'{arr_time}', 'utf-8'))


def to_str(bool_list):
    if len(bool_list) == 5:
        return ''.join(("classic-" if bool_list[0] else "argyle-",
                        "distinct-" if bool_list[1] else "PbEq-",
                        "percol-" if bool_list[2] else "inorder-",
                        "is_bool-" if bool_list[3] else "is_num-",
                        "prefill-" if bool_list[4] else "no_prefill-",
                        "gen_time" if bool_list[5] else "solve_time"))
    if len(bool_list) == 4:
        return ''.join(("classic-" if bool_list[0] else "argyle-",
                        "distinct-" if bool_list[1] else "PbEq-",
                        "percol-" if bool_list[2] else "inorder-",
                        "is_bool-" if bool_list[3] else "is_num-",
                        "prefill-" if bool_list[4] else "no_prefill-"))


def previous_useless_function(is_gen_full):
    for i in range(full_iter):
        for ele in conditions:
            condition = ("classic-" if ele[0] else "argyle-",
                         "distinct-" if ele[1] else "PbEq-",
                         "percol-" if ele[2] else "inorder-",
                         "is_bool-" if ele[3] else "is_num-",
                         "prefill-" if ele[4] else "no_prefill-")
            curr_line[condition] = 0
            total_solve[condition] = 0
        for cond in conditions:
            condition = to_str(cond)
            if is_gen_full:
                # TODO: Change file path
                condition_name = ''.join(condition) + 'solve_time'
            else:
                condition_name = ''.join(condition) + 'gen_time'
            print(f'Processing {condition_name}')
            print(ele)
            if condition_name not in total_solve:
                total_solve[condition_name] = 0
            if total_solve[condition_name] > total_time_per_condition:
                continue
            solve_time, solve_penalty, gen_time, gen_penalty \
                = Sudoku.gen_solve_sudoku(*ele, log_path='DataCollection/')
            total_solve[condition_name] += sum(solve_time)
            # Record time

            with open('../time-record/' + condition_name + 'solve_time.txt', 'a') as f:
                for solve_t, solve_p in zip(solve_time, solve_penalty):
                    f.write(f'{solve_t},{solve_p}\n')
            with open('../time-record/' + condition_name + 'gen_time.txt', 'a') as f:
                for gen_t, gen_p in zip(gen_time, gen_penalty):
                    f.write(f'{gen_t},{gen_p}\n')
            print(f'Appended gen and solve time for {condition_name} ')
            # print(condition_name + "-" + time.strftime("%Y_%m_%d_%H_%M_%S"))
            # write_file(condition_name, gen_solve_time)


# file_name = "test_file"
# write_to_file(file_name)
# content = read_from_file(file_name)
# print(len(content))


conditions = [[classic, distinct, percol, nonum, prefill]
              for classic in (True, False)
              for distinct in (True, False)
              for percol in (True, False)
              for nonum in (True, False) if not (distinct and nonum)
              for prefill in (True, False) if not (not percol and prefill)]
              # for gen_solve in (True, False)]
# conditions = [[True,True,False,True,False]]
classic_full_path = '../store-sudoku/classic_full_sudokus.txt'
argyle_full_path = '../store-sudoku/argyle_full_sudokus.txt'
classic_holes_path = '../store-sudoku/classic_holes_sudokus.txt'
argyle_holes_path = '../store-sudoku/argyle_holes_sudokus.txt'


for ele in conditions:
    exceed_time_limit = False
    # full_sudoku_path = '../store-sudoku/' + ''.join(condition) + 'full_sudokus.txt'
    if ele[0]:
        full_sudoku_path = classic_full_path
    else:
        full_sudoku_path = argyle_full_path

    for _ in range(full_iter):
        condition_name = to_str(ele) + 'full_time'
        print(f'Processing full sudoku {condition_name}')
        if condition_name not in total_solve:
            total_solve[condition_name] = 0
        if total_solve[condition_name] > total_time_per_condition:
            # record current position
            exceed_time_limit = True
            break
        full_time, full_penalty = Sudoku.gen_full_sudoku(*ele, hard_instances_log_path='DataCollection/',
                                                         store_sudoku_path=full_sudoku_path)
        total_solve[condition_name] += full_time
        with open('../time-record/' + condition_name + '.txt', 'a') as f: # if error, create ../time-record directory
            f.write(f'{full_time},{full_penalty}\n')
    if exceed_time_limit:
        print(f'{full_sudoku_path} {ele} exceeded time limit when generating full_grid')

for ele in conditions:
    enough_sudoku = False
    if ele[0]:
        full_sudoku_path = classic_full_path
        holes_sudoku_path = classic_holes_path
    else:
        full_sudoku_path = argyle_full_path
        holes_sudoku_path = argyle_holes_path

    with open(full_sudoku_path, 'r') as f:
        if full_sudoku_path in curr_line:
            f.seek(curr_line[full_sudoku_path])
        condition_name = to_str(ele) + 'holes_time'
        for _ in range(holes_iter):
            sudoku_lst = f.readline()[:-1] # get rid of new line character
            if condition_name not in total_solve:
                total_solve[condition_name] = 0
            if total_solve[condition_name] > total_time_per_condition:
                enough_sudoku = True
                break
            # holes_time, holes_penalty = Sudoku.gen_holes_sudoku(eval(sudoku_lst), *ele,
            # hard_instances_log_path='DataCollection/', store_sudoku_path='../store-sudoku/' + condition_name +
            # '.txt')
            holes_time, holes_penalty = Sudoku.gen_holes_sudoku(eval(sudoku_lst), *ele,
                                                                hard_instances_log_path='DataCollection/',
                                                                store_sudoku_path=holes_sudoku_path)
            total_solve[condition_name] += holes_time
            with open('../time-record/' + condition_name + '.txt', 'a+') as f_holes:
                f_holes.write(f'{holes_time},{holes_penalty}\n')

        curr_line[full_sudoku_path] = f.tell()
        f.read()
        file_size = f.tell()
        print(f'{curr_line[full_sudoku_path] / file_size * 100}% of the full grid for '
              f'{full_sudoku_path.removesuffix("full_sudokus.txt")} {ele} is used')
    print(f'{["NOT ", ""][enough_sudoku]}enough sudoku for this constraint')

with open(curr_line_path, 'w') as f:
    f.write(str(curr_line))

    # Increament both time
print("Process Finished")
