import os
import time
import zipfile

import Sudoku

num_iter = 20
total_time_per_condition = 5*60

def write_file(condition_name, arr_time):
    file_path = condition_name + "-" + time.strftime("%Y_%m_%d_%H_%M_%S")
    with zipfile.ZipFile(f'../{file_path}.zip', 'w') as my_zip:
        files = os.listdir('.')
        for f in files:
            my_zip.write(f)
        # *** When we read the txt, could we still convert it back to an array?
        with my_zip.open(f"{condition_name}.txt", "w") as new_hello:
            new_hello.write(bytes(f'{arr_time}', 'utf-8'))


# file_name = "test_file"
# write_to_file(file_name)
# content = read_from_file(file_name)
# print(len(content))

# TODO: Remember to change
# conditions = [[False, b2, b3, b4, b5]for b2 in (True, False)
#               for b3 in (True, False)
#               for b4 in (True, False) if not (b2 and b4)
#               for b5 in (True, False) if b3]
conditions = [[b1, b2, b3, b4, b5] for b1 in (True, False)
              for b2 in (True, False)
              for b3 in (True, False)
              for b4 in (True, False) if not (b2 and b4)
              for b5 in (True, False) if b3]


# I assigned this to time, and then got errors in the line above
total_solve = {}
for i in range(num_iter):
    for ele in conditions:
        condition = ("classic-" if ele[0] else "argyle-",
                     "distinct-" if ele[1] else "PbEq-",
                     "percol-" if ele[2] else "inorder-",
                     "is_bool-" if ele[3] else "is_num-",
                     "prefill-" if ele[4] else "no_prefill-")
        condition_name = ''.join(condition)
        print(f'Processing {condition_name}')
        print(ele)
        if condition_name not in total_solve:
            total_solve[condition_name] = 0
        if total_solve[condition_name] > total_time_per_condition:
            break
        solve_time, solve_penalty, gen_time, gen_penalty \
            = Sudoku.gen_solve_sudoku(*ele, log_path='DataCollection/')
        total_solve[condition_name] += sum(solve_time)
        # Record time
        with open('../time-record/' + condition_name + 'solve_time.txt', 'a') as f:
            for solve_t,solve_p in zip(solve_time,solve_penalty):
                f.write(f'{solve_t},{solve_p}\n')
        with open('../time-record/' + condition_name + 'gen_time.txt', 'a') as f:
            for gen_t,gen_p in zip(gen_time,gen_penalty):
                f.write(f'{gen_t},{gen_p}\n')
        print(f'Appended gen and solve time for {condition_name} ')
        # print(condition_name + "-" + time.strftime("%Y_%m_%d_%H_%M_%S"))
        # write_file(condition_name, gen_solve_time)
        # Very interesting this line is necessary
        # time.sleep(1)

print("Process Finished") 