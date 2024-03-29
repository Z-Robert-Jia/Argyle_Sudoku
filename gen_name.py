# Finial output script

import main2
import os
import numpy as np
import zipfile
import time


def write_file(condition_name, arr_time):
    file_path = condition_name + "-" + time.strftime("%Y_%m_%d_%H_%M_%S")
    with zipfile.ZipFile(f'../{file_path}.zip', 'w') as my_zip:
        files = os.listdir('.')
        for f in files:
            my_zip.write(f)
        # *** When we read the txt, could we still convert it back to an array?
        with my_zip.open(f"{condition_name}.txt", "w") as new_hello:
            new_hello.write(bytes(f'{arr_time}', 'utf-8'))


# # Variables calssic, distinct, per_col, is_num, prefill
conditions = [[b1, b2, b3, b4, b3] for b1 in (True, False)
              for b2 in (True, False)
              for b3 in (True, False)
              for b4 in (True, False) if not (b2 and b4)]

for ele in conditions:
    condition = ("classic-" if ele[0] else "argyle-",
                 "distinct-" if ele[0] else "PbEq-",
                 "percol-" if ele[0] else "inorder-",
                 "is_bool" if ele[0] else "is_num")
    condition_name = ''.join(condition)
    # I assigned this to time, and then got errors in the line above
    # TODO: REMEBER TO CHANGE THE FUNCTION
    gen_solve_time = main2.fake_gen_solve_sudoku(*ele, num_iter=2)
    print(condition_name + "-" + time.strftime("%Y_%m_%d_%H_%M_%S"))
    write_file(condition_name, gen_solve_time)
    # Very interesting this line is necessary
    time.sleep(1)

# os.chdir(os.path.dirname(os.getcwd()))
# file_path to store data for this experiment
# os.mkdir(file_path)
# print(os.getcwd())
# print(file_path)
# np.save(file_path+'/temp',a)

#     f.write(a)
# np.save(file_path+os.sep, a)


# my_zip.write('main.py')

# from itertools import product
# tpl = (True, False)
# conditions = [(b1,b2,b3,b4) for (b1,b2,b3,b4) in product(tpl, tpl, tpl, tpl)
#                if True]
