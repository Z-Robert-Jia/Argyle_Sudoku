# Generates
# Variables calssic, distinct, per_col, is_num
# per_col only required when generating
conditions = [[b1,b2,b3,b4] for b1 in (True,False) for b2 in (True,False) for b3 in (True,False) for b4 in (True,False)]
for ele in conditions:
    condition = ("classic-" if ele[0] else "argyle-",
                  "distinct-" if ele[0] else "PbEq-",
                  "percol-" if ele[0] else "inorder-",
                  "is_num" if ele[0] else "is_bool")
    calssic, distinct, per_col, is_num = condition
    print(condition)

sub_path = ''.join(condition)
print(sub_path)

import os
import numpy as np
import zipfile
import time

a = np.zeros(10)
print(a)
# np.save('interesting',a)
print(os.getcwd())
# Get parent dir
# os.chdir(os.path.dirname(os.getcwd()))
# file_path to store data for this experiment
file_path = "ex" + time.strftime("%Y_%m_%d_%H_%M_%S")
os.mkdir(file_path)
print(os.getcwd())

with zipfile.ZipFile('data_collection.zip', 'w') as my_zip:
    files = os.listdir(file_path)
    for f in files:
        my_zip.write(file_path + os.sep() + f)
    # my_zip.write('main.py')

