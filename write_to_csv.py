import csv

import numpy as np


def write(file_name):
    with open(file_name, 'a') as f:
        f.writelines("123\n")

        # spamwriter = csv.writer(csvfile, delimiter=' ',
        #                         quotechar='|', quoting=csv.QUOTE_MINIMAL)
        # spamwriter.writerow("0.12312314121")
        # csvfile.write("0.1231")
        # spamwriter.writerow(['Spam', 'Lovely Spam', 'Wonderful Spam'])


write("store_time.txt")
# a = np.loadtxt("store_time.txt")
# print(a)