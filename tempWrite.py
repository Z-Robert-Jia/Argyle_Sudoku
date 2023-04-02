import main2

_nums = [[0 for _ in range(9)] for _ in range(9)]


def write_to_file(file_path: str = "logFile") -> None:
    """
    CHANGE file_path
    :param file_path:
    :return:
    """
    with open("file_path", 'w') as f:
        s = ''.join(str(ele) for rows in _nums for ele in rows)
        f.write(s)


def read_from_file(file_path="logFile") -> str:
    with open('file_path', 'r') as f:
        s = f.read()
    return s


# file_name = "test_file"
# write_to_file(file_name)
# content = read_from_file(file_name)
#
# print(len(content))

conditions = [[b1, b2, b3, b4, b3] for b1 in (True, False)
              for b2 in (True, False)
              for b3 in (True, False)
              for b4 in (True, False) if not (b2 and b4)]

for ele in conditions:
    condition = ("classic-" if ele[0] else "argyle-",
                 "distinct-" if ele[1] else "PbEq-",
                 "percol-" if ele[2] else "inorder-",
                 "is_bool" if ele[3] else "is_num",
                 "prefill" if ele[4] else "no_prefill")
    condition_name = ''.join(condition)
    # I assigned this to time, and then got errors in the line above
    # TODO: REMEBER TO CHANGE THE FUNCTION
    gen_solve_time = main2.fake_gen_solve_sudoku(*ele, num_iter=2)
    solve_time, gen_time = gen_solve_time
    with open('../time-record/'+condition_name+'solve_time.txt', 'a') as f:
        f.write(str(solve_time)+'\n')
    with open('../time-record/'+condition_name+'gen_time.txt', 'a') as f:
        f.write(str(gen_time)+'\n')
    print(f'Appended gen and solve time for {condition_name} ')
    # print(condition_name + "-" + time.strftime("%Y_%m_%d_%H_%M_%S"))
    # write_file(condition_name, gen_solve_time)
    # Very interesting this line is necessary
    # time.sleep(1)