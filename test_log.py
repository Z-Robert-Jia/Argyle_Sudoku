
import z3
x = z3.Int('x')
s = z3.Solver()
#z3.open_log('Solver_interation')
# z3.open_log('test')
s.add(x>3)
s.add(x<6)
s.check()
with open('myfile', 'w') as myfile:
    print(s.to_smt2(), file=myfile)

t = z3.Solver()
t.from_file('myfile')
print(t, t.check())

# s.from_file(z3.String('Solver_interaction'))

# z3.Solver.from_file(s,'\Solver_interation')

# print(s)
# z3.solver_to_string()