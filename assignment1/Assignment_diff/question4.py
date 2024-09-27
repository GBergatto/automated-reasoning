from z3 import *
import time

A_values = Array('A', IntSort(), IntSort()) # values of a 
B_values = Array('B', IntSort(), IntSort()) # values of b
Boolean_values = Array('bool',IntSort(),BoolSort()) # possible values of test
n = Int('n')

SAT_Solver = Solver()
SAT_Solver.add(A_values[0]==1,B_values[0]==1)
for i in range(1,11):
    SAT_Solver.add(And(
                    Implies(Boolean_values[i], And(A_values[i]==A_values[i-1]+2*B_values[i-1],B_values[i]==B_values[i-1]+3)),
                    Implies(Not(Boolean_values[i]), And(A_values[i]==A_values[i-1] + i, B_values[i]== B_values[i-1] - A_values[i]))
                ))
SAT_Solver.add(B_values[10] == 210 + n)

start_time = time.time()
for n_value in range(1,11):
    SAT_Solver.push()
    SAT_Solver.add(n==n_value)
    result = SAT_Solver.check()
    print("<---------->")
    # If satisfiable, print the model
    if result == sat:
        model = SAT_Solver.model()
        print("SAT condition found:")
        #Print values of A_values and B_values
        for i in range(11):
            print(f"A[{i}] =", model.eval(A_values[i]))
            print(f"B[{i}] =", model.eval(B_values[i]))
            if i+1 != 11:
                print(f"Boolean[{i+1}] =", model.eval(Boolean_values[i+1]))
        #Print the value of SAT of n
        print("n =", model.eval(n))
    else:
        print(f"UNSAT\nValue for n is {n_value}")
    SAT_Solver.pop()
    print("<---------->")
end_time = time.time()
print(f">>> Program runtime: {end_time-start_time} seconds.")