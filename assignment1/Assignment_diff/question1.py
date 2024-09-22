from z3 import *
#Print Result of Solver
def print_sat(model,Trucks):
    print("SAT condition found:")
    #Print values of A_values and B_values
    print("           n p s c d")
    for i in range(0,6):
        print(f"Truck[{i+1}]: ",end=' ')
        for j in range(0,5):
            print(model.eval(Trucks[i][j]), end=' ')
        print(f"Truck {i+1} Amount of paletes: {model.eval(Trucks[i][0]+Trucks[i][1]+Trucks[i][2]+Trucks[i][3]+Trucks[i][4])} - Amount of weight: {model.eval(800*Trucks[i][0]+405*Trucks[i][1]+500*Trucks[i][2]+2500*Trucks[i][3]+600*Trucks[i][4])}")

#Create the solver
SAT_Solver = Optimize()

#Trucks matrix defined
Trucks = list([])
for i in range(0,6):
    Trucks.append(Array(f"Truck{i+1}",IntSort(),IntSort())) #Indices mapped to trucks
    for j in range(0,5):
        SAT_Solver.add(
            Trucks[i][j] >= 0
        )

# Amount of pallets per building block constraint, index mapping:
# 0->NUZZLES 1->PRITTLES 2->SKIPPLES 3->CROTTLES 4->DUPPLES
pallet_weight = [800,405,500,2500,600]
pallet_amount = [6, 12, 15, 8]

#Define constraints
for col_idx in range(0,4):
    SAT_Solver.add(
        Trucks[0][col_idx]+Trucks[1][col_idx]+Trucks[2][col_idx]+Trucks[3][col_idx]+Trucks[4][col_idx]+Trucks[5][col_idx] == pallet_amount[col_idx]
    )
# Per truck pallet amount, pallet weight constraint
skp_trck_distribute, prt_trck_distribute = [], []
for row_idx in range(0,6):
    SAT_Solver.add(
        Trucks[row_idx][0]+Trucks[row_idx][1]+Trucks[row_idx][2]+Trucks[row_idx][3]+Trucks[row_idx][4] <= 10, #Per truck pallet amount
        pallet_weight[0]*Trucks[row_idx][0]+pallet_weight[1]*Trucks[row_idx][1]+pallet_weight[2]*Trucks[row_idx][2]+pallet_weight[3]*Trucks[row_idx][3]+pallet_weight[4]*Trucks[row_idx][4] <= 8000 #Per truck weight
    )
    prt_trck_distribute.append(Trucks[row_idx][1] != 0) #True for trucks containing prittles
    skp_trck_distribute.append(Trucks[row_idx][2] != 0) #True for trucks containing skipples

SAT_Solver.add( # Prittle and Skipple constraints
    And(
        Sum([If(cond, 1, 0) for cond in prt_trck_distribute]) >= 5,
        Sum([If(cond, 1, 0) for cond in skp_trck_distribute]) <= 2
    )
)

#Solution 1.1
print("<--Answer Question 1.1-->")
max_dupple_objective_1_1 = Sum(Trucks[0][4],Trucks[1][4],Trucks[2][4],Trucks[3][4],Trucks[4][4],Trucks[5][4])
SAT_Solver.maximize(max_dupple_objective_1_1)
if SAT_Solver.check() == sat:
    max_dupple_model1_1 = SAT_Solver.model() #The model with the maximum amount of dupple pallets for question 1.1
    print_sat(max_dupple_model1_1,Trucks)
    print(f"The maximum number of pallets of dupples that can be delivered is {max_dupple_model1_1.eval(max_dupple_objective_1_1)}")
else:
    print("UNSAT")
print("<--Answer Question 1.1-->")
#Solution 1.2

# Crottle Constraint
crt_trck_dist = []
for row_idx in range(0,6):
    crt_trck_dist.append(If(Trucks[row_idx][3]!= 0,Trucks[row_idx][4] >= 2,True))
SAT_Solver.add(
    And(crt_trck_dist)
)
print("<--Answer Question 1.2-->")
if SAT_Solver.check() == sat:
    max_dupple_model1_2 = SAT_Solver.model() #The model with the maximum amount of dupple pallets for question 1.1
    print_sat(max_dupple_model1_2,Trucks)
    print(f"The maximum number of pallets of dupples that can be delivered is {max_dupple_model1_2.eval(max_dupple_objective_1_1)}")
else:
    print("UNSAT")
print("<--Answer Question 1.2-->")