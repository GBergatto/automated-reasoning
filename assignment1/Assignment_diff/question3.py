from z3 import *

SAT_solver = Solver()

rounds_sim = 59

def print_sat(model,rounds_sim):
    print(f"The locations the truck has been to: {[model.eval(Truck_Location[i]) for i in range(rounds_sim+1)]}")
    print(f"How much food ration has been dropped at each: {[model.eval(Truck_fdrop[i]) for i in range(rounds_sim+1)]}")
    print(f"How much food ration was left at each dropoff: {[model.eval(Truck_fsup[i]) for i in range(rounds_sim+1)]}")
    print(f"A village food supply {[model.eval(A_fsup[i]) for i in range(rounds_sim+1)]}")
    print(f"B village food supply {[model.eval(B_fsup[i]) for i in range(rounds_sim+1)]}")
    print(f"C village food supply {[model.eval(C_fsup[i]) for i in range(rounds_sim+1)]}")
    print(f"S village food supply {[model.eval(S_fsup[i]) for i in range(rounds_sim+1)]}")
    
#Define the amount of food supply for each village
A_fsup = Array("A_fsup",IntSort(),IntSort())
B_fsup = Array("B_fsup",IntSort(),IntSort())
C_fsup = Array("C_fsup",IntSort(),IntSort())
S_fsup = Array("S_fsup",IntSort(),IntSort())

#Define the capacity of food supply for each non-self-supporting village
A_cap = 90
B_cap = 120
C_cap = 90
#Define truck food supply,capacity,and current location
Truck_fsup, Truck_cap, Truck_Location, Truck_fdrop = Array("Truck_fsup",IntSort(),IntSort()), 150, Array("Truck_Location",IntSort(),StringSort()), Array("Truck_food_drop",IntSort(),IntSort())
#Define Road
Road_time = Array("Road_time",IntSort(),IntSort())

#Initial conditions
SAT_solver.add(
    A_fsup[0] == 60, B_fsup[0] == 60, C_fsup[0] == 60, S_fsup[0] == 60, #Food Supply Initial Conditions
    Truck_Location[0] == StringVal("S"), Truck_fsup[0] == Truck_cap, Truck_fdrop[0] == 0  #Truck Initial Status
)

#Round Start
for round_rank in range(1,rounds_sim+1):
    #For each round simulate system
    next_loc, curr_loc = Truck_Location[round_rank], Truck_Location[round_rank-1]
    SAT_solver.add(
        Or(next_loc == StringVal("S"),
           next_loc == StringVal("A"),
           next_loc == StringVal("B"),
           next_loc == StringVal("C")
        ), #Possible Truck Destinations
        next_loc != curr_loc, #Location cannot be current location
        Truck_fsup[round_rank] >= 0, #Truck cannot have negative amount food supply,
        Truck_fdrop[round_rank] >= 0, # Cannot drop off negative amount of food
        Truck_fdrop[round_rank] <= Truck_fsup[round_rank-1], #Truck cannot dropoff more food than its reserve
        #Which road can be taken
        If(And(curr_loc == "S", next_loc == "A"),Road_time[round_rank] == 15,
           If(And(curr_loc == "S", next_loc == "C"),Road_time[round_rank] == 15,
              If(And(curr_loc == "A", next_loc == "S"),Road_time[round_rank] == 15,
                 If(And(curr_loc == "A", next_loc == "C"),Road_time[round_rank] == 12,
                    If(And(curr_loc == "A", next_loc == "B"),Road_time[round_rank] == 17,
                       If(And(curr_loc == "B", next_loc == "A"),Road_time[round_rank] == 17,
                          If(And(curr_loc == "B", next_loc == "C"),Road_time[round_rank] == 13,
                             If(And(curr_loc == "C", next_loc == "S"),Road_time[round_rank] == 15,
                                If(And(curr_loc == "C", next_loc == "A"),Road_time[round_rank] == 12,
                                   If(And(curr_loc == "C", next_loc == "B"),Road_time[round_rank] == 9, 
                                      False)))))))))),
        #Village food supply cannot go below 0
        A_fsup[round_rank-1] - Road_time[round_rank] > 0, B_fsup[round_rank-1] - Road_time[round_rank] > 0,
        C_fsup[round_rank-1] - Road_time[round_rank] > 0, S_fsup[round_rank-1] - Road_time[round_rank] > 0,
        #Simulate for each village
        #For A
        If(A_fsup[round_rank-1] - Road_time[round_rank] + If(next_loc=="A",Truck_fdrop[round_rank],0) <= A_cap,
           A_fsup[round_rank] == A_fsup[round_rank-1] - Road_time[round_rank] + If(next_loc=="A",Truck_fdrop[round_rank],0),
           And(A_fsup[round_rank] == A_cap, Truck_fdrop[round_rank] == A_cap - A_fsup[round_rank-1])),
        #For B
        If(B_fsup[round_rank-1] - Road_time[round_rank] + If(next_loc=="B",Truck_fdrop[round_rank],0) <= B_cap,
           B_fsup[round_rank] == B_fsup[round_rank-1] - Road_time[round_rank] + If(next_loc=="B",Truck_fdrop[round_rank],0),
           And(B_fsup[round_rank] == B_cap, Truck_fdrop[round_rank] == B_cap - B_fsup[round_rank-1])),
        #For C
        If(C_fsup[round_rank-1] - Road_time[round_rank] + If(next_loc=="C",Truck_fdrop[round_rank],0) <= C_cap,
           C_fsup[round_rank] == C_fsup[round_rank-1] - Road_time[round_rank] + If(next_loc=="C",Truck_fdrop[round_rank],0),
           And(C_fsup[round_rank] == C_cap, Truck_fdrop[round_rank] == C_cap - C_fsup[round_rank-1])),
        #For S
        #S_fsup[round_rank] == S_fsup[round_rank-1] - Road_time[round_rank] + If(next_loc=="S",Truck_fdrop[round_rank],0),
        If(next_loc=="S",Truck_fsup[round_rank] == Truck_cap,Truck_fsup[round_rank] == Truck_fsup[round_rank-1] - Truck_fdrop[round_rank]) #Refill Truck Supply
    )

if SAT_solver.check() == sat:
    sat_model = SAT_solver.model()
    print_sat(sat_model,rounds_sim)
else:
    print("UNSAT")