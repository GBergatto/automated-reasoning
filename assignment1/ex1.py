import z3

# Trucks
num_trucks = 6
max_weight = 8000
max_pallets = 10

# Pallets
nuzzles_weight = 800
nuzzles_total = 6

prittles_weight = 405
prittles_total = 12

skipples_weight = 500
skipples_total = 15

crottles_weight = 2500
crottles_total = 8

dupples_weight = 600

# Solver
solver = z3.Optimize()

### Variables ###
nuzzles = [z3.Int(f'nuzzles_t{i}') for i in range(num_trucks)]
prittles = [z3.Int(f'prittles_t{i}') for i in range(num_trucks)]
skipples = [z3.Int(f'skipples_t{i}') for i in range(num_trucks)]
crottles = [z3.Int(f'crottles_t{i}') for i in range(num_trucks)]
dupples = [z3.Int(f'dupples_t{i}') for i in range(num_trucks)]

### Constraints ###
# all trucks must contain a non-negative number of pallets
for i in range(num_trucks):
    solver.add(nuzzles[i] >= 0, prittles[i] >= 0, skipples[i] >= 0, crottles[i] >= 0, dupples[i] >= 0)

# total pallets of each type must match the required number
solver.add(z3.Sum(nuzzles) == nuzzles_total)
solver.add(z3.Sum(prittles) == prittles_total)
solver.add(z3.Sum(skipples) == skipples_total)
solver.add(z3.Sum(crottles) == crottles_total)

# only two trucks can carry skipples
solver.add(z3.Sum([z3.If(skipples[i] > 0, 1, 0) for i in range(num_trucks)]) == 2)

# prittles must be distributed over at least 5 trucks
solver.add(z3.Sum([z3.If(prittles[i] > 0, 1, 0) for i in range(num_trucks)]) >= 5)

# part 2
# C get has to be with >= 2 D
# if part == 2:
for i in range(num_trucks):
    solver.add(z3.If(crottles[i] > 0, dupples[i]>=2, True))

# max 10 pallets per truck
for i in range(num_trucks):
    total_weight = z3.Sum(
        nuzzles[i] * nuzzles_weight,
        prittles[i] * prittles_weight,
        skipples[i] * skipples_weight,
        crottles[i] * crottles_weight,
        dupples[i] * dupples_weight
    )
    num_pallets = nuzzles[i] + prittles[i] + skipples[i] + crottles[i] + dupples[i]

    solver.add(total_weight <= max_weight)
    solver.add(num_pallets <= max_pallets)

### Solution
objective = z3.Sum(dupples)
solver.maximize(objective)

# Check for satisfiability
if solver.check() == z3.sat:
    model = solver.model()
    print(model.evaluate(objective))
    
    # Output the results
    for i in range(num_trucks):
        nuzzles_count = model.eval(nuzzles[i]).as_long()
        prittles_count = model.eval(prittles[i]).as_long()
        skipples_count = model.eval(skipples[i]).as_long()
        crottles_count = model.eval(crottles[i]).as_long()
        dupples_count = model.eval(dupples[i]).as_long()
        
        # Compute the total weight for truck i
        tw = (
            nuzzles_count * nuzzles_weight +
            prittles_count * prittles_weight +
            skipples_count * skipples_weight +
            crottles_count * crottles_weight +
            dupples_count * dupples_weight
        )
        
        print(f"Truck {i+1}:")
        print(f"  Nuzzles: {model[nuzzles[i]]}")
        print(f"  Prittles: {model[prittles[i]]}")
        print(f"  Skipples: {model[skipples[i]]}")
        print(f"  Crottles: {model[crottles[i]]}")
        print(f"  Dupples: {model[dupples[i]]}")
        print(f"Total weight: {tw} kg")
else:
    print("No solution found.")

